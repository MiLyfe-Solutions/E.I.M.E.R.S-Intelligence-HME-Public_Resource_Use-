import V185TrunkScan23Chunk0099

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_592445 : List Nat := [1, 4, 1, 3, 2, 1, 1, 3, 1, 2, 4]
def baseStart_592445 : Nat := 118140960795 + 592445 * 2 ^ 59
def prefixEnd_592445 : Nat := 4983230072969 + 3 ^ 40 * 592445 * 2
def baseEnd_592445 : Nat := 304209046353039789912901

theorem tailTrace_592445 : CollatzResearch.WordTrace tailWord_592445 prefixEnd_592445 304209046353039789912901 := by
  unfold tailWord_592445
  simp only [CollatzResearch.WordTrace]
  refine ⟨21608244338680421395634789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14405496225786947597089859 21608244338680421395634789)
  ·
    refine ⟨4051545813502579011681523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21608244338680421395634789 4051545813502579011681523)
    ·
      refine ⟨6077318720253868517522285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4051545813502579011681523 6077318720253868517522285)
      ·
        refine ⟨2278994520095200694070857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6077318720253868517522285 2278994520095200694070857)
        ·
          refine ⟨1709245890071400520553143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2278994520095200694070857 1709245890071400520553143)
          ·
            refine ⟨2563868835107100780829715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1709245890071400520553143 2563868835107100780829715)
            ·
              refine ⟨3845803252660651171244573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2563868835107100780829715 3845803252660651171244573)
              ·
                refine ⟨1442176219747744189216715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3845803252660651171244573 1442176219747744189216715)
                ·
                  refine ⟨2163264329621616283825073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1442176219747744189216715 2163264329621616283825073)
                  ·
                    refine ⟨1622448247216212212868805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2163264329621616283825073 1622448247216212212868805)
                    ·
                      refine ⟨304209046353039789912901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1622448247216212212868805 304209046353039789912901)
                      ·
                        rfl

theorem cell23_592445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_592445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592445 prefixEnd_592445 := by exact prefixLift 592445
  have htrace : WordTrace (prefixWord ++ tailWord_592445) baseStart_592445 baseEnd_592445 := by
    simpa [prefixWord, tailWord_592445, baseEnd_592445] using wordTrace_append hprefix tailTrace_592445
  have hstable : (prefixWord ++ tailWord_592445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592445).length < 2 ^ (prefixWord ++ tailWord_592445).sum := by decide
  have hdescent : baseEnd_592445 < baseStart_592445 := by decide
  rcases family_descends (prefixWord ++ tailWord_592445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592449 : List Nat := [1, 2, 5, 1, 1, 3, 1, 2, 3, 2, 2]
def baseStart_592449 : Nat := 118140960795 + 592449 * 2 ^ 59
def prefixEnd_592449 : Nat := 4983230072969 + 3 ^ 40 * 592449 * 2
def baseEnd_592449 : Nat := 304211100275657774262883

theorem tailTrace_592449 : CollatzResearch.WordTrace tailWord_592449 prefixEnd_592449 304211100275657774262883 := by
  unfold tailWord_592449
  simp only [CollatzResearch.WordTrace]
  refine ⟨21608390230665930078780401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14405593487110620052520267 21608390230665930078780401)
  ·
    refine ⟨16206292672999447559085301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21608390230665930078780401 16206292672999447559085301)
    ·
      refine ⟨1519339938093698208664247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16206292672999447559085301 1519339938093698208664247)
      ·
        refine ⟨2279009907140547312996371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1519339938093698208664247 2279009907140547312996371)
        ·
          refine ⟨3418514860710820969494557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2279009907140547312996371 3418514860710820969494557)
          ·
            refine ⟨1281943072766557863560459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3418514860710820969494557 1281943072766557863560459)
            ·
              refine ⟨1922914609149836795340689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1281943072766557863560459 1922914609149836795340689)
              ·
                refine ⟨1442185956862377596505517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1922914609149836795340689 1442185956862377596505517)
                ·
                  refine ⟨540819733823391598689569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1442185956862377596505517 540819733823391598689569)
                  ·
                    refine ⟨405614800367543699017177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 540819733823391598689569 405614800367543699017177)
                    ·
                      refine ⟨304211100275657774262883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 405614800367543699017177 304211100275657774262883)
                      ·
                        rfl

theorem cell23_592449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_592449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592449 prefixEnd_592449 := by exact prefixLift 592449
  have htrace : WordTrace (prefixWord ++ tailWord_592449) baseStart_592449 baseEnd_592449 := by
    simpa [prefixWord, tailWord_592449, baseEnd_592449] using wordTrace_append hprefix tailTrace_592449
  have hstable : (prefixWord ++ tailWord_592449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592449).length < 2 ^ (prefixWord ++ tailWord_592449).sum := by decide
  have hdescent : baseEnd_592449 < baseStart_592449 := by decide
  rcases family_descends (prefixWord ++ tailWord_592449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592455 : List Nat := [1, 1, 4, 1, 4, 2, 3, 7]
def baseStart_592455 : Nat := 118140960795 + 592455 * 2 ^ 59
def prefixEnd_592455 : Nat := 4983230072969 + 3 ^ 40 * 592455 * 2
def baseEnd_592455 : Nat := 11267191894799435214365

theorem tailTrace_592455 : CollatzResearch.WordTrace tailWord_592455 prefixEnd_592455 11267191894799435214365 := by
  unfold tailWord_592455
  simp only [CollatzResearch.WordTrace]
  refine ⟨21608609068644193103498819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14405739379096128735665879 21608609068644193103498819)
  ·
    refine ⟨32412913602966289655248229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21608609068644193103498819 32412913602966289655248229)
    ·
      refine ⟨6077421300556179310359043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32412913602966289655248229 6077421300556179310359043)
      ·
        refine ⟨9116131950834268965538565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6077421300556179310359043 9116131950834268965538565)
        ·
          refine ⟨1709274740781425431038481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9116131950834268965538565 1709274740781425431038481)
          ·
            refine ⟨1281956055586069073278861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1709274740781425431038481 1281956055586069073278861)
            ·
              refine ⟨480733520844775902479573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1281956055586069073278861 480733520844775902479573)
              ·
                refine ⟨11267191894799435214365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 480733520844775902479573 11267191894799435214365)
                ·
                  rfl

theorem cell23_592455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 7].length) (baseStart_592455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592455 prefixEnd_592455 := by exact prefixLift 592455
  have htrace : WordTrace (prefixWord ++ tailWord_592455) baseStart_592455 baseEnd_592455 := by
    simpa [prefixWord, tailWord_592455, baseEnd_592455] using wordTrace_append hprefix tailTrace_592455
  have hstable : (prefixWord ++ tailWord_592455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592455).length < 2 ^ (prefixWord ++ tailWord_592455).sum := by decide
  have hdescent : baseEnd_592455 < baseStart_592455 := by decide
  rcases family_descends (prefixWord ++ tailWord_592455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592465 : List Nat := [1, 2, 2, 1, 3, 3, 2, 2, 1, 3, 3]
def baseStart_592465 : Nat := 118140960795 + 592465 * 2 ^ 59
def prefixEnd_592465 : Nat := 4983230072969 + 3 ^ 40 * 592465 * 2
def baseEnd_592465 : Nat := 304219315966129711662809

theorem tailTrace_592465 : CollatzResearch.WordTrace tailWord_592465 prefixEnd_592465 304219315966129711662809 := by
  unfold tailWord_592465
  simp only [CollatzResearch.WordTrace]
  refine ⟨21608973798607964811362849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14405982532405309874241899 21608973798607964811362849)
  ·
    refine ⟨16206730348955973608522137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21608973798607964811362849 16206730348955973608522137)
    ·
      refine ⟨12155047761716980206391603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16206730348955973608522137 12155047761716980206391603)
      ·
        refine ⟨18232571642575470309587405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12155047761716980206391603 18232571642575470309587405)
        ·
          refine ⟨6837214365965801366095277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18232571642575470309587405 6837214365965801366095277)
          ·
            refine ⟨2563955387237175512285729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6837214365965801366095277 2563955387237175512285729)
            ·
              refine ⟨1922966540427881634214297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2563955387237175512285729 1922966540427881634214297)
              ·
                refine ⟨1442224905320911225660723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1922966540427881634214297 1442224905320911225660723)
                ·
                  refine ⟨2163337357981366838491085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1442224905320911225660723 2163337357981366838491085)
                  ·
                    refine ⟨811251509243012564434157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2163337357981366838491085 811251509243012564434157)
                    ·
                      refine ⟨304219315966129711662809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 811251509243012564434157 304219315966129711662809)
                      ·
                        rfl

theorem cell23_592465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 3, 3].length) (baseStart_592465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592465 prefixEnd_592465 := by exact prefixLift 592465
  have htrace : WordTrace (prefixWord ++ tailWord_592465) baseStart_592465 baseEnd_592465 := by
    simpa [prefixWord, tailWord_592465, baseEnd_592465] using wordTrace_append hprefix tailTrace_592465
  have hstable : (prefixWord ++ tailWord_592465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592465).length < 2 ^ (prefixWord ++ tailWord_592465).sum := by decide
  have hdescent : baseEnd_592465 < baseStart_592465 := by decide
  rcases family_descends (prefixWord ++ tailWord_592465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592466 : List Nat := [3, 2, 2, 1, 2, 1, 4, 3, 1, 2, 2]
def baseStart_592466 : Nat := 118140960795 + 592466 * 2 ^ 59
def prefixEnd_592466 : Nat := 4983230072969 + 3 ^ 40 * 592466 * 2
def baseEnd_592466 : Nat := 304219829446784207750305

theorem tailTrace_592466 : CollatzResearch.WordTrace tailWord_592466 prefixEnd_592466 304219829446784207750305 := by
  unfold tailWord_592466
  simp only [CollatzResearch.WordTrace]
  refine ⟨5402252567901085495537313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14406006847736227988099501 5402252567901085495537313)
  ·
    refine ⟨4051689425925814121652985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5402252567901085495537313 4051689425925814121652985)
    ·
      refine ⟨3038767069444360591239739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4051689425925814121652985 3038767069444360591239739)
      ·
        refine ⟨4558150604166540886859609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3038767069444360591239739 4558150604166540886859609)
        ·
          refine ⟨3418612953124905665144707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4558150604166540886859609 3418612953124905665144707)
          ·
            refine ⟨5127919429687358497717061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3418612953124905665144707 5127919429687358497717061)
            ·
              refine ⟨961484893066379718321949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5127919429687358497717061 961484893066379718321949)
              ·
                refine ⟨360556834899892394370731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 961484893066379718321949 360556834899892394370731)
                ·
                  refine ⟨540835252349838591556097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 360556834899892394370731 540835252349838591556097)
                  ·
                    refine ⟨405626439262378943667073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 540835252349838591556097 405626439262378943667073)
                    ·
                      refine ⟨304219829446784207750305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 405626439262378943667073 304219829446784207750305)
                      ·
                        rfl

theorem cell23_592466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_592466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592466 prefixEnd_592466 := by exact prefixLift 592466
  have htrace : WordTrace (prefixWord ++ tailWord_592466) baseStart_592466 baseEnd_592466 := by
    simpa [prefixWord, tailWord_592466, baseEnd_592466] using wordTrace_append hprefix tailTrace_592466
  have hstable : (prefixWord ++ tailWord_592466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592466).length < 2 ^ (prefixWord ++ tailWord_592466).sum := by decide
  have hdescent : baseEnd_592466 < baseStart_592466 := by decide
  rcases family_descends (prefixWord ++ tailWord_592466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592476 : List Nat := [2, 2, 4, 1, 4, 1, 1, 2, 2, 4]
def baseStart_592476 : Nat := 118140960795 + 592476 * 2 ^ 59
def prefixEnd_592476 : Nat := 4983230072969 + 3 ^ 40 * 592476 * 2
def baseEnd_592476 : Nat := 101408321417776389541753

theorem tailTrace_592476 : CollatzResearch.WordTrace tailWord_592476 prefixEnd_592476 101408321417776389541753 := by
  unfold tailWord_592476
  simp only [CollatzResearch.WordTrace]
  refine ⟨10804687500784056845006641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14406250001045409126675521 10804687500784056845006641)
  ·
    refine ⟨8103515625588042633754981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10804687500784056845006641 8103515625588042633754981)
    ·
      refine ⟨1519409179797757993829059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8103515625588042633754981 1519409179797757993829059)
      ·
        refine ⟨2279113769696636990743589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1519409179797757993829059 2279113769696636990743589)
        ·
          refine ⟨427333831818119435764423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2279113769696636990743589 427333831818119435764423)
          ·
            refine ⟨641000747727179153646635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427333831818119435764423 641000747727179153646635)
            ·
              refine ⟨961501121590768730469953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 641000747727179153646635 961501121590768730469953)
              ·
                refine ⟨721125841193076547852465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 961501121590768730469953 721125841193076547852465)
                ·
                  refine ⟨540844380894807410889349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 721125841193076547852465 540844380894807410889349)
                  ·
                    refine ⟨101408321417776389541753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 540844380894807410889349 101408321417776389541753)
                    ·
                      rfl

theorem cell23_592476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_592476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592476 prefixEnd_592476 := by exact prefixLift 592476
  have htrace : WordTrace (prefixWord ++ tailWord_592476) baseStart_592476 baseEnd_592476 := by
    simpa [prefixWord, tailWord_592476, baseEnd_592476] using wordTrace_append hprefix tailTrace_592476
  have hstable : (prefixWord ++ tailWord_592476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592476).length < 2 ^ (prefixWord ++ tailWord_592476).sum := by decide
  have hdescent : baseEnd_592476 < baseStart_592476 := by decide
  rcases family_descends (prefixWord ++ tailWord_592476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592542 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_592542 : Nat := 118140960795 + 592542 * 2 ^ 59
def prefixEnd_592542 : Nat := 4983230072969 + 3 ^ 40 * 592542 * 2
def baseEnd_592542 : Nat := 304258853976525910399955

theorem tailTrace_592542 : CollatzResearch.WordTrace tailWord_592542 prefixEnd_592542 304258853976525910399955 := by
  unfold tailWord_592542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2701472777416125870239485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14407854812886004641277253 2701472777416125870239485)
  ·
    refine ⟨1013052291531047201339807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2701472777416125870239485 1013052291531047201339807)
    ·
      refine ⟨1519578437296570802009711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1013052291531047201339807 1519578437296570802009711)
      ·
        refine ⟨2279367655944856203014567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1519578437296570802009711 2279367655944856203014567)
        ·
          refine ⟨3419051483917284304521851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2279367655944856203014567 3419051483917284304521851)
          ·
            refine ⟨5128577225875926456782777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3419051483917284304521851 5128577225875926456782777)
            ·
              refine ⟨3846432919406944842587083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5128577225875926456782777 3846432919406944842587083)
              ·
                refine ⟨5769649379110417263880625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3846432919406944842587083 5769649379110417263880625)
                ·
                  refine ⟨4327237034332812947910469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5769649379110417263880625 4327237034332812947910469)
                  ·
                    refine ⟨811356943937402427733213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4327237034332812947910469 811356943937402427733213)
                    ·
                      refine ⟨304258853976525910399955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 811356943937402427733213 304258853976525910399955)
                      ·
                        rfl

theorem cell23_592542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_592542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592542 prefixEnd_592542 := by exact prefixLift 592542
  have htrace : WordTrace (prefixWord ++ tailWord_592542) baseStart_592542 baseEnd_592542 := by
    simpa [prefixWord, tailWord_592542, baseEnd_592542] using wordTrace_append hprefix tailTrace_592542
  have hstable : (prefixWord ++ tailWord_592542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592542).length < 2 ^ (prefixWord ++ tailWord_592542).sum := by decide
  have hdescent : baseEnd_592542 < baseStart_592542 := by decide
  rcases family_descends (prefixWord ++ tailWord_592542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592575 : List Nat := [1, 1, 2, 2, 2, 4, 1, 3, 2, 5]
def baseStart_592575 : Nat := 118140960795 + 592575 * 2 ^ 59
def prefixEnd_592575 : Nat := 4983230072969 + 3 ^ 40 * 592575 * 2
def baseEnd_592575 : Nat := 101425266279374760429101

theorem tailTrace_592575 : CollatzResearch.WordTrace tailWord_592575 prefixEnd_592575 101425266279374760429101 := by
  unfold tailWord_592575
  simp only [CollatzResearch.WordTrace]
  refine ⟨21612985828209453597867179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14408657218806302398578119 21612985828209453597867179)
  ·
    refine ⟨32419478742314180396800769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21612985828209453597867179 32419478742314180396800769)
    ·
      refine ⟨24314609056735635297600577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32419478742314180396800769 24314609056735635297600577)
      ·
        refine ⟨18235956792551726473200433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24314609056735635297600577 18235956792551726473200433)
        ·
          refine ⟨13676967594413794854900325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18235956792551726473200433 13676967594413794854900325)
          ·
            refine ⟨2564431423952586535293811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13676967594413794854900325 2564431423952586535293811)
            ·
              refine ⟨3846647135928879802940717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2564431423952586535293811 3846647135928879802940717)
              ·
                refine ⟨1442492675973329926102769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3846647135928879802940717 1442492675973329926102769)
                ·
                  refine ⟨1081869506979997444577077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1442492675973329926102769 1081869506979997444577077)
                  ·
                    refine ⟨101425266279374760429101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1081869506979997444577077 101425266279374760429101)
                    ·
                      rfl

theorem cell23_592575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 5].length) (baseStart_592575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592575 prefixEnd_592575 := by exact prefixLift 592575
  have htrace : WordTrace (prefixWord ++ tailWord_592575) baseStart_592575 baseEnd_592575 := by
    simpa [prefixWord, tailWord_592575, baseEnd_592575] using wordTrace_append hprefix tailTrace_592575
  have hstable : (prefixWord ++ tailWord_592575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592575).length < 2 ^ (prefixWord ++ tailWord_592575).sum := by decide
  have hdescent : baseEnd_592575 < baseStart_592575 := by decide
  rcases family_descends (prefixWord ++ tailWord_592575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592612 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 1, 6, 2]
def baseStart_592612 : Nat := 118140960795 + 592612 * 2 ^ 59
def prefixEnd_592612 : Nat := 4983230072969 + 3 ^ 40 * 592612 * 2
def baseEnd_592612 : Nat := 304294797622340636524633

theorem tailTrace_592612 : CollatzResearch.WordTrace tailWord_592612 prefixEnd_592612 304294797622340636524633 := by
  unfold tailWord_592612
  simp only [CollatzResearch.WordTrace]
  refine ⟨10807167664537704458482045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14409556886050272611309393 10807167664537704458482045)
  ·
    refine ⟨4052687874201639171930767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10807167664537704458482045 4052687874201639171930767)
    ·
      refine ⟨6079031811302458757896151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4052687874201639171930767 6079031811302458757896151)
      ·
        refine ⟨9118547716953688136844227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6079031811302458757896151 9118547716953688136844227)
        ·
          refine ⟨13677821575430532205266341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9118547716953688136844227 13677821575430532205266341)
          ·
            refine ⟨2564591545393224788487439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13677821575430532205266341 2564591545393224788487439)
            ·
              refine ⟨3846887318089837182731159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2564591545393224788487439 3846887318089837182731159)
              ·
                refine ⟨5770330977134755774096739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3846887318089837182731159 5770330977134755774096739)
                ·
                  refine ⟨8655496465702133661145109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5770330977134755774096739 8655496465702133661145109)
                  ·
                    refine ⟨405726396829787515366177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8655496465702133661145109 405726396829787515366177)
                    ·
                      refine ⟨304294797622340636524633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 405726396829787515366177 304294797622340636524633)
                      ·
                        rfl

theorem cell23_592612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 1, 6, 2].length) (baseStart_592612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592612 prefixEnd_592612 := by exact prefixLift 592612
  have htrace : WordTrace (prefixWord ++ tailWord_592612) baseStart_592612 baseEnd_592612 := by
    simpa [prefixWord, tailWord_592612, baseEnd_592612] using wordTrace_append hprefix tailTrace_592612
  have hstable : (prefixWord ++ tailWord_592612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592612).length < 2 ^ (prefixWord ++ tailWord_592612).sum := by decide
  have hdescent : baseEnd_592612 < baseStart_592612 := by decide
  rcases family_descends (prefixWord ++ tailWord_592612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592622 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 5, 4]
def baseStart_592622 : Nat := 118140960795 + 592622 * 2 ^ 59
def prefixEnd_592622 : Nat := 4983230072969 + 3 ^ 40 * 592622 * 2
def baseEnd_592622 : Nat := 101433310809628532466529

theorem tailTrace_592622 : CollatzResearch.WordTrace tailWord_592622 prefixEnd_592622 101433310809628532466529 := by
  unfold tailWord_592622
  simp only [CollatzResearch.WordTrace]
  refine ⟨2701837507379897578103515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14409800039359453749885413 2701837507379897578103515)
  ·
    refine ⟨4052756261069846367155273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2701837507379897578103515 4052756261069846367155273)
    ·
      refine ⟨3039567195802384775366455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4052756261069846367155273 3039567195802384775366455)
      ·
        refine ⟨4559350793703577163049683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3039567195802384775366455 4559350793703577163049683)
        ·
          refine ⟨6839026190555365744574525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4559350793703577163049683 6839026190555365744574525)
          ·
            refine ⟨2564634821458262154215447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6839026190555365744574525 2564634821458262154215447)
            ·
              refine ⟨3846952232187393231323171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2564634821458262154215447 3846952232187393231323171)
              ·
                refine ⟨5770428348281089846984757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3846952232187393231323171 5770428348281089846984757)
                ·
                  refine ⟨540977657651352173154821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5770428348281089846984757 540977657651352173154821)
                  ·
                    refine ⟨101433310809628532466529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 540977657651352173154821 101433310809628532466529)
                    ·
                      rfl

theorem cell23_592622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_592622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592622 prefixEnd_592622 := by exact prefixLift 592622
  have htrace : WordTrace (prefixWord ++ tailWord_592622) baseStart_592622 baseEnd_592622 := by
    simpa [prefixWord, tailWord_592622, baseEnd_592622] using wordTrace_append hprefix tailTrace_592622
  have hstable : (prefixWord ++ tailWord_592622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592622).length < 2 ^ (prefixWord ++ tailWord_592622).sum := by decide
  have hdescent : baseEnd_592622 < baseStart_592622 := by decide
  rcases family_descends (prefixWord ++ tailWord_592622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592642 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_592642 : Nat := 118140960795 + 592642 * 2 ^ 59
def prefixEnd_592642 : Nat := 4983230072969 + 3 ^ 40 * 592642 * 2
def baseEnd_592642 : Nat := 304310202041975519149495

theorem tailTrace_592642 : CollatzResearch.WordTrace tailWord_592642 prefixEnd_592642 304310202041975519149495 := by
  unfold tailWord_592642
  simp only [CollatzResearch.WordTrace]
  refine ⟨5403857379741681010139045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14410286345977816027037453 5403857379741681010139045)
  ·
    refine ⟨1013223258701565189401071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5403857379741681010139045 1013223258701565189401071)
    ·
      refine ⟨1519834888052347784101607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1013223258701565189401071 1519834888052347784101607)
      ·
        refine ⟨2279752332078521676152411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1519834888052347784101607 2279752332078521676152411)
        ·
          refine ⟨3419628498117782514228617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2279752332078521676152411 3419628498117782514228617)
          ·
            refine ⟨2564721373588336885671463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3419628498117782514228617 2564721373588336885671463)
            ·
              refine ⟨3847082060382505328507195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2564721373588336885671463 3847082060382505328507195)
              ·
                refine ⟨5770623090573757992760793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3847082060382505328507195 5770623090573757992760793)
                ·
                  refine ⟨4327967317930318494570595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5770623090573757992760793 4327967317930318494570595)
                  ·
                    refine ⟨6491950976895477741855893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4327967317930318494570595 6491950976895477741855893)
                    ·
                      refine ⟨304310202041975519149495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6491950976895477741855893 304310202041975519149495)
                      ·
                        rfl

theorem cell23_592642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_592642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592642 prefixEnd_592642 := by exact prefixLift 592642
  have htrace : WordTrace (prefixWord ++ tailWord_592642) baseStart_592642 baseEnd_592642 := by
    simpa [prefixWord, tailWord_592642, baseEnd_592642] using wordTrace_append hprefix tailTrace_592642
  have hstable : (prefixWord ++ tailWord_592642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592642).length < 2 ^ (prefixWord ++ tailWord_592642).sum := by decide
  have hdescent : baseEnd_592642 < baseStart_592642 := by decide
  rcases family_descends (prefixWord ++ tailWord_592642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592645 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 1, 7, 3]
def baseStart_592645 : Nat := 118140960795 + 592645 * 2 ^ 59
def prefixEnd_592645 : Nat := 4983230072969 + 3 ^ 40 * 592645 * 2
def baseEnd_592645 : Nat := 304311742483939007411981

theorem tailTrace_592645 : CollatzResearch.WordTrace tailWord_592645 prefixEnd_592645 304311742483939007411981 := by
  unfold tailWord_592645
  simp only [CollatzResearch.WordTrace]
  refine ⟨21615538937955855552915389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14410359291970570368610259 21615538937955855552915389)
  ·
    refine ⟨8105827101733445832343271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21615538937955855552915389 8105827101733445832343271)
    ·
      refine ⟨12158740652600168748514907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8105827101733445832343271 12158740652600168748514907)
      ·
        refine ⟨18238110978900253122772361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12158740652600168748514907 18238110978900253122772361)
        ·
          refine ⟨13678583234175189842079271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18238110978900253122772361 13678583234175189842079271)
          ·
            refine ⟨20517874851262784763118907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13678583234175189842079271 20517874851262784763118907)
            ·
              refine ⟨30776812276894177144678361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20517874851262784763118907 30776812276894177144678361)
              ·
                refine ⟨23082609207670632858508771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30776812276894177144678361 23082609207670632858508771)
                ·
                  refine ⟨34623913811505949287763157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23082609207670632858508771 34623913811505949287763157)
                  ·
                    refine ⟨811497979957170686431949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34623913811505949287763157 811497979957170686431949)
                    ·
                      refine ⟨304311742483939007411981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 811497979957170686431949 304311742483939007411981)
                      ·
                        rfl

theorem cell23_592645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 7, 3].length) (baseStart_592645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592645 prefixEnd_592645 := by exact prefixLift 592645
  have htrace : WordTrace (prefixWord ++ tailWord_592645) baseStart_592645 baseEnd_592645 := by
    simpa [prefixWord, tailWord_592645, baseEnd_592645] using wordTrace_append hprefix tailTrace_592645
  have hstable : (prefixWord ++ tailWord_592645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592645).length < 2 ^ (prefixWord ++ tailWord_592645).sum := by decide
  have hdescent : baseEnd_592645 < baseStart_592645 := by decide
  rcases family_descends (prefixWord ++ tailWord_592645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592665 : List Nat := [1, 2, 1, 2, 1, 1, 1, 6, 3, 5]
def baseStart_592665 : Nat := 118140960795 + 592665 * 2 ^ 59
def prefixEnd_592665 : Nat := 4983230072969 + 3 ^ 40 * 592665 * 2
def baseEnd_592665 : Nat := 101440670699009643053963

theorem tailTrace_592665 : CollatzResearch.WordTrace tailWord_592665 prefixEnd_592665 101440670699009643053963 := by
  unfold tailWord_592665
  simp only [CollatzResearch.WordTrace]
  refine ⟨21616268397883398968643449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14410845598588932645762299 21616268397883398968643449)
  ·
    refine ⟨16212201298412549226482587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21616268397883398968643449 16212201298412549226482587)
    ·
      refine ⟨24318301947618823839723881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16212201298412549226482587 24318301947618823839723881)
      ·
        refine ⟨18238726460714117879792911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24318301947618823839723881 18238726460714117879792911)
        ·
          refine ⟨27358089691071176819689367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18238726460714117879792911 27358089691071176819689367)
          ·
            refine ⟨41037134536606765229534051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27358089691071176819689367 41037134536606765229534051)
            ·
              refine ⟨61555701804910147844301077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41037134536606765229534051 61555701804910147844301077)
              ·
                refine ⟨2885423522105163180201613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61555701804910147844301077 2885423522105163180201613)
                ·
                  refine ⟨1082033820789436192575605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2885423522105163180201613 1082033820789436192575605)
                  ·
                    refine ⟨101440670699009643053963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1082033820789436192575605 101440670699009643053963)
                    ·
                      rfl

theorem cell23_592665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 5].length) (baseStart_592665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592665 prefixEnd_592665 := by exact prefixLift 592665
  have htrace : WordTrace (prefixWord ++ tailWord_592665) baseStart_592665 baseEnd_592665 := by
    simpa [prefixWord, tailWord_592665, baseEnd_592665] using wordTrace_append hprefix tailTrace_592665
  have hstable : (prefixWord ++ tailWord_592665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592665).length < 2 ^ (prefixWord ++ tailWord_592665).sum := by decide
  have hdescent : baseEnd_592665 < baseStart_592665 := by decide
  rcases family_descends (prefixWord ++ tailWord_592665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592689 : List Nat := [1, 2, 2, 3, 2, 1, 2, 3, 2, 3, 2]
def baseStart_592689 : Nat := 118140960795 + 592689 * 2 ^ 59
def prefixEnd_592689 : Nat := 4983230072969 + 3 ^ 40 * 592689 * 2
def baseEnd_592689 : Nat := 304334335632736835261779

theorem tailTrace_592689 : CollatzResearch.WordTrace tailWord_592689 prefixEnd_592689 304334335632736835261779 := by
  unfold tailWord_592689
  simp only [CollatzResearch.WordTrace]
  refine ⟨21617143749796451067517121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14411429166530967378344747 21617143749796451067517121)
  ·
    refine ⟨16212857812347338300637841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21617143749796451067517121 16212857812347338300637841)
    ·
      refine ⟨12159643359260503725478381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16212857812347338300637841 12159643359260503725478381)
      ·
        refine ⟨4559866259722688897054393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12159643359260503725478381 4559866259722688897054393)
        ·
          refine ⟨3419899694792016672790795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4559866259722688897054393 3419899694792016672790795)
          ·
            refine ⟨5129849542188025009186193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3419899694792016672790795 5129849542188025009186193)
            ·
              refine ⟨3847387156641018756889645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5129849542188025009186193 3847387156641018756889645)
              ·
                refine ⟨1442770183740382033833617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3847387156641018756889645 1442770183740382033833617)
                ·
                  refine ⟨1082077637805286525375213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1442770183740382033833617 1082077637805286525375213)
                  ·
                    refine ⟨405779114176982447015705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1082077637805286525375213 405779114176982447015705)
                    ·
                      refine ⟨304334335632736835261779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 405779114176982447015705 304334335632736835261779)
                      ·
                        rfl

theorem cell23_592689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_592689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592689 prefixEnd_592689 := by exact prefixLift 592689
  have htrace : WordTrace (prefixWord ++ tailWord_592689) baseStart_592689 baseEnd_592689 := by
    simpa [prefixWord, tailWord_592689, baseEnd_592689] using wordTrace_append hprefix tailTrace_592689
  have hstable : (prefixWord ++ tailWord_592689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592689).length < 2 ^ (prefixWord ++ tailWord_592689).sum := by decide
  have hdescent : baseEnd_592689 < baseStart_592689 := by decide
  rcases family_descends (prefixWord ++ tailWord_592689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592695 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 3, 6]
def baseStart_592695 : Nat := 118140960795 + 592695 * 2 ^ 59
def prefixEnd_592695 : Nat := 4983230072969 + 3 ^ 40 * 592695 * 2
def baseEnd_592695 : Nat := 101445805505554603928917

theorem tailTrace_592695 : CollatzResearch.WordTrace tailWord_592695 prefixEnd_592695 101445805505554603928917 := by
  unfold tailWord_592695
  simp only [CollatzResearch.WordTrace]
  refine ⟨21617362587774714092235539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14411575058516476061490359 21617362587774714092235539)
  ·
    refine ⟨32426043881662071138353309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21617362587774714092235539 32426043881662071138353309)
    ·
      refine ⟨12159766455623276676882491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32426043881662071138353309 12159766455623276676882491)
      ·
        refine ⟨18239649683434915015323737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12159766455623276676882491 18239649683434915015323737)
        ·
          refine ⟨13679737262576186261492803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18239649683434915015323737 13679737262576186261492803)
          ·
            refine ⟨20519605893864279392239205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13679737262576186261492803 20519605893864279392239205)
            ·
              refine ⟨3847426105099552386044851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20519605893864279392239205 3847426105099552386044851)
              ·
                refine ⟨5771139157649328579067277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3847426105099552386044851 5771139157649328579067277)
                ·
                  refine ⟨2164177184118498217150229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5771139157649328579067277 2164177184118498217150229)
                  ·
                    refine ⟨101445805505554603928917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2164177184118498217150229 101445805505554603928917)
                    ·
                      rfl

theorem cell23_592695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_592695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592695 prefixEnd_592695 := by exact prefixLift 592695
  have htrace : WordTrace (prefixWord ++ tailWord_592695) baseStart_592695 baseEnd_592695 := by
    simpa [prefixWord, tailWord_592695, baseEnd_592695] using wordTrace_append hprefix tailTrace_592695
  have hstable : (prefixWord ++ tailWord_592695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592695).length < 2 ^ (prefixWord ++ tailWord_592695).sum := by decide
  have hdescent : baseEnd_592695 < baseStart_592695 := by decide
  rcases family_descends (prefixWord ++ tailWord_592695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592712 : List Nat := [2, 1, 3, 1, 1, 3, 1, 3, 4, 4]
def baseStart_592712 : Nat := 118140960795 + 592712 * 2 ^ 59
def prefixEnd_592712 : Nat := 4983230072969 + 3 ^ 40 * 592712 * 2
def baseEnd_592712 : Nat := 101448715229263415091391

theorem tailTrace_592712 : CollatzResearch.WordTrace tailWord_592712 prefixEnd_592712 101448715229263415091391 := by
  unfold tailWord_592712
  simp only [CollatzResearch.WordTrace]
  refine ⟨10808991314356562997802195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14411988419142083997069593 10808991314356562997802195)
  ·
    refine ⟨16213486971534844496703293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10808991314356562997802195 16213486971534844496703293)
    ·
      refine ⟨6080057614325566686263735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16213486971534844496703293 6080057614325566686263735)
      ·
        refine ⟨9120086421488350029395603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6080057614325566686263735 9120086421488350029395603)
        ·
          refine ⟨13680129632232525044093405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9120086421488350029395603 13680129632232525044093405)
          ·
            refine ⟨5130048612087196891535027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13680129632232525044093405 5130048612087196891535027)
            ·
              refine ⟨7695072918130795337302541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5130048612087196891535027 7695072918130795337302541)
              ·
                refine ⟨2885652344299048251488453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7695072918130795337302541 2885652344299048251488453)
                ·
                  refine ⟨541059814556071547154085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2885652344299048251488453 541059814556071547154085)
                  ·
                    refine ⟨101448715229263415091391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 541059814556071547154085 101448715229263415091391)
                    ·
                      rfl

theorem cell23_592712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_592712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592712 prefixEnd_592712 := by exact prefixLift 592712
  have htrace : WordTrace (prefixWord ++ tailWord_592712) baseStart_592712 baseEnd_592712 := by
    simpa [prefixWord, tailWord_592712, baseEnd_592712] using wordTrace_append hprefix tailTrace_592712
  have hstable : (prefixWord ++ tailWord_592712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592712).length < 2 ^ (prefixWord ++ tailWord_592712).sum := by decide
  have hdescent : baseEnd_592712 < baseStart_592712 := by decide
  rcases family_descends (prefixWord ++ tailWord_592712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592713 : List Nat := [1, 2, 1, 1, 2, 6, 3, 2, 1, 1, 3]
def baseStart_592713 : Nat := 118140960795 + 592713 * 2 ^ 59
def prefixEnd_592713 : Nat := 4983230072969 + 3 ^ 40 * 592713 * 2
def baseEnd_592713 : Nat := 304346659168444741361669

theorem tailTrace_592713 : CollatzResearch.WordTrace tailWord_592713 prefixEnd_592713 304346659168444741361669 := by
  unfold tailWord_592713
  simp only [CollatzResearch.WordTrace]
  refine ⟨21618019101709503166390793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14412012734473002110927195 21618019101709503166390793)
  ·
    refine ⟨16213514326282127374793095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21618019101709503166390793 16213514326282127374793095)
    ·
      refine ⟨24320271489423191062189643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16213514326282127374793095 24320271489423191062189643)
      ·
        refine ⟨36480407234134786593284465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24320271489423191062189643 36480407234134786593284465)
        ·
          refine ⟨27360305425601089944963349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36480407234134786593284465 27360305425601089944963349)
          ·
            refine ⟨1282514316825051091170157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27360305425601089944963349 1282514316825051091170157)
            ·
              refine ⟨480942868809394159188809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1282514316825051091170157 480942868809394159188809)
              ·
                refine ⟨360707151607045619391607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 480942868809394159188809 360707151607045619391607)
                ·
                  refine ⟨541060727410568429087411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 360707151607045619391607 541060727410568429087411)
                  ·
                    refine ⟨811591091115852643631117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 541060727410568429087411 811591091115852643631117)
                    ·
                      refine ⟨304346659168444741361669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 811591091115852643631117 304346659168444741361669)
                      ·
                        rfl

theorem cell23_592713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 1, 1, 3].length) (baseStart_592713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592713 prefixEnd_592713 := by exact prefixLift 592713
  have htrace : WordTrace (prefixWord ++ tailWord_592713) baseStart_592713 baseEnd_592713 := by
    simpa [prefixWord, tailWord_592713, baseEnd_592713] using wordTrace_append hprefix tailTrace_592713
  have hstable : (prefixWord ++ tailWord_592713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592713).length < 2 ^ (prefixWord ++ tailWord_592713).sum := by decide
  have hdescent : baseEnd_592713 < baseStart_592713 := by decide
  rcases family_descends (prefixWord ++ tailWord_592713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592722 : List Nat := [3, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_592722 : Nat := 118140960795 + 592722 * 2 ^ 59
def prefixEnd_592722 : Nat := 4983230072969 + 3 ^ 40 * 592722 * 2
def baseEnd_592722 : Nat := 304351280494335206149127

theorem tailTrace_592722 : CollatzResearch.WordTrace tailWord_592722 prefixEnd_592722 304351280494335206149127 := by
  unfold tailWord_592722
  simp only [CollatzResearch.WordTrace]
  refine ⟨5404586839669224425867105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14412231572451265135645613 5404586839669224425867105)
  ·
    refine ⟨4053440129751918319400329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5404586839669224425867105 4053440129751918319400329)
    ·
      refine ⟨3040080097313938739550247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4053440129751918319400329 3040080097313938739550247)
      ·
        refine ⟨4560120145970908109325371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3040080097313938739550247 4560120145970908109325371)
        ·
          refine ⟨6840180218956362163988057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4560120145970908109325371 6840180218956362163988057)
          ·
            refine ⟨5130135164217271622991043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6840180218956362163988057 5130135164217271622991043)
            ·
              refine ⟨7695202746325907434486565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5130135164217271622991043 7695202746325907434486565)
              ·
                refine ⟨1442850514936107643966231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7695202746325907434486565 1442850514936107643966231)
                ·
                  refine ⟨2164275772404161465949347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1442850514936107643966231 2164275772404161465949347)
                  ·
                    refine ⟨3246413658606242198924021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2164275772404161465949347 3246413658606242198924021)
                    ·
                      refine ⟨304351280494335206149127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3246413658606242198924021 304351280494335206149127)
                      ·
                        rfl

theorem cell23_592722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_592722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592722 prefixEnd_592722 := by exact prefixLift 592722
  have htrace : WordTrace (prefixWord ++ tailWord_592722) baseStart_592722 baseEnd_592722 := by
    simpa [prefixWord, tailWord_592722, baseEnd_592722] using wordTrace_append hprefix tailTrace_592722
  have hstable : (prefixWord ++ tailWord_592722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592722).length < 2 ^ (prefixWord ++ tailWord_592722).sum := by decide
  have hdescent : baseEnd_592722 < baseStart_592722 := by decide
  rcases family_descends (prefixWord ++ tailWord_592722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592729 : List Nat := [1, 2, 1, 2, 2, 5, 1, 3, 2, 4]
def baseStart_592729 : Nat := 118140960795 + 592729 * 2 ^ 59
def prefixEnd_592729 : Nat := 4983230072969 + 3 ^ 40 * 592729 * 2
def baseEnd_592729 : Nat := 101451624952972226253865

theorem tailTrace_592729 : CollatzResearch.WordTrace tailWord_592729 prefixEnd_592729 101451624952972226253865 := by
  unfold tailWord_592729
  simp only [CollatzResearch.WordTrace]
  refine ⟨21618602669651537898973241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14412401779767691932648827 21618602669651537898973241)
  ·
    refine ⟨16213952002238653424229931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21618602669651537898973241 16213952002238653424229931)
    ·
      refine ⟨24320928003357980136344897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16213952002238653424229931 24320928003357980136344897)
      ·
        refine ⟨18240696002518485102258673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24320928003357980136344897 18240696002518485102258673)
        ·
          refine ⟨13680522001888863826694005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18240696002518485102258673 13680522001888863826694005)
          ·
            refine ⟨1282548937677080983752563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13680522001888863826694005 1282548937677080983752563)
            ·
              refine ⟨1923823406515621475628845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1282548937677080983752563 1923823406515621475628845)
              ·
                refine ⟨721433777443358053360817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1923823406515621475628845 721433777443358053360817)
                ·
                  refine ⟨541075333082518540020613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 721433777443358053360817 541075333082518540020613)
                  ·
                    refine ⟨101451624952972226253865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 541075333082518540020613 101451624952972226253865)
                    ·
                      rfl

theorem cell23_592729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 4].length) (baseStart_592729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592729 prefixEnd_592729 := by exact prefixLift 592729
  have htrace : WordTrace (prefixWord ++ tailWord_592729) baseStart_592729 baseEnd_592729 := by
    simpa [prefixWord, tailWord_592729, baseEnd_592729] using wordTrace_append hprefix tailTrace_592729
  have hstable : (prefixWord ++ tailWord_592729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592729).length < 2 ^ (prefixWord ++ tailWord_592729).sum := by decide
  have hdescent : baseEnd_592729 < baseStart_592729 := by decide
  rcases family_descends (prefixWord ++ tailWord_592729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592739 : List Nat := [1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 3]
def baseStart_592739 : Nat := 118140960795 + 592739 * 2 ^ 59
def prefixEnd_592739 : Nat := 4983230072969 + 3 ^ 40 * 592739 * 2
def baseEnd_592739 : Nat := 304360009665461639636549

theorem tailTrace_592739 : CollatzResearch.WordTrace tailWord_592739 prefixEnd_592739 304360009665461639636549 := by
  unfold tailWord_592739
  simp only [CollatzResearch.WordTrace]
  refine ⟨21618967399615309606837271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14412644933076873071224847 21618967399615309606837271)
  ·
    refine ⟨32428451099422964410255907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21618967399615309606837271 32428451099422964410255907)
    ·
      refine ⟨48642676649134446615383861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32428451099422964410255907 48642676649134446615383861)
      ·
        refine ⟨4560250935856354370192237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48642676649134446615383861 4560250935856354370192237)
        ·
          refine ⟨1710094100946132888822089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4560250935856354370192237 1710094100946132888822089)
          ·
            refine ⟨1282570575709599666616567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1710094100946132888822089 1282570575709599666616567)
            ·
              refine ⟨1923855863564399499924851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1282570575709599666616567 1923855863564399499924851)
              ·
                refine ⟨2885783795346599249887277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1923855863564399499924851 2885783795346599249887277)
                ·
                  refine ⟨1082168923254974718707729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2885783795346599249887277 1082168923254974718707729)
                  ·
                    refine ⟨811626692441231039030797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1082168923254974718707729 811626692441231039030797)
                    ·
                      refine ⟨304360009665461639636549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 811626692441231039030797 304360009665461639636549)
                      ·
                        rfl

theorem cell23_592739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_592739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592739 prefixEnd_592739 := by exact prefixLift 592739
  have htrace : WordTrace (prefixWord ++ tailWord_592739) baseStart_592739 baseEnd_592739 := by
    simpa [prefixWord, tailWord_592739, baseEnd_592739] using wordTrace_append hprefix tailTrace_592739
  have hstable : (prefixWord ++ tailWord_592739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592739).length < 2 ^ (prefixWord ++ tailWord_592739).sum := by decide
  have hdescent : baseEnd_592739 < baseStart_592739 := by decide
  rcases family_descends (prefixWord ++ tailWord_592739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592752 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 3]
def baseStart_592752 : Nat := 118140960795 + 592752 * 2 ^ 59
def prefixEnd_592752 : Nat := 4983230072969 + 3 ^ 40 * 592752 * 2
def baseEnd_592752 : Nat := 304366684913970088773989

theorem tailTrace_592752 : CollatzResearch.WordTrace tailWord_592752 prefixEnd_592752 304366684913970088773989 := by
  unfold tailWord_592752
  simp only [CollatzResearch.WordTrace]
  refine ⟨10809720774284106413530255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14412961032378808551373673 10809720774284106413530255)
  ·
    refine ⟨16214581161426159620295383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10809720774284106413530255 16214581161426159620295383)
    ·
      refine ⟨24321871742139239430443075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16214581161426159620295383 24321871742139239430443075)
      ·
        refine ⟨36482807613208859145664613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24321871742139239430443075 36482807613208859145664613)
        ·
          refine ⟨6840526427476661089812115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36482807613208859145664613 6840526427476661089812115)
          ·
            refine ⟨10260789641214991634718173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6840526427476661089812115 10260789641214991634718173)
            ·
              refine ⟨3847796115455621863019315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10260789641214991634718173 3847796115455621863019315)
              ·
                refine ⟨5771694173183432794528973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3847796115455621863019315 5771694173183432794528973)
                ·
                  refine ⟨2164385314943787297948365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5771694173183432794528973 2164385314943787297948365)
                  ·
                    refine ⟨811644493103920236730637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2164385314943787297948365 811644493103920236730637)
                    ·
                      refine ⟨304366684913970088773989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 811644493103920236730637 304366684913970088773989)
                      ·
                        rfl

theorem cell23_592752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 3].length) (baseStart_592752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592752 prefixEnd_592752 := by exact prefixLift 592752
  have htrace : WordTrace (prefixWord ++ tailWord_592752) baseStart_592752 baseEnd_592752 := by
    simpa [prefixWord, tailWord_592752, baseEnd_592752] using wordTrace_append hprefix tailTrace_592752
  have hstable : (prefixWord ++ tailWord_592752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592752).length < 2 ^ (prefixWord ++ tailWord_592752).sum := by decide
  have hdescent : baseEnd_592752 < baseStart_592752 := by decide
  rcases family_descends (prefixWord ++ tailWord_592752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592779 : List Nat := [1, 1, 1, 1, 4, 2, 3, 2, 3, 3, 2]
def baseStart_592779 : Nat := 118140960795 + 592779 * 2 ^ 59
def prefixEnd_592779 : Nat := 4983230072969 + 3 ^ 40 * 592779 * 2
def baseEnd_592779 : Nat := 304380548891641483136365

theorem tailTrace_592779 : CollatzResearch.WordTrace tailWord_592779 prefixEnd_592779 304380548891641483136365 := by
  unfold tailWord_592779
  simp only [CollatzResearch.WordTrace]
  refine ⟨21620426319470396438293391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14413617546313597625528927 21620426319470396438293391)
  ·
    refine ⟨32430639479205594657440087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21620426319470396438293391 32430639479205594657440087)
    ·
      refine ⟨48645959218808391986160131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32430639479205594657440087 48645959218808391986160131)
      ·
        refine ⟨72968938828212587979240197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48645959218808391986160131 72968938828212587979240197)
        ·
          refine ⟨13681676030289860246107537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72968938828212587979240197 13681676030289860246107537)
          ·
            refine ⟨10261257022717395184580653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13681676030289860246107537 10261257022717395184580653)
            ·
              refine ⟨3847971383519023194217745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10261257022717395184580653 3847971383519023194217745)
              ·
                refine ⟨2885978537639267395663309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3847971383519023194217745 2885978537639267395663309)
                ·
                  refine ⟨1082241951614725273373741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2885978537639267395663309 1082241951614725273373741)
                  ·
                    refine ⟨405840731855521977515153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1082241951614725273373741 405840731855521977515153)
                    ·
                      refine ⟨304380548891641483136365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 405840731855521977515153 304380548891641483136365)
                      ·
                        rfl

theorem cell23_592779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 3, 2].length) (baseStart_592779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592779 prefixEnd_592779 := by exact prefixLift 592779
  have htrace : WordTrace (prefixWord ++ tailWord_592779) baseStart_592779 baseEnd_592779 := by
    simpa [prefixWord, tailWord_592779, baseEnd_592779] using wordTrace_append hprefix tailTrace_592779
  have hstable : (prefixWord ++ tailWord_592779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592779).length < 2 ^ (prefixWord ++ tailWord_592779).sum := by decide
  have hdescent : baseEnd_592779 < baseStart_592779 := by decide
  rcases family_descends (prefixWord ++ tailWord_592779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592795 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 9]
def baseStart_592795 : Nat := 118140960795 + 592795 * 2 ^ 59
def prefixEnd_592795 : Nat := 4983230072969 + 3 ^ 40 * 592795 * 2
def baseEnd_592795 : Nat := 304388764582113420536291

theorem tailTrace_592795 : CollatzResearch.WordTrace tailWord_592795 prefixEnd_592795 304388764582113420536291 := by
  unfold tailWord_592795
  simp only [CollatzResearch.WordTrace]
  refine ⟨21621009887412431170875839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14414006591608287447250559 21621009887412431170875839)
  ·
    refine ⟨32431514831118646756313759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21621009887412431170875839 32431514831118646756313759)
    ·
      refine ⟨48647272246677970134470639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32431514831118646756313759 48647272246677970134470639)
      ·
        refine ⟨72970908370016955201705959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48647272246677970134470639 72970908370016955201705959)
        ·
          refine ⟨109456362555025432802558939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72970908370016955201705959 109456362555025432802558939)
          ·
            refine ⟨164184543832538149203838409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109456362555025432802558939 164184543832538149203838409)
            ·
              refine ⟨123138407874403611902878807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164184543832538149203838409 123138407874403611902878807)
              ·
                refine ⟨184707611811605417854318211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123138407874403611902878807 184707611811605417854318211)
                ·
                  refine ⟨277061417717408126781477317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184707611811605417854318211 277061417717408126781477317)
                  ·
                    refine ⟨51949015822014023771526997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 277061417717408126781477317 51949015822014023771526997)
                    ·
                      refine ⟨304388764582113420536291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 51949015822014023771526997 304388764582113420536291)
                      ·
                        rfl

theorem cell23_592795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 9].length) (baseStart_592795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592795 prefixEnd_592795 := by exact prefixLift 592795
  have htrace : WordTrace (prefixWord ++ tailWord_592795) baseStart_592795 baseEnd_592795 := by
    simpa [prefixWord, tailWord_592795, baseEnd_592795] using wordTrace_append hprefix tailTrace_592795
  have hstable : (prefixWord ++ tailWord_592795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592795).length < 2 ^ (prefixWord ++ tailWord_592795).sum := by decide
  have hdescent : baseEnd_592795 < baseStart_592795 := by decide
  rcases family_descends (prefixWord ++ tailWord_592795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592809 : List Nat := [1, 2, 1, 1, 1, 1, 5, 4, 1, 4, 2]
def baseStart_592809 : Nat := 118140960795 + 592809 * 2 ^ 59
def prefixEnd_592809 : Nat := 4983230072969 + 3 ^ 40 * 592809 * 2
def baseEnd_592809 : Nat := 304395953311276365761227

theorem tailTrace_592809 : CollatzResearch.WordTrace tailWord_592809 prefixEnd_592809 304395953311276365761227 := by
  unfold tailWord_592809
  simp only [CollatzResearch.WordTrace]
  refine ⟨21621520509361711561885481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14414347006241141041256987 21621520509361711561885481)
  ·
    refine ⟨16216140382021283671414111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21621520509361711561885481 16216140382021283671414111)
    ·
      refine ⟨24324210573031925507121167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16216140382021283671414111 24324210573031925507121167)
      ·
        refine ⟨36486315859547888260681751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24324210573031925507121167 36486315859547888260681751)
        ·
          refine ⟨54729473789321832391022627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36486315859547888260681751 54729473789321832391022627)
          ·
            refine ⟨82094210683982748586533941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54729473789321832391022627 82094210683982748586533941)
            ·
              refine ⟨7696332251623382679987557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82094210683982748586533941 7696332251623382679987557)
              ·
                refine ⟨1443062297179384252497667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7696332251623382679987557 1443062297179384252497667)
                ·
                  refine ⟨2164593445769076378746501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1443062297179384252497667 2164593445769076378746501)
                  ·
                    refine ⟨405861271081701821014969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2164593445769076378746501 405861271081701821014969)
                    ·
                      refine ⟨304395953311276365761227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 405861271081701821014969 304395953311276365761227)
                      ·
                        rfl

theorem cell23_592809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 4, 2].length) (baseStart_592809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592809 prefixEnd_592809 := by exact prefixLift 592809
  have htrace : WordTrace (prefixWord ++ tailWord_592809) baseStart_592809 baseEnd_592809 := by
    simpa [prefixWord, tailWord_592809, baseEnd_592809] using wordTrace_append hprefix tailTrace_592809
  have hstable : (prefixWord ++ tailWord_592809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592809).length < 2 ^ (prefixWord ++ tailWord_592809).sum := by decide
  have hdescent : baseEnd_592809 < baseStart_592809 := by decide
  rcases family_descends (prefixWord ++ tailWord_592809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592812 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 3]
def baseStart_592812 : Nat := 118140960795 + 592812 * 2 ^ 59
def prefixEnd_592812 : Nat := 4983230072969 + 3 ^ 40 * 592812 * 2
def baseEnd_592812 : Nat := 304397493753239854023713

theorem tailTrace_592812 : CollatzResearch.WordTrace tailWord_592812 prefixEnd_592812 304397493753239854023713 := by
  unfold tailWord_592812
  simp only [CollatzResearch.WordTrace]
  refine ⟨10810814964175421537122345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14414419952233895382829793 10810814964175421537122345)
  ·
    refine ⟨8108111223131566152841759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10810814964175421537122345 8108111223131566152841759)
    ·
      refine ⟨12162166834697349229262639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8108111223131566152841759 12162166834697349229262639)
      ·
        refine ⟨18243250252046023843893959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12162166834697349229262639 18243250252046023843893959)
        ·
          refine ⟨27364875378069035765840939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18243250252046023843893959 27364875378069035765840939)
          ·
            refine ⟨41047313067103553648761409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27364875378069035765840939 41047313067103553648761409)
            ·
              refine ⟨30785484800327665236571057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41047313067103553648761409 30785484800327665236571057)
              ·
                refine ⟨23089113600245748927428293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30785484800327665236571057 23089113600245748927428293)
                ·
                  refine ⟨4329208800046077923892805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23089113600245748927428293 4329208800046077923892805)
                  ·
                    refine ⟨811726650008639610729901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4329208800046077923892805 811726650008639610729901)
                    ·
                      refine ⟨304397493753239854023713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 811726650008639610729901 304397493753239854023713)
                      ·
                        rfl

theorem cell23_592812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 3].length) (baseStart_592812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592812 prefixEnd_592812 := by exact prefixLift 592812
  have htrace : WordTrace (prefixWord ++ tailWord_592812) baseStart_592812 baseEnd_592812 := by
    simpa [prefixWord, tailWord_592812, baseEnd_592812] using wordTrace_append hprefix tailTrace_592812
  have hstable : (prefixWord ++ tailWord_592812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592812).length < 2 ^ (prefixWord ++ tailWord_592812).sum := by decide
  have hdescent : baseEnd_592812 < baseStart_592812 := by decide
  rcases family_descends (prefixWord ++ tailWord_592812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592820 : List Nat := [2, 5, 2, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_592820 : Nat := 118140960795 + 592820 * 2 ^ 59
def prefixEnd_592820 : Nat := 4983230072969 + 3 ^ 40 * 592820 * 2
def baseEnd_592820 : Nat := 304401601598475822723677

theorem tailTrace_592820 : CollatzResearch.WordTrace tailWord_592820 prefixEnd_592820 304401601598475822723677 := by
  unfold tailWord_592820
  simp only [CollatzResearch.WordTrace]
  refine ⟨10810960856160930220267957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14414614474881240293690609 10810960856160930220267957)
  ·
    refine ⟨1013527580265087208150121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10810960856160930220267957 1013527580265087208150121)
    ·
      refine ⟨760145685198815406112591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1013527580265087208150121 760145685198815406112591)
      ·
        refine ⟨1140218527798223109168887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 760145685198815406112591 1140218527798223109168887)
        ·
          refine ⟨1710327791697334663753331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1140218527798223109168887 1710327791697334663753331)
          ·
            refine ⟨2565491687546001995629997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1710327791697334663753331 2565491687546001995629997)
            ·
              refine ⟨962059382829750748361249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2565491687546001995629997 962059382829750748361249)
              ·
                refine ⟨721544537122313061270937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 962059382829750748361249 721544537122313061270937)
                ·
                  refine ⟨541158402841734795953203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 721544537122313061270937 541158402841734795953203)
                  ·
                    refine ⟨811737604262602193929805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 541158402841734795953203 811737604262602193929805)
                    ·
                      refine ⟨304401601598475822723677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 811737604262602193929805 304401601598475822723677)
                      ·
                        rfl

theorem cell23_592820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_592820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592820 prefixEnd_592820 := by exact prefixLift 592820
  have htrace : WordTrace (prefixWord ++ tailWord_592820) baseStart_592820 baseEnd_592820 := by
    simpa [prefixWord, tailWord_592820, baseEnd_592820] using wordTrace_append hprefix tailTrace_592820
  have hstable : (prefixWord ++ tailWord_592820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592820).length < 2 ^ (prefixWord ++ tailWord_592820).sum := by decide
  have hdescent : baseEnd_592820 < baseStart_592820 := by decide
  rcases family_descends (prefixWord ++ tailWord_592820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592826 : List Nat := [3, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2]
def baseStart_592826 : Nat := 118140960795 + 592826 * 2 ^ 59
def prefixEnd_592826 : Nat := 4983230072969 + 3 ^ 40 * 592826 * 2
def baseEnd_592826 : Nat := 304404682482402799248649

theorem tailTrace_592826 : CollatzResearch.WordTrace tailWord_592826 prefixEnd_592826 304404682482402799248649 := by
  unfold tailWord_592826
  simp only [CollatzResearch.WordTrace]
  refine ⟨5405535137575030866313583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14414760366866748976836221 5405535137575030866313583)
  ·
    refine ⟨8108302706362546299470375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5405535137575030866313583 8108302706362546299470375)
    ·
      refine ⟨12162454059543819449205563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8108302706362546299470375 12162454059543819449205563)
      ·
        refine ⟨18243681089315729173808345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12162454059543819449205563 18243681089315729173808345)
        ·
          refine ⟨13682760816986796880356259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18243681089315729173808345 13682760816986796880356259)
          ·
            refine ⟨20524141225480195320534389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13682760816986796880356259 20524141225480195320534389)
            ·
              refine ⟨1924138239888768311300099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20524141225480195320534389 1924138239888768311300099)
              ·
                refine ⟨2886207359833152466950149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1924138239888768311300099 2886207359833152466950149)
                ·
                  refine ⟨541163879968716087553153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2886207359833152466950149 541163879968716087553153)
                  ·
                    refine ⟨405872909976537065664865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 541163879968716087553153 405872909976537065664865)
                    ·
                      refine ⟨304404682482402799248649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 405872909976537065664865 304404682482402799248649)
                      ·
                        rfl

theorem cell23_592826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2].length) (baseStart_592826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592826 prefixEnd_592826 := by exact prefixLift 592826
  have htrace : WordTrace (prefixWord ++ tailWord_592826) baseStart_592826 baseEnd_592826 := by
    simpa [prefixWord, tailWord_592826, baseEnd_592826] using wordTrace_append hprefix tailTrace_592826
  have hstable : (prefixWord ++ tailWord_592826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592826).length < 2 ^ (prefixWord ++ tailWord_592826).sum := by decide
  have hdescent : baseEnd_592826 < baseStart_592826 := by decide
  rcases family_descends (prefixWord ++ tailWord_592826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592832 : List Nat := [2, 1, 1, 2, 3, 3, 1, 3, 7]
def baseStart_592832 : Nat := 118140960795 + 592832 * 2 ^ 59
def prefixEnd_592832 : Nat := 4983230072969 + 3 ^ 40 * 592832 * 2
def baseEnd_592832 : Nat := 33823084818481086197069

theorem tailTrace_592832 : CollatzResearch.WordTrace tailWord_592832 prefixEnd_592832 33823084818481086197069 := by
  unfold tailWord_592832
  simp only [CollatzResearch.WordTrace]
  refine ⟨10811179694139193244986375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14414906258852257659981833 10811179694139193244986375)
  ·
    refine ⟨16216769541208789867479563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10811179694139193244986375 16216769541208789867479563)
    ·
      refine ⟨24325154311813184801219345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16216769541208789867479563 24325154311813184801219345)
      ·
        refine ⟨18243865733859888600914509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24325154311813184801219345 18243865733859888600914509)
        ·
          refine ⟨6841449650197458225342941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18243865733859888600914509 6841449650197458225342941)
          ·
            refine ⟨2565543618824046834503603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6841449650197458225342941 2565543618824046834503603)
            ·
              refine ⟨3848315428236070251755405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2565543618824046834503603 3848315428236070251755405)
              ·
                refine ⟨1443118285588526344408277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3848315428236070251755405 1443118285588526344408277)
                ·
                  refine ⟨33823084818481086197069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1443118285588526344408277 33823084818481086197069)
                  ·
                    rfl

theorem cell23_592832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 7].length) (baseStart_592832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592832 prefixEnd_592832 := by exact prefixLift 592832
  have htrace : WordTrace (prefixWord ++ tailWord_592832) baseStart_592832 baseEnd_592832 := by
    simpa [prefixWord, tailWord_592832, baseEnd_592832] using wordTrace_append hprefix tailTrace_592832
  have hstable : (prefixWord ++ tailWord_592832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592832).length < 2 ^ (prefixWord ++ tailWord_592832).sum := by decide
  have hdescent : baseEnd_592832 < baseStart_592832 := by decide
  rcases family_descends (prefixWord ++ tailWord_592832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592879 : List Nat := [1, 1, 2, 1, 4, 4, 1, 2, 2, 5]
def baseStart_592879 : Nat := 118140960795 + 592879 * 2 ^ 59
def prefixEnd_592879 : Nat := 4983230072969 + 3 ^ 40 * 592879 * 2
def baseEnd_592879 : Nat := 101477298985697030628635

theorem tailTrace_592879 : CollatzResearch.WordTrace tailWord_592879 prefixEnd_592879 101477298985697030628635 := by
  unfold tailWord_592879
  simp only [CollatzResearch.WordTrace]
  refine ⟨21624073619108113516933691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14416049079405409011289127 21624073619108113516933691)
  ·
    refine ⟨32436110428662170275400537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21624073619108113516933691 32436110428662170275400537)
    ·
      refine ⟨24327082821496627706550403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32436110428662170275400537 24327082821496627706550403)
      ·
        refine ⟨36490624232244941559825605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24327082821496627706550403 36490624232244941559825605)
        ·
          refine ⟨6841992043545926542467301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36490624232244941559825605 6841992043545926542467301)
          ·
            refine ⟨1282873508164861226712619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6841992043545926542467301 1282873508164861226712619)
            ·
              refine ⟨1924310262247291840068929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1282873508164861226712619 1924310262247291840068929)
              ·
                refine ⟨1443232696685468880051697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1924310262247291840068929 1443232696685468880051697)
                ·
                  refine ⟨1082424522514101660038773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1443232696685468880051697 1082424522514101660038773)
                  ·
                    refine ⟨101477298985697030628635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1082424522514101660038773 101477298985697030628635)
                    ·
                      rfl

theorem cell23_592879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 5].length) (baseStart_592879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592879 prefixEnd_592879 := by exact prefixLift 592879
  have htrace : WordTrace (prefixWord ++ tailWord_592879) baseStart_592879 baseEnd_592879 := by
    simpa [prefixWord, tailWord_592879, baseEnd_592879] using wordTrace_append hprefix tailTrace_592879
  have hstable : (prefixWord ++ tailWord_592879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592879).length < 2 ^ (prefixWord ++ tailWord_592879).sum := by decide
  have hdescent : baseEnd_592879 < baseStart_592879 := by decide
  rcases family_descends (prefixWord ++ tailWord_592879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592894 : List Nat := [4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2]
def baseStart_592894 : Nat := 118140960795 + 592894 * 2 ^ 59
def prefixEnd_592894 : Nat := 4983230072969 + 3 ^ 40 * 592894 * 2
def baseEnd_592894 : Nat := 304439599166908533198337

theorem tailTrace_592894 : CollatzResearch.WordTrace tailWord_592894 prefixEnd_592894 304439599166908533198337 := by
  unfold tailWord_592894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2703077589256721384841217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14416413809369180719153157 2703077589256721384841217)
  ·
    refine ⟨2027308191942541038630913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2703077589256721384841217 2027308191942541038630913)
    ·
      refine ⟨1520481143956905778973185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2027308191942541038630913 1520481143956905778973185)
      ·
        refine ⟨1140360857967679334229889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1520481143956905778973185 1140360857967679334229889)
        ·
          refine ⟨855270643475759500672417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1140360857967679334229889 855270643475759500672417)
          ·
            refine ⟨641452982606819625504313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 855270643475759500672417 641452982606819625504313)
            ·
              refine ⟨481089736955114719128235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 641452982606819625504313 481089736955114719128235)
              ·
                refine ⟨721634605432672078692353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 481089736955114719128235 721634605432672078692353)
                ·
                  refine ⟨541225954074504059019265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 721634605432672078692353 541225954074504059019265)
                  ·
                    refine ⟨405919465555878044264449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 541225954074504059019265 405919465555878044264449)
                    ·
                      refine ⟨304439599166908533198337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 405919465555878044264449 304439599166908533198337)
                      ·
                        rfl

theorem cell23_592894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_592894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592894 prefixEnd_592894 := by exact prefixLift 592894
  have htrace : WordTrace (prefixWord ++ tailWord_592894) baseStart_592894 baseEnd_592894 := by
    simpa [prefixWord, tailWord_592894, baseEnd_592894] using wordTrace_append hprefix tailTrace_592894
  have hstable : (prefixWord ++ tailWord_592894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592894).length < 2 ^ (prefixWord ++ tailWord_592894).sum := by decide
  have hdescent : baseEnd_592894 < baseStart_592894 := by decide
  rcases family_descends (prefixWord ++ tailWord_592894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592939 : List Nat := [1, 1, 1, 1, 2, 1, 8, 2, 6]
def baseStart_592939 : Nat := 118140960795 + 592939 * 2 ^ 59
def prefixEnd_592939 : Nat := 4983230072969 + 3 ^ 40 * 592939 * 2
def baseEnd_592939 : Nat := 33829189532928984126181

theorem tailTrace_592939 : CollatzResearch.WordTrace tailWord_592939 prefixEnd_592939 33829189532928984126181 := by
  unfold tailWord_592939
  simp only [CollatzResearch.WordTrace]
  refine ⟨21626261998890743764117871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14417507999260495842745247 21626261998890743764117871)
  ·
    refine ⟨32439392998336115646176807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21626261998890743764117871 32439392998336115646176807)
    ·
      refine ⟨48659089497504173469265211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32439392998336115646176807 48659089497504173469265211)
      ·
        refine ⟨72988634246256260203897817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48659089497504173469265211 72988634246256260203897817)
        ·
          refine ⟨54741475684692195152923363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72988634246256260203897817 54741475684692195152923363)
          ·
            refine ⟨82112213527038292729385045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54741475684692195152923363 82112213527038292729385045)
            ·
              refine ⟨962252502269979992922481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 82112213527038292729385045 962252502269979992922481)
              ·
                refine ⟨721689376702484994691861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 962252502269979992922481 721689376702484994691861)
                ·
                  refine ⟨33829189532928984126181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 721689376702484994691861 33829189532928984126181)
                  ·
                    rfl

theorem cell23_592939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 6].length) (baseStart_592939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592939 prefixEnd_592939 := by exact prefixLift 592939
  have htrace : WordTrace (prefixWord ++ tailWord_592939) baseStart_592939 baseEnd_592939 := by
    simpa [prefixWord, tailWord_592939, baseEnd_592939] using wordTrace_append hprefix tailTrace_592939
  have hstable : (prefixWord ++ tailWord_592939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592939).length < 2 ^ (prefixWord ++ tailWord_592939).sum := by decide
  have hdescent : baseEnd_592939 < baseStart_592939 := by decide
  rcases family_descends (prefixWord ++ tailWord_592939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592949 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 2, 5, 3]
def baseStart_592949 : Nat := 118140960795 + 592949 * 2 ^ 59
def prefixEnd_592949 : Nat := 4983230072969 + 3 ^ 40 * 592949 * 2
def baseEnd_592949 : Nat := 304467840602905818010583

theorem tailTrace_592949 : CollatzResearch.WordTrace tailWord_592949 prefixEnd_592949 304467840602905818010583 := by
  unfold tailWord_592949
  simp only [CollatzResearch.WordTrace]
  refine ⟨21626626728854515471981901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14417751152569676981321267 21626626728854515471981901)
  ·
    refine ⟨8109985023320443301993213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21626626728854515471981901 8109985023320443301993213)
    ·
      refine ⟨3041244383745166238247455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8109985023320443301993213 3041244383745166238247455)
      ·
        refine ⟨4561866575617749357371183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3041244383745166238247455 4561866575617749357371183)
        ·
          refine ⟨6842799863426624036056775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4561866575617749357371183 6842799863426624036056775)
          ·
            refine ⟨10264199795139936054085163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6842799863426624036056775 10264199795139936054085163)
            ·
              refine ⟨15396299692709904081127745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10264199795139936054085163 15396299692709904081127745)
              ·
                refine ⟨11547224769532428060845809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15396299692709904081127745 11547224769532428060845809)
                ·
                  refine ⟨8660418577149321045634357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11547224769532428060845809 8660418577149321045634357)
                  ·
                    refine ⟨811914241607748848028221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8660418577149321045634357 811914241607748848028221)
                    ·
                      refine ⟨304467840602905818010583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 811914241607748848028221 304467840602905818010583)
                      ·
                        rfl

theorem cell23_592949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_592949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592949 prefixEnd_592949 := by exact prefixLift 592949
  have htrace : WordTrace (prefixWord ++ tailWord_592949) baseStart_592949 baseEnd_592949 := by
    simpa [prefixWord, tailWord_592949, baseEnd_592949] using wordTrace_append hprefix tailTrace_592949
  have hstable : (prefixWord ++ tailWord_592949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592949).length < 2 ^ (prefixWord ++ tailWord_592949).sum := by decide
  have hdescent : baseEnd_592949 < baseStart_592949 := by decide
  rcases family_descends (prefixWord ++ tailWord_592949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592990 : List Nat := [4, 4, 1, 1, 1, 1, 3, 2, 6]
def baseStart_592990 : Nat := 118140960795 + 592990 * 2 ^ 59
def prefixEnd_592990 : Nat := 4983230072969 + 3 ^ 40 * 592990 * 2
def baseEnd_592990 : Nat := 33832099256637795288655

theorem tailTrace_592990 : CollatzResearch.WordTrace tailWord_592990 prefixEnd_592990 33832099256637795288655 := by
  unfold tailWord_592990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2703515265213247434278053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14418748081137319649482949 2703515265213247434278053)
  ·
    refine ⟨506909112227483893927135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2703515265213247434278053 506909112227483893927135)
    ·
      refine ⟨760363668341225840890703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 506909112227483893927135 760363668341225840890703)
      ·
        refine ⟨1140545502511838761336055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 760363668341225840890703 1140545502511838761336055)
        ·
          refine ⟨1710818253767758142004083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1140545502511838761336055 1710818253767758142004083)
          ·
            refine ⟨2566227380651637213006125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1710818253767758142004083 2566227380651637213006125)
            ·
              refine ⟨962335267744363954877297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2566227380651637213006125 962335267744363954877297)
              ·
                refine ⟨721751450808272966157973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 962335267744363954877297 721751450808272966157973)
                ·
                  refine ⟨33832099256637795288655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 721751450808272966157973 33832099256637795288655)
                  ·
                    rfl

theorem cell23_592990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_592990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_592990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_592990 prefixEnd_592990 := by exact prefixLift 592990
  have htrace : WordTrace (prefixWord ++ tailWord_592990) baseStart_592990 baseEnd_592990 := by
    simpa [prefixWord, tailWord_592990, baseEnd_592990] using wordTrace_append hprefix tailTrace_592990
  have hstable : (prefixWord ++ tailWord_592990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592990).length < 2 ^ (prefixWord ++ tailWord_592990).sum := by decide
  have hdescent : baseEnd_592990 < baseStart_592990 := by decide
  rcases family_descends (prefixWord ++ tailWord_592990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593009 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 2, 6, 3]
def baseStart_593009 : Nat := 118140960795 + 593009 * 2 ^ 59
def prefixEnd_593009 : Nat := 4983230072969 + 3 ^ 40 * 593009 * 2
def baseEnd_593009 : Nat := 304498649442175583260307

theorem tailTrace_593009 : CollatzResearch.WordTrace tailWord_593009 prefixEnd_593009 304498649442175583260307 := by
  unfold tailWord_593009
  simp only [CollatzResearch.WordTrace]
  refine ⟨21628815108637145719166081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14419210072424763812777387 21628815108637145719166081)
  ·
    refine ⟨16221611331477859289374561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21628815108637145719166081 16221611331477859289374561)
    ·
      refine ⟨12166208498608394467030921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16221611331477859289374561 12166208498608394467030921)
      ·
        refine ⟨9124656373956295850273191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12166208498608394467030921 9124656373956295850273191)
        ·
          refine ⟨13686984560934443775409787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9124656373956295850273191 13686984560934443775409787)
          ·
            refine ⟨20530476841401665663114681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13686984560934443775409787 20530476841401665663114681)
            ·
              refine ⟨15397857631051249247336011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20530476841401665663114681 15397857631051249247336011)
              ·
                refine ⟨23096786446576873871004017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15397857631051249247336011 23096786446576873871004017)
                ·
                  refine ⟨17322589834932655403253013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23096786446576873871004017 17322589834932655403253013)
                  ·
                    refine ⟨811996398512468222027485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17322589834932655403253013 811996398512468222027485)
                    ·
                      refine ⟨304498649442175583260307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 811996398512468222027485 304498649442175583260307)
                      ·
                        rfl

theorem cell23_593009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_593009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593009 prefixEnd_593009 := by exact prefixLift 593009
  have htrace : WordTrace (prefixWord ++ tailWord_593009) baseStart_593009 baseEnd_593009 := by
    simpa [prefixWord, tailWord_593009, baseEnd_593009] using wordTrace_append hprefix tailTrace_593009
  have hstable : (prefixWord ++ tailWord_593009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593009).length < 2 ^ (prefixWord ++ tailWord_593009).sum := by decide
  have hdescent : baseEnd_593009 < baseStart_593009 := by decide
  rcases family_descends (prefixWord ++ tailWord_593009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593016 : List Nat := [2, 1, 2, 1, 1, 1, 4, 5, 2, 4]
def baseStart_593016 : Nat := 118140960795 + 593016 * 2 ^ 59
def prefixEnd_593016 : Nat := 4983230072969 + 3 ^ 40 * 593016 * 2
def baseEnd_593016 : Nat := 101500747935585685290925

theorem tailTrace_593016 : CollatzResearch.WordTrace tailWord_593016 prefixEnd_593016 101500747935585685290925 := by
  unfold tailWord_593016
  simp only [CollatzResearch.WordTrace]
  refine ⟨10814535209805892957335451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14419380279741190609780601 10814535209805892957335451)
  ·
    refine ⟨16221802814708839436003177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10814535209805892957335451 16221802814708839436003177)
    ·
      refine ⟨12166352111031629577002383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16221802814708839436003177 12166352111031629577002383)
      ·
        refine ⟨18249528166547444365503575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12166352111031629577002383 18249528166547444365503575)
        ·
          refine ⟨27374292249821166548255363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18249528166547444365503575 27374292249821166548255363)
          ·
            refine ⟨41061438374731749822383045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27374292249821166548255363 41061438374731749822383045)
            ·
              refine ⟨7699019695262203091696821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41061438374731749822383045 7699019695262203091696821)
              ·
                refine ⟨721783096430831539846577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7699019695262203091696821 721783096430831539846577)
                ·
                  refine ⟨541337322323123654884933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 721783096430831539846577 541337322323123654884933)
                  ·
                    refine ⟨101500747935585685290925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 541337322323123654884933 101500747935585685290925)
                    ·
                      rfl

theorem cell23_593016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 2, 4].length) (baseStart_593016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593016 prefixEnd_593016 := by exact prefixLift 593016
  have htrace : WordTrace (prefixWord ++ tailWord_593016) baseStart_593016 baseEnd_593016 := by
    simpa [prefixWord, tailWord_593016, baseEnd_593016] using wordTrace_append hprefix tailTrace_593016
  have hstable : (prefixWord ++ tailWord_593016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593016).length < 2 ^ (prefixWord ++ tailWord_593016).sum := by decide
  have hdescent : baseEnd_593016 < baseStart_593016 := by decide
  rcases family_descends (prefixWord ++ tailWord_593016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593040 : List Nat := [2, 1, 1, 1, 1, 1, 4, 7, 1, 2, 2]
def baseStart_593040 : Nat := 118140960795 + 593040 * 2 ^ 59
def prefixEnd_593040 : Nat := 4983230072969 + 3 ^ 40 * 593040 * 2
def baseEnd_593040 : Nat := 304514567342464961972665

theorem tailTrace_593040 : CollatzResearch.WordTrace tailWord_593040 prefixEnd_593040 304514567342464961972665 := by
  unfold tailWord_593040
  simp only [CollatzResearch.WordTrace]
  refine ⟨10814972885762419006772287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14419963847683225342363049 10814972885762419006772287)
  ·
    refine ⟨16222459328643628510158431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10814972885762419006772287 16222459328643628510158431)
    ·
      refine ⟨24333688992965442765237647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16222459328643628510158431 24333688992965442765237647)
      ·
        refine ⟨36500533489448164147856471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24333688992965442765237647 36500533489448164147856471)
        ·
          refine ⟨54750800234172246221784707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36500533489448164147856471 54750800234172246221784707)
          ·
            refine ⟨82126200351258369332677061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54750800234172246221784707 82126200351258369332677061)
            ·
              refine ⟨15398662565860944249876949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82126200351258369332677061 15398662565860944249876949)
              ·
                refine ⟨360906153887365880856491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15398662565860944249876949 360906153887365880856491)
                ·
                  refine ⟨541359230831048821284737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 360906153887365880856491 541359230831048821284737)
                  ·
                    refine ⟨406019423123286615963553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 541359230831048821284737 406019423123286615963553)
                    ·
                      refine ⟨304514567342464961972665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 406019423123286615963553 304514567342464961972665)
                      ·
                        rfl

theorem cell23_593040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 1, 2, 2].length) (baseStart_593040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593040 prefixEnd_593040 := by exact prefixLift 593040
  have htrace : WordTrace (prefixWord ++ tailWord_593040) baseStart_593040 baseEnd_593040 := by
    simpa [prefixWord, tailWord_593040, baseEnd_593040] using wordTrace_append hprefix tailTrace_593040
  have hstable : (prefixWord ++ tailWord_593040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593040).length < 2 ^ (prefixWord ++ tailWord_593040).sum := by decide
  have hdescent : baseEnd_593040 < baseStart_593040 := by decide
  rcases family_descends (prefixWord ++ tailWord_593040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593083 : List Nat := [1, 1, 1, 1, 1, 2, 4, 6, 1, 3, 2]
def baseStart_593083 : Nat := 118140960795 + 593083 * 2 ^ 59
def prefixEnd_593083 : Nat := 4983230072969 + 3 ^ 40 * 593083 * 2
def baseEnd_593083 : Nat := 304536647010608293734967

theorem tailTrace_593083 : CollatzResearch.WordTrace tailWord_593083 prefixEnd_593083 304536647010608293734967 := by
  unfold tailWord_593083
  simp only [CollatzResearch.WordTrace]
  refine ⟨21631514110369056357359903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14421009406912704238239935 21631514110369056357359903)
  ·
    refine ⟨32447271165553584536039855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21631514110369056357359903 32447271165553584536039855)
    ·
      refine ⟨48670906748330376804059783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32447271165553584536039855 48670906748330376804059783)
      ·
        refine ⟨73006360122495565206089675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48670906748330376804059783 73006360122495565206089675)
        ·
          refine ⟨109509540183743347809134513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73006360122495565206089675 109509540183743347809134513)
          ·
            refine ⟨82132155137807510856850885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109509540183743347809134513 82132155137807510856850885)
            ·
              refine ⟨15399779088338908285659541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82132155137807510856850885 15399779088338908285659541)
              ·
                refine ⟨721864644765886325890291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15399779088338908285659541 721864644765886325890291)
                ·
                  refine ⟨1082796967148829488835437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 721864644765886325890291 1082796967148829488835437)
                  ·
                    refine ⟨406048862680811058313289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1082796967148829488835437 406048862680811058313289)
                    ·
                      refine ⟨304536647010608293734967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 406048862680811058313289 304536647010608293734967)
                      ·
                        rfl

theorem cell23_593083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 3, 2].length) (baseStart_593083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593083 prefixEnd_593083 := by exact prefixLift 593083
  have htrace : WordTrace (prefixWord ++ tailWord_593083) baseStart_593083 baseEnd_593083 := by
    simpa [prefixWord, tailWord_593083, baseEnd_593083] using wordTrace_append hprefix tailTrace_593083
  have hstable : (prefixWord ++ tailWord_593083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593083).length < 2 ^ (prefixWord ++ tailWord_593083).sum := by decide
  have hdescent : baseEnd_593083 < baseStart_593083 := by decide
  rcases family_descends (prefixWord ++ tailWord_593083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593094 : List Nat := [6, 1, 2, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_593094 : Nat := 118140960795 + 593094 * 2 ^ 59
def prefixEnd_593094 : Nat := 4983230072969 + 3 ^ 40 * 593094 * 2
def baseEnd_593094 : Nat := 304542295297807750697417

theorem tailTrace_593094 : CollatzResearch.WordTrace tailWord_593094 prefixEnd_593094 304542295297807750697417 := by
  unfold tailWord_593094
  simp only [CollatzResearch.WordTrace]
  refine ⟨675997353541537663625323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14421276875552803490673557 675997353541537663625323)
  ·
    refine ⟨1013996030312306495437985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 675997353541537663625323 1013996030312306495437985)
    ·
      refine ⟨760497022734229871578489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1013996030312306495437985 760497022734229871578489)
      ·
        refine ⟨570372767050672403683867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 760497022734229871578489 570372767050672403683867)
        ·
          refine ⟨855559150576008605525801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570372767050672403683867 855559150576008605525801)
          ·
            refine ⟨641669362932006454144351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 855559150576008605525801 641669362932006454144351)
            ·
              refine ⟨962504044398009681216527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 641669362932006454144351 962504044398009681216527)
              ·
                refine ⟨1443756066597014521824791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 962504044398009681216527 1443756066597014521824791)
                ·
                  refine ⟨2165634099895521782737187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1443756066597014521824791 2165634099895521782737187)
                  ·
                    refine ⟨3248451149843282674105781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2165634099895521782737187 3248451149843282674105781)
                    ·
                      refine ⟨304542295297807750697417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3248451149843282674105781 304542295297807750697417)
                      ·
                        rfl

theorem cell23_593094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_593094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593094 prefixEnd_593094 := by exact prefixLift 593094
  have htrace : WordTrace (prefixWord ++ tailWord_593094) baseStart_593094 baseEnd_593094 := by
    simpa [prefixWord, tailWord_593094, baseEnd_593094] using wordTrace_append hprefix tailTrace_593094
  have hstable : (prefixWord ++ tailWord_593094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593094).length < 2 ^ (prefixWord ++ tailWord_593094).sum := by decide
  have hdescent : baseEnd_593094 < baseStart_593094 := by decide
  rcases family_descends (prefixWord ++ tailWord_593094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593099 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 5]
def baseStart_593099 : Nat := 118140960795 + 593099 * 2 ^ 59
def prefixEnd_593099 : Nat := 4983230072969 + 3 ^ 40 * 593099 * 2
def baseEnd_593099 : Nat := 304544862701080231134893

theorem tailTrace_593099 : CollatzResearch.WordTrace tailWord_593099 prefixEnd_593099 304544862701080231134893 := by
  unfold tailWord_593099
  simp only [CollatzResearch.WordTrace]
  refine ⟨21632097678311091089942351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14421398452207394059961567 21632097678311091089942351)
  ·
    refine ⟨32448146517466636634913527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21632097678311091089942351 32448146517466636634913527)
    ·
      refine ⟨48672219776199954952370291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32448146517466636634913527 48672219776199954952370291)
      ·
        refine ⟨73008329664299932428555437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48672219776199954952370291 73008329664299932428555437)
        ·
          refine ⟨27378123624112474660708289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73008329664299932428555437 27378123624112474660708289)
          ·
            refine ⟨20533592718084355995531217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27378123624112474660708289 20533592718084355995531217)
            ·
              refine ⟨15400194538563266996648413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20533592718084355995531217 15400194538563266996648413)
              ·
                refine ⟨5775072951961225123743155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15400194538563266996648413 5775072951961225123743155)
                ·
                  refine ⟨8662609427941837685614733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5775072951961225123743155 8662609427941837685614733)
                  ·
                    refine ⟨3248478535478189132105525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8662609427941837685614733 3248478535478189132105525)
                    ·
                      refine ⟨304544862701080231134893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3248478535478189132105525 304544862701080231134893)
                      ·
                        rfl

theorem cell23_593099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 5].length) (baseStart_593099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593099 prefixEnd_593099 := by exact prefixLift 593099
  have htrace : WordTrace (prefixWord ++ tailWord_593099) baseStart_593099 baseEnd_593099 := by
    simpa [prefixWord, tailWord_593099, baseEnd_593099] using wordTrace_append hprefix tailTrace_593099
  have hstable : (prefixWord ++ tailWord_593099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593099).length < 2 ^ (prefixWord ++ tailWord_593099).sum := by decide
  have hdescent : baseEnd_593099 < baseStart_593099 := by decide
  rcases family_descends (prefixWord ++ tailWord_593099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593106 : List Nat := [3, 2, 2, 2, 1, 1, 2, 2, 2, 6]
def baseStart_593106 : Nat := 118140960795 + 593106 * 2 ^ 59
def prefixEnd_593106 : Nat := 4983230072969 + 3 ^ 40 * 593106 * 2
def baseEnd_593106 : Nat := 101516152355220567915787

theorem tailTrace_593106 : CollatzResearch.WordTrace tailWord_593106 prefixEnd_593106 101516152355220567915787 := by
  unfold tailWord_593106
  simp only [CollatzResearch.WordTrace]
  refine ⟨5408088247321432821361793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14421568659523820856964781 5408088247321432821361793)
  ·
    refine ⟨4056066185491074616021345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5408088247321432821361793 4056066185491074616021345)
    ·
      refine ⟨3042049639118305962016009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4056066185491074616021345 3042049639118305962016009)
      ·
        refine ⟨2281537229338729471512007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3042049639118305962016009 2281537229338729471512007)
        ·
          refine ⟨3422305844008094207268011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2281537229338729471512007 3422305844008094207268011)
          ·
            refine ⟨5133458766012141310902017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3422305844008094207268011 5133458766012141310902017)
            ·
              refine ⟨3850094074509105983176513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5133458766012141310902017 3850094074509105983176513)
              ·
                refine ⟨2887570555881829487382385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3850094074509105983176513 2887570555881829487382385)
                ·
                  refine ⟨2165677916911372115536789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2887570555881829487382385 2165677916911372115536789)
                  ·
                    refine ⟨101516152355220567915787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2165677916911372115536789 101516152355220567915787)
                    ·
                      rfl

theorem cell23_593106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_593106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593106 prefixEnd_593106 := by exact prefixLift 593106
  have htrace : WordTrace (prefixWord ++ tailWord_593106) baseStart_593106 baseEnd_593106 := by
    simpa [prefixWord, tailWord_593106, baseEnd_593106] using wordTrace_append hprefix tailTrace_593106
  have hstable : (prefixWord ++ tailWord_593106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593106).length < 2 ^ (prefixWord ++ tailWord_593106).sum := by decide
  have hdescent : baseEnd_593106 < baseStart_593106 := by decide
  rcases family_descends (prefixWord ++ tailWord_593106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593108 : List Nat := [2, 4, 1, 4, 1, 2, 2, 2, 1, 2, 2]
def baseStart_593108 : Nat := 118140960795 + 593108 * 2 ^ 59
def prefixEnd_593108 : Nat := 4983230072969 + 3 ^ 40 * 593108 * 2
def baseEnd_593108 : Nat := 304549484026970695922353

theorem tailTrace_593108 : CollatzResearch.WordTrace tailWord_593108 prefixEnd_593108 304549484026970695922353 := by
  unfold tailWord_593108
  simp only [CollatzResearch.WordTrace]
  refine ⟨10816212967639242813509989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14421617290185657084679985 10816212967639242813509989)
  ·
    refine ⟨2028039931432358027533123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10816212967639242813509989 2028039931432358027533123)
    ·
      refine ⟨3042059897148537041299685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2028039931432358027533123 3042059897148537041299685)
      ·
        refine ⟨570386230715350695243691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3042059897148537041299685 570386230715350695243691)
        ·
          refine ⟨855579346073026042865537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570386230715350695243691 855579346073026042865537)
          ·
            refine ⟨641684509554769532149153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 855579346073026042865537 641684509554769532149153)
            ·
              refine ⟨481263382166077149111865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 641684509554769532149153 481263382166077149111865)
              ·
                refine ⟨360947536624557861833899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 481263382166077149111865 360947536624557861833899)
                ·
                  refine ⟨541421304936836792750849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 360947536624557861833899 541421304936836792750849)
                  ·
                    refine ⟨406065978702627594563137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 541421304936836792750849 406065978702627594563137)
                    ·
                      refine ⟨304549484026970695922353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 406065978702627594563137 304549484026970695922353)
                      ·
                        rfl

theorem cell23_593108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_593108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593108 prefixEnd_593108 := by exact prefixLift 593108
  have htrace : WordTrace (prefixWord ++ tailWord_593108) baseStart_593108 baseEnd_593108 := by
    simpa [prefixWord, tailWord_593108, baseEnd_593108] using wordTrace_append hprefix tailTrace_593108
  have hstable : (prefixWord ++ tailWord_593108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593108).length < 2 ^ (prefixWord ++ tailWord_593108).sum := by decide
  have hdescent : baseEnd_593108 < baseStart_593108 := by decide
  rcases family_descends (prefixWord ++ tailWord_593108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593130 : List Nat := [3, 1, 3, 1, 1, 4, 2, 1, 1, 4, 2]
def baseStart_593130 : Nat := 118140960795 + 593130 * 2 ^ 59
def prefixEnd_593130 : Nat := 4983230072969 + 3 ^ 40 * 593130 * 2
def baseEnd_593130 : Nat := 304560780601369609847251

theorem tailTrace_593130 : CollatzResearch.WordTrace tailWord_593130 prefixEnd_593130 304560780601369609847251 := by
  unfold tailWord_593130
  simp only [CollatzResearch.WordTrace]
  refine ⟨5408307085299695846080211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14422152227465855589547229 5408307085299695846080211)
  ·
    refine ⟨8112460627949543769120317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5408307085299695846080211 8112460627949543769120317)
    ·
      refine ⟨3042172735481078913420119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8112460627949543769120317 3042172735481078913420119)
      ·
        refine ⟨4563259103221618370130179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3042172735481078913420119 4563259103221618370130179)
        ·
          refine ⟨6844888654832427555195269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4563259103221618370130179 6844888654832427555195269)
          ·
            refine ⟨1283416622781080166599113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6844888654832427555195269 1283416622781080166599113)
            ·
              refine ⟨962562467085810124949335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1283416622781080166599113 962562467085810124949335)
              ·
                refine ⟨1443843700628715187424003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 962562467085810124949335 1443843700628715187424003)
                ·
                  refine ⟨2165765550943072781136005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1443843700628715187424003 2165765550943072781136005)
                  ·
                    refine ⟨406081040801826146463001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2165765550943072781136005 406081040801826146463001)
                    ·
                      refine ⟨304560780601369609847251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 406081040801826146463001 304560780601369609847251)
                      ·
                        rfl

theorem cell23_593130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_593130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593130 prefixEnd_593130 := by exact prefixLift 593130
  have htrace : WordTrace (prefixWord ++ tailWord_593130) baseStart_593130 baseEnd_593130 := by
    simpa [prefixWord, tailWord_593130, baseEnd_593130] using wordTrace_append hprefix tailTrace_593130
  have hstable : (prefixWord ++ tailWord_593130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593130).length < 2 ^ (prefixWord ++ tailWord_593130).sum := by decide
  have hdescent : baseEnd_593130 < baseStart_593130 := by decide
  rcases family_descends (prefixWord ++ tailWord_593130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593146 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3]
def baseStart_593146 : Nat := 118140960795 + 593146 * 2 ^ 59
def prefixEnd_593146 : Nat := 4983230072969 + 3 ^ 40 * 593146 * 2
def baseEnd_593146 : Nat := 304568996291841547247177

theorem tailTrace_593146 : CollatzResearch.WordTrace tailWord_593146 prefixEnd_593146 304568996291841547247177 := by
  unfold tailWord_593146
  simp only [CollatzResearch.WordTrace]
  refine ⟨5408452977285204529225823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14422541272760545411268861 5408452977285204529225823)
  ·
    refine ⟨8112679465927806793838735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5408452977285204529225823 8112679465927806793838735)
    ·
      refine ⟨12169019198891710190758103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8112679465927806793838735 12169019198891710190758103)
      ·
        refine ⟨18253528798337565286137155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12169019198891710190758103 18253528798337565286137155)
        ·
          refine ⟨27380293197506347929205733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18253528798337565286137155 27380293197506347929205733)
          ·
            refine ⟨5133804974532440236726075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27380293197506347929205733 5133804974532440236726075)
            ·
              refine ⟨7700707461798660355089113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5133804974532440236726075 7700707461798660355089113)
              ·
                refine ⟨5775530596348995266316835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7700707461798660355089113 5775530596348995266316835)
                ·
                  refine ⟨8663295894523492899475253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5775530596348995266316835 8663295894523492899475253)
                  ·
                    refine ⟨812183990111577459325805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8663295894523492899475253 812183990111577459325805)
                    ·
                      refine ⟨304568996291841547247177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 812183990111577459325805 304568996291841547247177)
                      ·
                        rfl

theorem cell23_593146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3].length) (baseStart_593146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593146 prefixEnd_593146 := by exact prefixLift 593146
  have htrace : WordTrace (prefixWord ++ tailWord_593146) baseStart_593146 baseEnd_593146 := by
    simpa [prefixWord, tailWord_593146, baseEnd_593146] using wordTrace_append hprefix tailTrace_593146
  have hstable : (prefixWord ++ tailWord_593146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593146).length < 2 ^ (prefixWord ++ tailWord_593146).sum := by decide
  have hdescent : baseEnd_593146 < baseStart_593146 := by decide
  rcases family_descends (prefixWord ++ tailWord_593146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593153 : List Nat := [1, 2, 4, 1, 1, 3, 1, 5, 5]
def baseStart_593153 : Nat := 118140960795 + 593153 * 2 ^ 59
def prefixEnd_593153 : Nat := 4983230072969 + 3 ^ 40 * 593153 * 2
def baseEnd_593153 : Nat := 33841398961824779984405

theorem tailTrace_593153 : CollatzResearch.WordTrace tailWord_593153 prefixEnd_593153 33841398961824779984405 := by
  unfold tailWord_593153
  simp only [CollatzResearch.WordTrace]
  refine ⟨21634067220115458312408113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14422711480076972208272075 21634067220115458312408113)
  ·
    refine ⟨16225550415086593734306085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21634067220115458312408113 16225550415086593734306085)
    ·
      refine ⟨3042290702828736325182391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16225550415086593734306085 3042290702828736325182391)
      ·
        refine ⟨4563436054243104487773587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3042290702828736325182391 4563436054243104487773587)
        ·
          refine ⟨6845154081364656731660381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4563436054243104487773587 6845154081364656731660381)
          ·
            refine ⟨2566932780511746274372643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6845154081364656731660381 2566932780511746274372643)
            ·
              refine ⟨3850399170767619411558965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2566932780511746274372643 3850399170767619411558965)
              ·
                refine ⟨360974922259464319833653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3850399170767619411558965 360974922259464319833653)
                ·
                  refine ⟨33841398961824779984405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 360974922259464319833653 33841398961824779984405)
                  ·
                    rfl

theorem cell23_593153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 5].length) (baseStart_593153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593153 prefixEnd_593153 := by exact prefixLift 593153
  have htrace : WordTrace (prefixWord ++ tailWord_593153) baseStart_593153 baseEnd_593153 := by
    simpa [prefixWord, tailWord_593153, baseEnd_593153] using wordTrace_append hprefix tailTrace_593153
  have hstable : (prefixWord ++ tailWord_593153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593153).length < 2 ^ (prefixWord ++ tailWord_593153).sum := by decide
  have hdescent : baseEnd_593153 < baseStart_593153 := by decide
  rcases family_descends (prefixWord ++ tailWord_593153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593220 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_593220 : Nat := 118140960795 + 593220 * 2 ^ 59
def prefixEnd_593220 : Nat := 4983230072969 + 3 ^ 40 * 593220 * 2
def baseEnd_593220 : Nat := 304606993860274257721837

theorem tailTrace_593220 : CollatzResearch.WordTrace tailWord_593220 prefixEnd_593220 304606993860274257721837 := by
  unfold tailWord_593220
  simp only [CollatzResearch.WordTrace]
  refine ⟨10818255455436364377548557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14424340607248485836731409 10818255455436364377548557)
  ·
    refine ⟨4056845795788636641580709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10818255455436364377548557 4056845795788636641580709)
    ·
      refine ⟨760658586710369370296383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4056845795788636641580709 760658586710369370296383)
      ·
        refine ⟨1140987880065554055444575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 760658586710369370296383 1140987880065554055444575)
        ·
          refine ⟨1711481820098331083166863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1140987880065554055444575 1711481820098331083166863)
          ·
            refine ⟨2567222730147496624750295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1711481820098331083166863 2567222730147496624750295)
            ·
              refine ⟨3850834095221244937125443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2567222730147496624750295 3850834095221244937125443)
              ·
                refine ⟨5776251142831867405688165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3850834095221244937125443 5776251142831867405688165)
                ·
                  refine ⟨1083047089280975138566531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5776251142831867405688165 1083047089280975138566531)
                  ·
                    refine ⟨1624570633921462707849797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1083047089280975138566531 1624570633921462707849797)
                    ·
                      refine ⟨304606993860274257721837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1624570633921462707849797 304606993860274257721837)
                      ·
                        rfl

theorem cell23_593220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_593220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593220 prefixEnd_593220 := by exact prefixLift 593220
  have htrace : WordTrace (prefixWord ++ tailWord_593220) baseStart_593220 baseEnd_593220 := by
    simpa [prefixWord, tailWord_593220, baseEnd_593220] using wordTrace_append hprefix tailTrace_593220
  have hstable : (prefixWord ++ tailWord_593220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593220).length < 2 ^ (prefixWord ++ tailWord_593220).sum := by decide
  have hdescent : baseEnd_593220 < baseStart_593220 := by decide
  rcases family_descends (prefixWord ++ tailWord_593220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593223 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 3]
def baseStart_593223 : Nat := 118140960795 + 593223 * 2 ^ 59
def prefixEnd_593223 : Nat := 4983230072969 + 3 ^ 40 * 593223 * 2
def baseEnd_593223 : Nat := 304608534302237745984323

theorem tailTrace_593223 : CollatzResearch.WordTrace tailWord_593223 prefixEnd_593223 304608534302237745984323 := by
  unfold tailWord_593223
  simp only [CollatzResearch.WordTrace]
  refine ⟨21636620329861860267456323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14424413553241240178304215 21636620329861860267456323)
  ·
    refine ⟨32454930494792790401184485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21636620329861860267456323 32454930494792790401184485)
    ·
      refine ⟨6085299467773648200222091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32454930494792790401184485 6085299467773648200222091)
      ·
        refine ⟨9127949201660472300333137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6085299467773648200222091 9127949201660472300333137)
        ·
          refine ⟨6845961901245354225249853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9127949201660472300333137 6845961901245354225249853)
          ·
            refine ⟨2567235712967007834468695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6845961901245354225249853 2567235712967007834468695)
            ·
              refine ⟨3850853569450511751703043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2567235712967007834468695 3850853569450511751703043)
              ·
                refine ⟨5776280354175767627554565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3850853569450511751703043 5776280354175767627554565)
                ·
                  refine ⟨1083052566407956430166481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5776280354175767627554565 1083052566407956430166481)
                  ·
                    refine ⟨812289424805967322624861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1083052566407956430166481 812289424805967322624861)
                    ·
                      refine ⟨304608534302237745984323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 812289424805967322624861 304608534302237745984323)
                      ·
                        rfl

theorem cell23_593223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_593223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593223 prefixEnd_593223 := by exact prefixLift 593223
  have htrace : WordTrace (prefixWord ++ tailWord_593223) baseStart_593223 baseEnd_593223 := by
    simpa [prefixWord, tailWord_593223, baseEnd_593223] using wordTrace_append hprefix tailTrace_593223
  have hstable : (prefixWord ++ tailWord_593223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593223).length < 2 ^ (prefixWord ++ tailWord_593223).sum := by decide
  have hdescent : baseEnd_593223 < baseStart_593223 := by decide
  rcases family_descends (prefixWord ++ tailWord_593223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593273 : List Nat := [1, 2, 1, 3, 2, 1, 2, 5, 1, 5]
def baseStart_593273 : Nat := 118140960795 + 593273 * 2 ^ 59
def prefixEnd_593273 : Nat := 4983230072969 + 3 ^ 40 * 593273 * 2
def baseEnd_593273 : Nat := 101544736111654183453031

theorem tailTrace_593273 : CollatzResearch.WordTrace tailWord_593273 prefixEnd_593273 101544736111654183453031 := by
  unfold tailWord_593273
  simp only [CollatzResearch.WordTrace]
  refine ⟨21638443979680718806776473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14425629319787145871184315 21638443979680718806776473)
  ·
    refine ⟨16228832984760539105082355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21638443979680718806776473 16228832984760539105082355)
    ·
      refine ⟨24343249477140808657623533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16228832984760539105082355 24343249477140808657623533)
      ·
        refine ⟨9128718553927803246608825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24343249477140808657623533 9128718553927803246608825)
        ·
          refine ⟨6846538915445852434956619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9128718553927803246608825 6846538915445852434956619)
          ·
            refine ⟨10269808373168778652434929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6846538915445852434956619 10269808373168778652434929)
            ·
              refine ⟨7702356279876583989326197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10269808373168778652434929 7702356279876583989326197)
              ·
                refine ⟨722095901238429748999331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7702356279876583989326197 722095901238429748999331)
                ·
                  refine ⟨1083143851857644623498997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 722095901238429748999331 1083143851857644623498997)
                  ·
                    refine ⟨101544736111654183453031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1083143851857644623498997 101544736111654183453031)
                    ·
                      rfl

theorem cell23_593273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 5].length) (baseStart_593273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593273 prefixEnd_593273 := by exact prefixLift 593273
  have htrace : WordTrace (prefixWord ++ tailWord_593273) baseStart_593273 baseEnd_593273 := by
    simpa [prefixWord, tailWord_593273, baseEnd_593273] using wordTrace_append hprefix tailTrace_593273
  have hstable : (prefixWord ++ tailWord_593273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593273).length < 2 ^ (prefixWord ++ tailWord_593273).sum := by decide
  have hdescent : baseEnd_593273 < baseStart_593273 := by decide
  rcases family_descends (prefixWord ++ tailWord_593273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593281 : List Nat := [1, 2, 4, 3, 2, 2, 2, 2, 1, 4]
def baseStart_593281 : Nat := 118140960795 + 593281 * 2 ^ 59
def prefixEnd_593281 : Nat := 4983230072969 + 3 ^ 40 * 593281 * 2
def baseEnd_593281 : Nat := 101546105393399506353019

theorem tailTrace_593281 : CollatzResearch.WordTrace tailWord_593281 prefixEnd_593281 101546105393399506353019 := by
  unfold tailWord_593281
  simp only [CollatzResearch.WordTrace]
  refine ⟨21638735763651736173067697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14425823842434490782045131 21638735763651736173067697)
  ·
    refine ⟨16229051822738802129800773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21638735763651736173067697 16229051822738802129800773)
    ·
      refine ⟨3042947216763525399337645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16229051822738802129800773 3042947216763525399337645)
      ·
        refine ⟨1141105206286322024751617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3042947216763525399337645 1141105206286322024751617)
        ·
          refine ⟨855828904714741518563713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1141105206286322024751617 855828904714741518563713)
          ·
            refine ⟨641871678536056138922785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 855828904714741518563713 641871678536056138922785)
            ·
              refine ⟨481403758902042104192089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 641871678536056138922785 481403758902042104192089)
              ·
                refine ⟨361052819176531578144067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 481403758902042104192089 361052819176531578144067)
                ·
                  refine ⟨541579228764797367216101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 361052819176531578144067 541579228764797367216101)
                  ·
                    refine ⟨101546105393399506353019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 541579228764797367216101 101546105393399506353019)
                    ·
                      rfl

theorem cell23_593281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_593281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593281 prefixEnd_593281 := by exact prefixLift 593281
  have htrace : WordTrace (prefixWord ++ tailWord_593281) baseStart_593281 baseEnd_593281 := by
    simpa [prefixWord, tailWord_593281, baseEnd_593281] using wordTrace_append hprefix tailTrace_593281
  have hstable : (prefixWord ++ tailWord_593281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593281).length < 2 ^ (prefixWord ++ tailWord_593281).sum := by decide
  have hdescent : baseEnd_593281 < baseStart_593281 := by decide
  rcases family_descends (prefixWord ++ tailWord_593281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593303 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 6, 4]
def baseStart_593303 : Nat := 118140960795 + 593303 * 2 ^ 59
def prefixEnd_593303 : Nat := 4983230072969 + 3 ^ 40 * 593303 * 2
def baseEnd_593303 : Nat := 101549870918199144327985

theorem tailTrace_593303 : CollatzResearch.WordTrace tailWord_593303 prefixEnd_593303 101549870918199144327985 := by
  unfold tailWord_593303
  simp only [CollatzResearch.WordTrace]
  refine ⟨21639538169572033930368563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14426358779714689286912375 21639538169572033930368563)
  ·
    refine ⟨32459307254358050895552845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21639538169572033930368563 32459307254358050895552845)
    ·
      refine ⟨12172240220384269085832317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32459307254358050895552845 12172240220384269085832317)
      ·
        refine ⟨4564590082644100907187119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12172240220384269085832317 4564590082644100907187119)
        ·
          refine ⟨6846885123966151360780679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4564590082644100907187119 6846885123966151360780679)
          ·
            refine ⟨10270327685949227041171019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6846885123966151360780679 10270327685949227041171019)
            ·
              refine ⟨15405491528923840561756529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10270327685949227041171019 15405491528923840561756529)
              ·
                refine ⟨11554118646692880421317397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15405491528923840561756529 11554118646692880421317397)
                ·
                  refine ⟨541599311563728769749253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11554118646692880421317397 541599311563728769749253)
                  ·
                    refine ⟨101549870918199144327985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 541599311563728769749253 101549870918199144327985)
                    ·
                      rfl

theorem cell23_593303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 4].length) (baseStart_593303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593303 prefixEnd_593303 := by exact prefixLift 593303
  have htrace : WordTrace (prefixWord ++ tailWord_593303) baseStart_593303 baseEnd_593303 := by
    simpa [prefixWord, tailWord_593303, baseEnd_593303] using wordTrace_append hprefix tailTrace_593303
  have hstable : (prefixWord ++ tailWord_593303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593303).length < 2 ^ (prefixWord ++ tailWord_593303).sum := by decide
  have hdescent : baseEnd_593303 < baseStart_593303 := by decide
  rcases family_descends (prefixWord ++ tailWord_593303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593314 : List Nat := [3, 3, 1, 2, 1, 4, 1, 1, 2, 3, 2]
def baseStart_593314 : Nat := 118140960795 + 593314 * 2 ^ 59
def prefixEnd_593314 : Nat := 4983230072969 + 3 ^ 40 * 593314 * 2
def baseEnd_593314 : Nat := 304655261041796889946405

theorem tailTrace_593314 : CollatzResearch.WordTrace tailWord_593314 prefixEnd_593314 304655261041796889946405 := by
  unfold tailWord_593314
  simp only [CollatzResearch.WordTrace]
  refine ⟨5409984843133045702254749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14426626248354788539345997 5409984843133045702254749)
  ·
    refine ⟨2028744316174892138345531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5409984843133045702254749 2028744316174892138345531)
    ·
      refine ⟨3043116474262338207518297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2028744316174892138345531 3043116474262338207518297)
      ·
        refine ⟨2282337355696753655638723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3043116474262338207518297 2282337355696753655638723)
        ·
          refine ⟨3423506033545130483458085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2282337355696753655638723 3423506033545130483458085)
          ·
            refine ⟨641907381289711965648391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3423506033545130483458085 641907381289711965648391)
            ·
              refine ⟨962861071934567948472587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 641907381289711965648391 962861071934567948472587)
              ·
                refine ⟨1444291607901851922708881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 962861071934567948472587 1444291607901851922708881)
                ·
                  refine ⟨1083218705926388942031661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1444291607901851922708881 1083218705926388942031661)
                  ·
                    refine ⟨406207014722395853261873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1083218705926388942031661 406207014722395853261873)
                    ·
                      refine ⟨304655261041796889946405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 406207014722395853261873 304655261041796889946405)
                      ·
                        rfl

theorem cell23_593314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_593314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593314 prefixEnd_593314 := by exact prefixLift 593314
  have htrace : WordTrace (prefixWord ++ tailWord_593314) baseStart_593314 baseEnd_593314 := by
    simpa [prefixWord, tailWord_593314, baseEnd_593314] using wordTrace_append hprefix tailTrace_593314
  have hstable : (prefixWord ++ tailWord_593314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593314).length < 2 ^ (prefixWord ++ tailWord_593314).sum := by decide
  have hdescent : baseEnd_593314 < baseStart_593314 := by decide
  rcases family_descends (prefixWord ++ tailWord_593314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593333 : List Nat := [1, 3, 3, 2, 2, 2, 10]
def baseStart_593333 : Nat := 118140960795 + 593333 * 2 ^ 59
def prefixEnd_593333 : Nat := 4983230072969 + 3 ^ 40 * 593333 * 2
def baseEnd_593333 : Nat := 3761296508323855748257

theorem tailTrace_593333 : CollatzResearch.WordTrace tailWord_593333 prefixEnd_593333 3761296508323855748257 := by
  unfold tailWord_593333
  simp only [CollatzResearch.WordTrace]
  refine ⟨21640632359463349053960653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14427088239642232702640435 21640632359463349053960653)
  ·
    refine ⟨8115237134798755895235245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21640632359463349053960653 8115237134798755895235245)
    ·
      refine ⟨3043213925549533460713217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8115237134798755895235245 3043213925549533460713217)
      ·
        refine ⟨2282410444162150095534913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3043213925549533460713217 2282410444162150095534913)
        ·
          refine ⟨1711807833121612571651185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2282410444162150095534913 1711807833121612571651185)
          ·
            refine ⟨1283855874841209428738389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1711807833121612571651185 1283855874841209428738389)
            ·
              refine ⟨3761296508323855748257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1283855874841209428738389 3761296508323855748257)
              ·
                rfl

theorem cell23_593333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 10].length) (baseStart_593333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593333 prefixEnd_593333 := by exact prefixLift 593333
  have htrace : WordTrace (prefixWord ++ tailWord_593333) baseStart_593333 baseEnd_593333 := by
    simpa [prefixWord, tailWord_593333, baseEnd_593333] using wordTrace_append hprefix tailTrace_593333
  have hstable : (prefixWord ++ tailWord_593333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593333).length < 2 ^ (prefixWord ++ tailWord_593333).sum := by decide
  have hdescent : baseEnd_593333 < baseStart_593333 := by decide
  rcases family_descends (prefixWord ++ tailWord_593333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593343 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 3]
def baseStart_593343 : Nat := 118140960795 + 593343 * 2 ^ 59
def prefixEnd_593343 : Nat := 4983230072969 + 3 ^ 40 * 593343 * 2
def baseEnd_593343 : Nat := 304670151980777276483771

theorem tailTrace_593343 : CollatzResearch.WordTrace tailWord_593343 prefixEnd_593343 304670151980777276483771 := by
  unfold tailWord_593343
  simp only [CollatzResearch.WordTrace]
  refine ⟨21640997089427120761824683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14427331392951413841216455 21640997089427120761824683)
  ·
    refine ⟨32461495634140681142737025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21640997089427120761824683 32461495634140681142737025)
    ·
      refine ⟨24346121725605510857052769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32461495634140681142737025 24346121725605510857052769)
      ·
        refine ⟨18259591294204133142789577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24346121725605510857052769 18259591294204133142789577)
        ·
          refine ⟨13694693470653099857092183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18259591294204133142789577 13694693470653099857092183)
          ·
            refine ⟨20542040205979649785638275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13694693470653099857092183 20542040205979649785638275)
            ·
              refine ⟨30813060308969474678457413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20542040205979649785638275 30813060308969474678457413)
              ·
                refine ⟨5777448807931776502210765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30813060308969474678457413 5777448807931776502210765)
                ·
                  refine ⟨2166543302974416188329037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5777448807931776502210765 2166543302974416188329037)
                  ·
                    refine ⟨812453738615406070623389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2166543302974416188329037 812453738615406070623389)
                    ·
                      refine ⟨304670151980777276483771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 812453738615406070623389 304670151980777276483771)
                      ·
                        rfl

theorem cell23_593343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 3].length) (baseStart_593343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593343 prefixEnd_593343 := by exact prefixLift 593343
  have htrace : WordTrace (prefixWord ++ tailWord_593343) baseStart_593343 baseEnd_593343 := by
    simpa [prefixWord, tailWord_593343, baseEnd_593343] using wordTrace_append hprefix tailTrace_593343
  have hstable : (prefixWord ++ tailWord_593343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593343).length < 2 ^ (prefixWord ++ tailWord_593343).sum := by decide
  have hdescent : baseEnd_593343 < baseStart_593343 := by decide
  rcases family_descends (prefixWord ++ tailWord_593343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593344 : List Nat := [2, 1, 1, 2, 3, 1, 4, 4, 1, 2, 2]
def baseStart_593344 : Nat := 118140960795 + 593344 * 2 ^ 59
def prefixEnd_593344 : Nat := 4983230072969 + 3 ^ 40 * 593344 * 2
def baseEnd_593344 : Nat := 304670665461431772571267

theorem tailTrace_593344 : CollatzResearch.WordTrace tailWord_593344 prefixEnd_593344 304670665461431772571267 := by
  unfold tailWord_593344
  simp only [CollatzResearch.WordTrace]
  refine ⟨10820516781211748966305543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14427355708282331955074057 10820516781211748966305543)
  ·
    refine ⟨16230775171817623449458315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10820516781211748966305543 16230775171817623449458315)
    ·
      refine ⟨24346162757726435174187473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16230775171817623449458315 24346162757726435174187473)
      ·
        refine ⟨18259622068294826380640605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24346162757726435174187473 18259622068294826380640605)
        ·
          refine ⟨6847358275610559892740227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18259622068294826380640605 6847358275610559892740227)
          ·
            refine ⟨10271037413415839839110341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6847358275610559892740227 10271037413415839839110341)
            ·
              refine ⟨1925819515015469969833189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10271037413415839839110341 1925819515015469969833189)
              ·
                refine ⟨361091159065400619343723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1925819515015469969833189 361091159065400619343723)
                ·
                  refine ⟨541636738598100929015585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 361091159065400619343723 541636738598100929015585)
                  ·
                    refine ⟨406227553948575696761689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 541636738598100929015585 406227553948575696761689)
                    ·
                      refine ⟨304670665461431772571267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 406227553948575696761689 304670665461431772571267)
                      ·
                        rfl

theorem cell23_593344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 1, 2, 2].length) (baseStart_593344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593344 prefixEnd_593344 := by exact prefixLift 593344
  have htrace : WordTrace (prefixWord ++ tailWord_593344) baseStart_593344 baseEnd_593344 := by
    simpa [prefixWord, tailWord_593344, baseEnd_593344] using wordTrace_append hprefix tailTrace_593344
  have hstable : (prefixWord ++ tailWord_593344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593344).length < 2 ^ (prefixWord ++ tailWord_593344).sum := by decide
  have hdescent : baseEnd_593344 < baseStart_593344 := by decide
  rcases family_descends (prefixWord ++ tailWord_593344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593364 : List Nat := [2, 4, 1, 2, 3, 1, 2, 2, 1, 2, 3]
def baseStart_593364 : Nat := 118140960795 + 593364 * 2 ^ 59
def prefixEnd_593364 : Nat := 4983230072969 + 3 ^ 40 * 593364 * 2
def baseEnd_593364 : Nat := 304680935074521694321175

theorem tailTrace_593364 : CollatzResearch.WordTrace tailWord_593364 prefixEnd_593364 304680935074521694321175 := by
  unfold tailWord_593364
  simp only [CollatzResearch.WordTrace]
  refine ⟨10820881511175520674169573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14427842014900694232226097 10820881511175520674169573)
  ·
    refine ⟨2028915283345410126406795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10820881511175520674169573 2028915283345410126406795)
    ·
      refine ⟨3043372925018115189610193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2028915283345410126406795 3043372925018115189610193)
      ·
        refine ⟨2282529693763586392207645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3043372925018115189610193 2282529693763586392207645)
        ·
          refine ⟨855948635161344897077867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2282529693763586392207645 855948635161344897077867)
          ·
            refine ⟨1283922952742017345616801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 855948635161344897077867 1283922952742017345616801)
            ·
              refine ⟨962942214556513009212601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1283922952742017345616801 962942214556513009212601)
              ·
                refine ⟨722206660917384756909451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 962942214556513009212601 722206660917384756909451)
                ·
                  refine ⟨1083309991376077135364177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 722206660917384756909451 1083309991376077135364177)
                  ·
                    refine ⟨812482493532057851523133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1083309991376077135364177 812482493532057851523133)
                    ·
                      refine ⟨304680935074521694321175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 812482493532057851523133 304680935074521694321175)
                      ·
                        rfl

theorem cell23_593364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_593364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593364 prefixEnd_593364 := by exact prefixLift 593364
  have htrace : WordTrace (prefixWord ++ tailWord_593364) baseStart_593364 baseEnd_593364 := by
    simpa [prefixWord, tailWord_593364, baseEnd_593364] using wordTrace_append hprefix tailTrace_593364
  have hstable : (prefixWord ++ tailWord_593364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593364).length < 2 ^ (prefixWord ++ tailWord_593364).sum := by decide
  have hdescent : baseEnd_593364 < baseStart_593364 := by decide
  rcases family_descends (prefixWord ++ tailWord_593364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593403 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 3]
def baseStart_593403 : Nat := 118140960795 + 593403 * 2 ^ 59
def prefixEnd_593403 : Nat := 4983230072969 + 3 ^ 40 * 593403 * 2
def baseEnd_593403 : Nat := 304700960820047041733495

theorem tailTrace_593403 : CollatzResearch.WordTrace tailWord_593403 prefixEnd_593403 304700960820047041733495 := by
  unfold tailWord_593403
  simp only [CollatzResearch.WordTrace]
  refine ⟨21643185469209751009008863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14428790312806500672672575 21643185469209751009008863)
  ·
    refine ⟨32464778203814626513513295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21643185469209751009008863 32464778203814626513513295)
    ·
      refine ⟨48697167305721939770269943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32464778203814626513513295 48697167305721939770269943)
      ·
        refine ⟨73045750958582909655404915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48697167305721939770269943 73045750958582909655404915)
        ·
          refine ⟨109568626437874364483107373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73045750958582909655404915 109568626437874364483107373)
          ·
            refine ⟨41088234914202886681165265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109568626437874364483107373 41088234914202886681165265)
            ·
              refine ⟨30816176185652165010873949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41088234914202886681165265 30816176185652165010873949)
              ·
                refine ⟨11556066069619561879077731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30816176185652165010873949 11556066069619561879077731)
                ·
                  refine ⟨17334099104429342818616597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11556066069619561879077731 17334099104429342818616597)
                  ·
                    refine ⟨812535895520125444622653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17334099104429342818616597 812535895520125444622653)
                    ·
                      refine ⟨304700960820047041733495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 812535895520125444622653 304700960820047041733495)
                      ·
                        rfl

theorem cell23_593403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 3].length) (baseStart_593403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593403 prefixEnd_593403 := by exact prefixLift 593403
  have htrace : WordTrace (prefixWord ++ tailWord_593403) baseStart_593403 baseEnd_593403 := by
    simpa [prefixWord, tailWord_593403, baseEnd_593403] using wordTrace_append hprefix tailTrace_593403
  have hstable : (prefixWord ++ tailWord_593403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593403).length < 2 ^ (prefixWord ++ tailWord_593403).sum := by decide
  have hdescent : baseEnd_593403 < baseStart_593403 := by decide
  rcases family_descends (prefixWord ++ tailWord_593403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593413 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 1, 4, 4]
def baseStart_593413 : Nat := 118140960795 + 593413 * 2 ^ 59
def prefixEnd_593413 : Nat := 4983230072969 + 3 ^ 40 * 593413 * 2
def baseEnd_593413 : Nat := 304706095626592002608449

theorem tailTrace_593413 : CollatzResearch.WordTrace tailWord_593413 prefixEnd_593413 304706095626592002608449 := by
  unfold tailWord_593413
  simp only [CollatzResearch.WordTrace]
  refine ⟨21643550199173522716872893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14429033466115681811248595 21643550199173522716872893)
  ·
    refine ⟨8116331324690071018827335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21643550199173522716872893 8116331324690071018827335)
    ·
      refine ⟨12174496987035106528241003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8116331324690071018827335 12174496987035106528241003)
      ·
        refine ⟨18261745480552659792361505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12174496987035106528241003 18261745480552659792361505)
        ·
          refine ⟨13696309110414494844271129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18261745480552659792361505 13696309110414494844271129)
          ·
            refine ⟨10272231832810871133203347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13696309110414494844271129 10272231832810871133203347)
            ·
              refine ⟨15408347749216306699805021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10272231832810871133203347 15408347749216306699805021)
              ·
                refine ⟨5778130405956115012426883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15408347749216306699805021 5778130405956115012426883)
                ·
                  refine ⟨8667195608934172518640325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5778130405956115012426883 8667195608934172518640325)
                  ·
                    refine ⟨1625099176675157347245061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8667195608934172518640325 1625099176675157347245061)
                    ·
                      refine ⟨304706095626592002608449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1625099176675157347245061 304706095626592002608449)
                      ·
                        rfl

theorem cell23_593413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_593413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593413 prefixEnd_593413 := by exact prefixLift 593413
  have htrace : WordTrace (prefixWord ++ tailWord_593413) baseStart_593413 baseEnd_593413 := by
    simpa [prefixWord, tailWord_593413, baseEnd_593413] using wordTrace_append hprefix tailTrace_593413
  have hstable : (prefixWord ++ tailWord_593413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593413).length < 2 ^ (prefixWord ++ tailWord_593413).sum := by decide
  have hdescent : baseEnd_593413 < baseStart_593413 := by decide
  rcases family_descends (prefixWord ++ tailWord_593413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593507 : List Nat := [1, 1, 1, 5, 1, 3, 1, 2, 2, 4, 2]
def baseStart_593507 : Nat := 118140960795 + 593507 * 2 ^ 59
def prefixEnd_593507 : Nat := 4983230072969 + 3 ^ 40 * 593507 * 2
def baseEnd_593507 : Nat := 304754362808114634833017

theorem tailTrace_593507 : CollatzResearch.WordTrace tailWord_593507 prefixEnd_593507 304754362808114634833017 := by
  unfold tailWord_593507
  simp only [CollatzResearch.WordTrace]
  refine ⟨21646978660832976770794775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14431319107221984513863183 21646978660832976770794775)
  ·
    refine ⟨32470467991249465156192163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21646978660832976770794775 32470467991249465156192163)
    ·
      refine ⟨48705701986874197734288245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32470467991249465156192163 48705701986874197734288245)
      ·
        refine ⟨4566159561269456037589523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48705701986874197734288245 4566159561269456037589523)
        ·
          refine ⟨6849239341904184056384285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4566159561269456037589523 6849239341904184056384285)
          ·
            refine ⟨2568464753214069021144107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6849239341904184056384285 2568464753214069021144107)
            ·
              refine ⟨3852697129821103531716161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2568464753214069021144107 3852697129821103531716161)
              ·
                refine ⟨2889522847365827648787121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3852697129821103531716161 2889522847365827648787121)
                ·
                  refine ⟨2167142135524370736590341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2889522847365827648787121 2167142135524370736590341)
                  ·
                    refine ⟨406339150410819513110689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2167142135524370736590341 406339150410819513110689)
                    ·
                      refine ⟨304754362808114634833017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 406339150410819513110689 304754362808114634833017)
                      ·
                        rfl

theorem cell23_593507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_593507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593507 prefixEnd_593507 := by exact prefixLift 593507
  have htrace : WordTrace (prefixWord ++ tailWord_593507) baseStart_593507 baseEnd_593507 := by
    simpa [prefixWord, tailWord_593507, baseEnd_593507] using wordTrace_append hprefix tailTrace_593507
  have hstable : (prefixWord ++ tailWord_593507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593507).length < 2 ^ (prefixWord ++ tailWord_593507).sum := by decide
  have hdescent : baseEnd_593507 < baseStart_593507 := by decide
  rcases family_descends (prefixWord ++ tailWord_593507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593523 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 9]
def baseStart_593523 : Nat := 118140960795 + 593523 * 2 ^ 59
def prefixEnd_593523 : Nat := 4983230072969 + 3 ^ 40 * 593523 * 2
def baseEnd_593523 : Nat := 304762578498586572232943

theorem tailTrace_593523 : CollatzResearch.WordTrace tailWord_593523 prefixEnd_593523 304762578498586572232943 := by
  unfold tailWord_593523
  simp only [CollatzResearch.WordTrace]
  refine ⟨21647562228775011503377223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14431708152516674335584815 21647562228775011503377223)
  ·
    refine ⟨32471343343162517255065835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21647562228775011503377223 32471343343162517255065835)
    ·
      refine ⟨48707015014743775882598753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32471343343162517255065835 48707015014743775882598753)
      ·
        refine ⟨36530261261057831911949065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48707015014743775882598753 36530261261057831911949065)
        ·
          refine ⟨27397695945793373933961799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36530261261057831911949065 27397695945793373933961799)
          ·
            refine ⟨41096543918690060900942699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27397695945793373933961799 41096543918690060900942699)
            ·
              refine ⟨61644815878035091351414049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41096543918690060900942699 61644815878035091351414049)
              ·
                refine ⟨46233611908526318513560537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61644815878035091351414049 46233611908526318513560537)
                ·
                  refine ⟨34675208931394738885170403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46233611908526318513560537 34675208931394738885170403)
                  ·
                    refine ⟨52012813397092108327755605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34675208931394738885170403 52012813397092108327755605)
                    ·
                      refine ⟨304762578498586572232943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 52012813397092108327755605 304762578498586572232943)
                      ·
                        rfl

theorem cell23_593523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_593523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593523 prefixEnd_593523 := by exact prefixLift 593523
  have htrace : WordTrace (prefixWord ++ tailWord_593523) baseStart_593523 baseEnd_593523 := by
    simpa [prefixWord, tailWord_593523, baseEnd_593523] using wordTrace_append hprefix tailTrace_593523
  have hstable : (prefixWord ++ tailWord_593523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593523).length < 2 ^ (prefixWord ++ tailWord_593523).sum := by decide
  have hdescent : baseEnd_593523 < baseStart_593523 := by decide
  rcases family_descends (prefixWord ++ tailWord_593523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593557 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 5, 1, 3]
def baseStart_593557 : Nat := 118140960795 + 593557 * 2 ^ 59
def prefixEnd_593557 : Nat := 4983230072969 + 3 ^ 40 * 593557 * 2
def baseEnd_593557 : Nat := 304780036840839439207787

theorem tailTrace_593557 : CollatzResearch.WordTrace tailWord_593557 prefixEnd_593557 304780036840839439207787 := by
  unfold tailWord_593557
  simp only [CollatzResearch.WordTrace]
  refine ⟨21648802310651835310114925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14432534873767890206743283 21648802310651835310114925)
  ·
    refine ⟨8118300866494438241293097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21648802310651835310114925 8118300866494438241293097)
    ·
      refine ⟨6088725649870828680969823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8118300866494438241293097 6088725649870828680969823)
      ·
        refine ⟨9133088474806243021454735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6088725649870828680969823 9133088474806243021454735)
        ·
          refine ⟨13699632712209364532182103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9133088474806243021454735 13699632712209364532182103)
          ·
            refine ⟨20549449068314046798273155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13699632712209364532182103 20549449068314046798273155)
            ·
              refine ⟨30824173602471070197409733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20549449068314046798273155 30824173602471070197409733)
              ·
                refine ⟨5779532550463325662014325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30824173602471070197409733 5779532550463325662014325)
                ·
                  refine ⟨541831176605936780813843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5779532550463325662014325 541831176605936780813843)
                  ·
                    refine ⟨812746764908905171220765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 541831176605936780813843 812746764908905171220765)
                    ·
                      refine ⟨304780036840839439207787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 812746764908905171220765 304780036840839439207787)
                      ·
                        rfl

theorem cell23_593557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_593557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593557 prefixEnd_593557 := by exact prefixLift 593557
  have htrace : WordTrace (prefixWord ++ tailWord_593557) baseStart_593557 baseEnd_593557 := by
    simpa [prefixWord, tailWord_593557, baseEnd_593557] using wordTrace_append hprefix tailTrace_593557
  have hstable : (prefixWord ++ tailWord_593557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593557).length < 2 ^ (prefixWord ++ tailWord_593557).sum := by decide
  have hdescent : baseEnd_593557 < baseStart_593557 := by decide
  rcases family_descends (prefixWord ++ tailWord_593557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593594 : List Nat := [3, 1, 1, 1, 2, 6, 1, 2, 1, 5]
def baseStart_593594 : Nat := 118140960795 + 593594 * 2 ^ 59
def prefixEnd_593594 : Nat := 4983230072969 + 3 ^ 40 * 593594 * 2
def baseEnd_593594 : Nat := 101599678541685264815039

theorem tailTrace_593594 : CollatzResearch.WordTrace tailWord_593594 prefixEnd_593594 101599678541685264815039 := by
  unfold tailWord_593594
  simp only [CollatzResearch.WordTrace]
  refine ⟨5412537952879447657302959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14433434541011860419474557 5412537952879447657302959)
  ·
    refine ⟨8118806929319171485954439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5412537952879447657302959 8118806929319171485954439)
    ·
      refine ⟨12178210393978757228931659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8118806929319171485954439 12178210393978757228931659)
      ·
        refine ⟨18267315590968135843397489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12178210393978757228931659 18267315590968135843397489)
        ·
          refine ⟨13700486693226101882548117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18267315590968135843397489 13700486693226101882548117)
          ·
            refine ⟨642210313744973525744443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13700486693226101882548117 642210313744973525744443)
            ·
              refine ⟨963315470617460288616665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 642210313744973525744443 963315470617460288616665)
              ·
                refine ⟨722486602963095216462499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 963315470617460288616665 722486602963095216462499)
                ·
                  refine ⟨1083729904444642824693749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 722486602963095216462499 1083729904444642824693749)
                  ·
                    refine ⟨101599678541685264815039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1083729904444642824693749 101599678541685264815039)
                    ·
                      rfl

theorem cell23_593594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 1, 5].length) (baseStart_593594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593594 prefixEnd_593594 := by exact prefixLift 593594
  have htrace : WordTrace (prefixWord ++ tailWord_593594) baseStart_593594 baseEnd_593594 := by
    simpa [prefixWord, tailWord_593594, baseEnd_593594] using wordTrace_append hprefix tailTrace_593594
  have hstable : (prefixWord ++ tailWord_593594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593594).length < 2 ^ (prefixWord ++ tailWord_593594).sum := by decide
  have hdescent : baseEnd_593594 < baseStart_593594 := by decide
  rcases family_descends (prefixWord ++ tailWord_593594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593597 : List Nat := [1, 4, 1, 2, 1, 2, 3, 1, 3, 1, 4]
def baseStart_593597 : Nat := 118140960795 + 593597 * 2 ^ 59
def prefixEnd_593597 : Nat := 4983230072969 + 3 ^ 40 * 593597 * 2
def baseEnd_593597 : Nat := 304800576067019282707603

theorem tailTrace_593597 : CollatzResearch.WordTrace tailWord_593597 prefixEnd_593597 304800576067019282707603 := by
  unfold tailWord_593597
  simp only [CollatzResearch.WordTrace]
  refine ⟨21650261230506922141571045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14433507487004614761047363 21650261230506922141571045)
  ·
    refine ⟨4059423980720047901544571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21650261230506922141571045 4059423980720047901544571)
    ·
      refine ⟨6089135971080071852316857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4059423980720047901544571 6089135971080071852316857)
      ·
        refine ⟨4566851978310053889237643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6089135971080071852316857 4566851978310053889237643)
        ·
          refine ⟨6850277967465080833856465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4566851978310053889237643 6850277967465080833856465)
          ·
            refine ⟨5137708475598810625392349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6850277967465080833856465 5137708475598810625392349)
            ·
              refine ⟨1926640678349553984522131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5137708475598810625392349 1926640678349553984522131)
              ·
                refine ⟨2889961017524330976783197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1926640678349553984522131 2889961017524330976783197)
                ·
                  refine ⟨1083735381571624116293699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2889961017524330976783197 1083735381571624116293699)
                  ·
                    refine ⟨1625603072357436174440549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1083735381571624116293699 1625603072357436174440549)
                    ·
                      refine ⟨304800576067019282707603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1625603072357436174440549 304800576067019282707603)
                      ·
                        rfl

theorem cell23_593597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_593597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593597 prefixEnd_593597 := by exact prefixLift 593597
  have htrace : WordTrace (prefixWord ++ tailWord_593597) baseStart_593597 baseEnd_593597 := by
    simpa [prefixWord, tailWord_593597, baseEnd_593597] using wordTrace_append hprefix tailTrace_593597
  have hstable : (prefixWord ++ tailWord_593597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593597).length < 2 ^ (prefixWord ++ tailWord_593597).sum := by decide
  have hdescent : baseEnd_593597 < baseStart_593597 := by decide
  rcases family_descends (prefixWord ++ tailWord_593597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593617 : List Nat := [1, 2, 2, 1, 2, 4, 3, 1, 1, 1, 5]
def baseStart_593617 : Nat := 118140960795 + 593617 * 2 ^ 59
def prefixEnd_593617 : Nat := 4983230072969 + 3 ^ 40 * 593617 * 2
def baseEnd_593617 : Nat := 304810845680109204457511

theorem tailTrace_593617 : CollatzResearch.WordTrace tailWord_593617 prefixEnd_593617 304810845680109204457511 := by
  unfold tailWord_593617
  simp only [CollatzResearch.WordTrace]
  refine ⟨21650990690434465557299105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14433993793622977038199403 21650990690434465557299105)
  ·
    refine ⟨16238243017825849167974329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21650990690434465557299105 16238243017825849167974329)
    ·
      refine ⟨12178682263369386875980747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16238243017825849167974329 12178682263369386875980747)
      ·
        refine ⟨18268023395054080313971121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12178682263369386875980747 18268023395054080313971121)
        ·
          refine ⟨13701017546290560235478341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18268023395054080313971121 13701017546290560235478341)
          ·
            refine ⟨2568940789929480044152189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13701017546290560235478341 2568940789929480044152189)
            ·
              refine ⟨963352796223555016557071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2568940789929480044152189 963352796223555016557071)
              ·
                refine ⟨1445029194335332524835607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 963352796223555016557071 1445029194335332524835607)
                ·
                  refine ⟨2167543791502998787253411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1445029194335332524835607 2167543791502998787253411)
                  ·
                    refine ⟨3251315687254498180880117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2167543791502998787253411 3251315687254498180880117)
                    ·
                      refine ⟨304810845680109204457511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3251315687254498180880117 304810845680109204457511)
                      ·
                        rfl

theorem cell23_593617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 1, 5].length) (baseStart_593617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593617 prefixEnd_593617 := by exact prefixLift 593617
  have htrace : WordTrace (prefixWord ++ tailWord_593617) baseStart_593617 baseEnd_593617 := by
    simpa [prefixWord, tailWord_593617, baseEnd_593617] using wordTrace_append hprefix tailTrace_593617
  have hstable : (prefixWord ++ tailWord_593617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593617).length < 2 ^ (prefixWord ++ tailWord_593617).sum := by decide
  have hdescent : baseEnd_593617 < baseStart_593617 := by decide
  rcases family_descends (prefixWord ++ tailWord_593617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593624 : List Nat := [2, 1, 2, 2, 3, 1, 4, 2, 2, 4]
def baseStart_593624 : Nat := 118140960795 + 593624 * 2 ^ 59
def prefixEnd_593624 : Nat := 4983230072969 + 3 ^ 40 * 593624 * 2
def baseEnd_593624 : Nat := 101604813348230225689993

theorem tailTrace_593624 : CollatzResearch.WordTrace tailWord_593624 prefixEnd_593624 101604813348230225689993 := by
  unfold tailWord_593624
  simp only [CollatzResearch.WordTrace]
  refine ⟨10825623000704552876401963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14434164000939403835202617 10825623000704552876401963)
  ·
    refine ⟨16238434501056829314602945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10825623000704552876401963 16238434501056829314602945)
    ·
      refine ⟨12178825875792621985952209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16238434501056829314602945 12178825875792621985952209)
      ·
        refine ⟨9134119406844466489464157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12178825875792621985952209 9134119406844466489464157)
        ·
          refine ⟨3425294777566674933549059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9134119406844466489464157 3425294777566674933549059)
          ·
            refine ⟨5137942166350012400323589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3425294777566674933549059 5137942166350012400323589)
            ·
              refine ⟨963364156190627325060673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5137942166350012400323589 963364156190627325060673)
              ·
                refine ⟨722523117142970493795505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 963364156190627325060673 722523117142970493795505)
                ·
                  refine ⟨541892337857227870346629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 722523117142970493795505 541892337857227870346629)
                  ·
                    refine ⟨101604813348230225689993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 541892337857227870346629 101604813348230225689993)
                    ·
                      rfl

theorem cell23_593624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 2, 4].length) (baseStart_593624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593624 prefixEnd_593624 := by exact prefixLift 593624
  have htrace : WordTrace (prefixWord ++ tailWord_593624) baseStart_593624 baseEnd_593624 := by
    simpa [prefixWord, tailWord_593624, baseEnd_593624] using wordTrace_append hprefix tailTrace_593624
  have hstable : (prefixWord ++ tailWord_593624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593624).length < 2 ^ (prefixWord ++ tailWord_593624).sum := by decide
  have hdescent : baseEnd_593624 < baseStart_593624 := by decide
  rcases family_descends (prefixWord ++ tailWord_593624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593654 : List Nat := [5, 1, 1, 1, 1, 4, 3, 7]
def baseStart_593654 : Nat := 118140960795 + 593654 * 2 ^ 59
def prefixEnd_593654 : Nat := 4983230072969 + 3 ^ 40 * 593654 * 2
def baseEnd_593654 : Nat := 11289994239419465173883

theorem tailTrace_593654 : CollatzResearch.WordTrace tailWord_593654 prefixEnd_593654 11289994239419465173883 := by
  unfold tailWord_593654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1353271261956276304774751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14434893460866947250930677 1353271261956276304774751)
  ·
    refine ⟨2029906892934414457162127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1353271261956276304774751 2029906892934414457162127)
    ·
      refine ⟨3044860339401621685743191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2029906892934414457162127 3044860339401621685743191)
      ·
        refine ⟨4567290509102432528614787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3044860339401621685743191 4567290509102432528614787)
        ·
          refine ⟨6850935763653648792922181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4567290509102432528614787 6850935763653648792922181)
          ·
            refine ⟨1284550455685059148672909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6850935763653648792922181 1284550455685059148672909)
            ·
              refine ⟨481706420881897180752341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1284550455685059148672909 481706420881897180752341)
              ·
                refine ⟨11289994239419465173883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 481706420881897180752341 11289994239419465173883)
                ·
                  rfl

theorem cell23_593654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_593654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593654 prefixEnd_593654 := by exact prefixLift 593654
  have htrace : WordTrace (prefixWord ++ tailWord_593654) baseStart_593654 baseEnd_593654 := by
    simpa [prefixWord, tailWord_593654, baseEnd_593654] using wordTrace_append hprefix tailTrace_593654
  have hstable : (prefixWord ++ tailWord_593654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593654).length < 2 ^ (prefixWord ++ tailWord_593654).sum := by decide
  have hdescent : baseEnd_593654 < baseStart_593654 := by decide
  rcases family_descends (prefixWord ++ tailWord_593654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593668 : List Nat := [2, 3, 2, 2, 1, 4, 2, 1, 1, 2, 3]
def baseStart_593668 : Nat := 118140960795 + 593668 * 2 ^ 59
def prefixEnd_593668 : Nat := 4983230072969 + 3 ^ 40 * 593668 * 2
def baseEnd_593668 : Nat := 304837033193488504919777

theorem tailTrace_593668 : CollatzResearch.WordTrace tailWord_593668 prefixEnd_593668 304837033193488504919777 := by
  unfold tailWord_593668
  simp only [CollatzResearch.WordTrace]
  refine ⟨10826425406624850633702829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14435233875499800844937105 10826425406624850633702829)
  ·
    refine ⟨4059909527484318987638561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10826425406624850633702829 4059909527484318987638561)
    ·
      refine ⟨3044932145613239240728921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4059909527484318987638561 3044932145613239240728921)
      ·
        refine ⟨2283699109209929430546691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3044932145613239240728921 2283699109209929430546691)
        ·
          refine ⟨3425548663814894145820037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2283699109209929430546691 3425548663814894145820037)
          ·
            refine ⟨642290374465292652341257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3425548663814894145820037 642290374465292652341257)
            ·
              refine ⟨481717780848969489255943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 642290374465292652341257 481717780848969489255943)
              ·
                refine ⟨722576671273454233883915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 481717780848969489255943 722576671273454233883915)
                ·
                  refine ⟨1083865006910181350825873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 722576671273454233883915 1083865006910181350825873)
                  ·
                    refine ⟨812898755182636013119405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1083865006910181350825873 812898755182636013119405)
                    ·
                      refine ⟨304837033193488504919777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 812898755182636013119405 304837033193488504919777)
                      ·
                        rfl

theorem cell23_593668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_593668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593668 prefixEnd_593668 := by exact prefixLift 593668
  have htrace : WordTrace (prefixWord ++ tailWord_593668) baseStart_593668 baseEnd_593668 := by
    simpa [prefixWord, tailWord_593668, baseEnd_593668] using wordTrace_append hprefix tailTrace_593668
  have hstable : (prefixWord ++ tailWord_593668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593668).length < 2 ^ (prefixWord ++ tailWord_593668).sum := by decide
  have hdescent : baseEnd_593668 < baseStart_593668 := by decide
  rcases family_descends (prefixWord ++ tailWord_593668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593697 : List Nat := [1, 2, 3, 2, 1, 3, 2, 1, 2, 6]
def baseStart_593697 : Nat := 118140960795 + 593697 * 2 ^ 59
def prefixEnd_593697 : Nat := 4983230072969 + 3 ^ 40 * 593697 * 2
def baseEnd_593697 : Nat := 101617308044156297152381

theorem tailTrace_593697 : CollatzResearch.WordTrace tailWord_593697 prefixEnd_593697 101617308044156297152381 := by
  unfold tailWord_593697
  simp only [CollatzResearch.WordTrace]
  refine ⟨21653908530144639220211345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14435939020096426146807563 21653908530144639220211345)
  ·
    refine ⟨16240431397608479415158509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21653908530144639220211345 16240431397608479415158509)
    ·
      refine ⟨6090161774103179780684441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16240431397608479415158509 6090161774103179780684441)
      ·
        refine ⟨4567621330577384835513331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6090161774103179780684441 4567621330577384835513331)
        ·
          refine ⟨6851431995866077253269997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4567621330577384835513331 6851431995866077253269997)
          ·
            refine ⟨2569286998449778969976249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6851431995866077253269997 2569286998449778969976249)
            ·
              refine ⟨1926965248837334227482187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2569286998449778969976249 1926965248837334227482187)
              ·
                refine ⟨2890447873256001341223281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1926965248837334227482187 2890447873256001341223281)
                ·
                  refine ⟨2167835904942001005917461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2890447873256001341223281 2167835904942001005917461)
                  ·
                    refine ⟨101617308044156297152381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2167835904942001005917461 101617308044156297152381)
                    ·
                      rfl

theorem cell23_593697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_593697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593697 prefixEnd_593697 := by exact prefixLift 593697
  have htrace : WordTrace (prefixWord ++ tailWord_593697) baseStart_593697 baseEnd_593697 := by
    simpa [prefixWord, tailWord_593697, baseEnd_593697] using wordTrace_append hprefix tailTrace_593697
  have hstable : (prefixWord ++ tailWord_593697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593697).length < 2 ^ (prefixWord ++ tailWord_593697).sum := by decide
  have hdescent : baseEnd_593697 < baseStart_593697 := by decide
  rcases family_descends (prefixWord ++ tailWord_593697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593698 : List Nat := [3, 3, 1, 1, 2, 1, 5, 1, 2, 1, 3]
def baseStart_593698 : Nat := 118140960795 + 593698 * 2 ^ 59
def prefixEnd_593698 : Nat := 4983230072969 + 3 ^ 40 * 593698 * 2
def baseEnd_593698 : Nat := 304852437613123387544639

theorem tailTrace_593698 : CollatzResearch.WordTrace tailWord_593698 prefixEnd_593698 304852437613123387544639 := by
  unfold tailWord_593698
  simp only [CollatzResearch.WordTrace]
  refine ⟨5413486250785254097749437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14435963335427344260665165 5413486250785254097749437)
  ·
    refine ⟨2030057344044470286656039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5413486250785254097749437 2030057344044470286656039)
    ·
      refine ⟨3045086016066705429984059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2030057344044470286656039 3045086016066705429984059)
      ·
        refine ⟨4567629024100058144976089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3045086016066705429984059 4567629024100058144976089)
        ·
          refine ⟨3425721768075043608732067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4567629024100058144976089 3425721768075043608732067)
          ·
            refine ⟨5138582652112565413098101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3425721768075043608732067 5138582652112565413098101)
            ·
              refine ⟨481742123635553007477947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5138582652112565413098101 481742123635553007477947)
              ·
                refine ⟨722613185453329511216921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 481742123635553007477947 722613185453329511216921)
                ·
                  refine ⟨541959889089997133412691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 722613185453329511216921 541959889089997133412691)
                  ·
                    refine ⟨812939833634995700119037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 541959889089997133412691 812939833634995700119037)
                    ·
                      refine ⟨304852437613123387544639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 812939833634995700119037 304852437613123387544639)
                      ·
                        rfl

theorem cell23_593698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_593698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593698 prefixEnd_593698 := by exact prefixLift 593698
  have htrace : WordTrace (prefixWord ++ tailWord_593698) baseStart_593698 baseEnd_593698 := by
    simpa [prefixWord, tailWord_593698, baseEnd_593698] using wordTrace_append hprefix tailTrace_593698
  have hstable : (prefixWord ++ tailWord_593698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593698).length < 2 ^ (prefixWord ++ tailWord_593698).sum := by decide
  have hdescent : baseEnd_593698 < baseStart_593698 := by decide
  rcases family_descends (prefixWord ++ tailWord_593698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593767 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_593767 : Nat := 118140960795 + 593767 * 2 ^ 59
def prefixEnd_593767 : Nat := 4983230072969 + 3 ^ 40 * 593767 * 2
def baseEnd_593767 : Nat := 304887867778283617581821

theorem tailTrace_593767 : CollatzResearch.WordTrace tailWord_593767 prefixEnd_593767 304887867778283617581821 := by
  unfold tailWord_593767
  simp only [CollatzResearch.WordTrace]
  refine ⟨21656461639891041175259555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14437641093260694116839703 21656461639891041175259555)
  ·
    refine ⟨32484692459836561762889333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21656461639891041175259555 32484692459836561762889333)
    ·
      refine ⟨3045439918109677665270875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32484692459836561762889333 3045439918109677665270875)
      ·
        refine ⟨4568159877164516497906313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3045439918109677665270875 4568159877164516497906313)
        ·
          refine ⟨3426119907873387373429735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4568159877164516497906313 3426119907873387373429735)
          ·
            refine ⟨5139179861810081060144603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3426119907873387373429735 5139179861810081060144603)
            ·
              refine ⟨7708769792715121590216905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5139179861810081060144603 7708769792715121590216905)
              ·
                refine ⟨5781577344536341192662679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7708769792715121590216905 5781577344536341192662679)
                ·
                  refine ⟨8672366016804511788994019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5781577344536341192662679 8672366016804511788994019)
                  ·
                    refine ⟨13008549025206767683491029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8672366016804511788994019 13008549025206767683491029)
                    ·
                      refine ⟨304887867778283617581821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13008549025206767683491029 304887867778283617581821)
                      ·
                        rfl

theorem cell23_593767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_593767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593767 prefixEnd_593767 := by exact prefixLift 593767
  have htrace : WordTrace (prefixWord ++ tailWord_593767) baseStart_593767 baseEnd_593767 := by
    simpa [prefixWord, tailWord_593767, baseEnd_593767] using wordTrace_append hprefix tailTrace_593767
  have hstable : (prefixWord ++ tailWord_593767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593767).length < 2 ^ (prefixWord ++ tailWord_593767).sum := by decide
  have hdescent : baseEnd_593767 < baseStart_593767 := by decide
  rcases family_descends (prefixWord ++ tailWord_593767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593797 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 2, 3, 5]
def baseStart_593797 : Nat := 118140960795 + 593797 * 2 ^ 59
def prefixEnd_593797 : Nat := 4983230072969 + 3 ^ 40 * 593797 * 2
def baseEnd_593797 : Nat := 304903272197918500206683

theorem tailTrace_593797 : CollatzResearch.WordTrace tailWord_593797 prefixEnd_593797 304903272197918500206683 := by
  unfold tailWord_593797
  simp only [CollatzResearch.WordTrace]
  refine ⟨21657555829782356298851645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14438370553188237532567763 21657555829782356298851645)
  ·
    refine ⟨8121583436168383612069367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21657555829782356298851645 8121583436168383612069367)
    ·
      refine ⟨12182375154252575418104051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8121583436168383612069367 12182375154252575418104051)
      ·
        refine ⟨18273562731378863127156077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12182375154252575418104051 18273562731378863127156077)
        ·
          refine ⟨6852586024267073672683529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18273562731378863127156077 6852586024267073672683529)
          ·
            refine ⟨5139439518200305254512647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6852586024267073672683529 5139439518200305254512647)
            ·
              refine ⟨7709159277300457881768971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5139439518200305254512647 7709159277300457881768971)
              ·
                refine ⟨11563738915950686822653457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7709159277300457881768971 11563738915950686822653457)
                ·
                  refine ⟨8672804186963015116990093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11563738915950686822653457 8672804186963015116990093)
                  ·
                    refine ⟨3252301570111130668871285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8672804186963015116990093 3252301570111130668871285)
                    ·
                      refine ⟨304903272197918500206683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3252301570111130668871285 304903272197918500206683)
                      ·
                        rfl

theorem cell23_593797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_593797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593797 prefixEnd_593797 := by exact prefixLift 593797
  have htrace : WordTrace (prefixWord ++ tailWord_593797) baseStart_593797 baseEnd_593797 := by
    simpa [prefixWord, tailWord_593797, baseEnd_593797] using wordTrace_append hprefix tailTrace_593797
  have hstable : (prefixWord ++ tailWord_593797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593797).length < 2 ^ (prefixWord ++ tailWord_593797).sum := by decide
  have hdescent : baseEnd_593797 < baseStart_593797 := by decide
  rcases family_descends (prefixWord ++ tailWord_593797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593804 : List Nat := [2, 2, 1, 2, 1, 2, 1, 5, 3, 4]
def baseStart_593804 : Nat := 118140960795 + 593804 * 2 ^ 59
def prefixEnd_593804 : Nat := 4983230072969 + 3 ^ 40 * 593804 * 2
def baseEnd_593804 : Nat := 101635622187499990939717

theorem tailTrace_593804 : CollatzResearch.WordTrace tailWord_593804 prefixEnd_593804 101635622187499990939717 := by
  unfold tailWord_593804
  simp only [CollatzResearch.WordTrace]
  refine ⟨10828905570378498247178233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14438540760504664329570977 10828905570378498247178233)
  ·
    refine ⟨8121679177783873685383675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10828905570378498247178233 8121679177783873685383675)
    ·
      refine ⟨12182518766675810528075513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8121679177783873685383675 12182518766675810528075513)
      ·
        refine ⟨9136889075006857896056635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12182518766675810528075513 9136889075006857896056635)
        ·
          refine ⟨13705333612510286844084953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9136889075006857896056635 13705333612510286844084953)
          ·
            refine ⟨10279000209382715133063715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13705333612510286844084953 10279000209382715133063715)
            ·
              refine ⟨15418500314074072699595573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10279000209382715133063715 15418500314074072699595573)
              ·
                refine ⟨1445484404444444315587085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15418500314074072699595573 1445484404444444315587085)
                ·
                  refine ⟨542056651666666618345157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1445484404444444315587085 542056651666666618345157)
                  ·
                    refine ⟨101635622187499990939717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 542056651666666618345157 101635622187499990939717)
                    ·
                      rfl

theorem cell23_593804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 3, 4].length) (baseStart_593804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593804 prefixEnd_593804 := by exact prefixLift 593804
  have htrace : WordTrace (prefixWord ++ tailWord_593804) baseStart_593804 baseEnd_593804 := by
    simpa [prefixWord, tailWord_593804, baseEnd_593804] using wordTrace_append hprefix tailTrace_593804
  have hstable : (prefixWord ++ tailWord_593804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593804).length < 2 ^ (prefixWord ++ tailWord_593804).sum := by decide
  have hdescent : baseEnd_593804 < baseStart_593804 := by decide
  rcases family_descends (prefixWord ++ tailWord_593804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593821 : List Nat := [1, 4, 2, 1, 2, 3, 1, 2, 3, 4]
def baseStart_593821 : Nat := 118140960795 + 593821 * 2 ^ 59
def prefixEnd_593821 : Nat := 4983230072969 + 3 ^ 40 * 593821 * 2
def baseEnd_593821 : Nat := 101638531911208802102191

theorem tailTrace_593821 : CollatzResearch.WordTrace tailWord_593821 prefixEnd_593821 101638531911208802102191 := by
  unfold tailWord_593821
  simp only [CollatzResearch.WordTrace]
  refine ⟨21658431181695408397725317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14438954121130272265150211 21658431181695408397725317)
  ·
    refine ⟨4060955846567889074573497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21658431181695408397725317 4060955846567889074573497)
    ·
      refine ⟨3045716884925916805930123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4060955846567889074573497 3045716884925916805930123)
      ·
        refine ⟨4568575327388875208895185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3045716884925916805930123 4568575327388875208895185)
        ·
          refine ⟨3426431495541656406671389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4568575327388875208895185 3426431495541656406671389)
          ·
            refine ⟨1284911810828121152501771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3426431495541656406671389 1284911810828121152501771)
            ·
              refine ⟨1927367716242181728752657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1284911810828121152501771 1927367716242181728752657)
              ·
                refine ⟨1445525787181636296564493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1927367716242181728752657 1445525787181636296564493)
                ·
                  refine ⟨542072170193113611211685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1445525787181636296564493 542072170193113611211685)
                  ·
                    refine ⟨101638531911208802102191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 542072170193113611211685 101638531911208802102191)
                    ·
                      rfl

theorem cell23_593821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_593821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593821 prefixEnd_593821 := by exact prefixLift 593821
  have htrace : WordTrace (prefixWord ++ tailWord_593821) baseStart_593821 baseEnd_593821 := by
    simpa [prefixWord, tailWord_593821, baseEnd_593821] using wordTrace_append hprefix tailTrace_593821
  have hstable : (prefixWord ++ tailWord_593821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593821).length < 2 ^ (prefixWord ++ tailWord_593821).sum := by decide
  have hdescent : baseEnd_593821 < baseStart_593821 := by decide
  rcases family_descends (prefixWord ++ tailWord_593821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593831 : List Nat := [1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_593831 : Nat := 118140960795 + 593831 * 2 ^ 59
def prefixEnd_593831 : Nat := 4983230072969 + 3 ^ 40 * 593831 * 2
def baseEnd_593831 : Nat := 304920730540171367181527

theorem tailTrace_593831 : CollatzResearch.WordTrace tailWord_593831 prefixEnd_593831 304920730540171367181527 := by
  unfold tailWord_593831
  simp only [CollatzResearch.WordTrace]
  refine ⟨21658795911659180105589347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14439197274439453403726231 21658795911659180105589347)
  ·
    refine ⟨32488193867488770158384021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21658795911659180105589347 32488193867488770158384021)
    ·
      refine ⟨1522884087538536101174251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32488193867488770158384021 1522884087538536101174251)
      ·
        refine ⟨2284326131307804151761377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1522884087538536101174251 2284326131307804151761377)
        ·
          refine ⟨1713244598480853113821033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2284326131307804151761377 1713244598480853113821033)
          ·
            refine ⟨1284933448860639835365775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1713244598480853113821033 1284933448860639835365775)
            ·
              refine ⟨1927400173290959753048663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1284933448860639835365775 1927400173290959753048663)
              ·
                refine ⟨2891100259936439629572995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1927400173290959753048663 2891100259936439629572995)
                ·
                  refine ⟨4336650389904659444359493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2891100259936439629572995 4336650389904659444359493)
                  ·
                    refine ⟨813121948107123645817405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4336650389904659444359493 813121948107123645817405)
                    ·
                      refine ⟨304920730540171367181527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 813121948107123645817405 304920730540171367181527)
                      ·
                        rfl

theorem cell23_593831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_593831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593831 prefixEnd_593831 := by exact prefixLift 593831
  have htrace : WordTrace (prefixWord ++ tailWord_593831) baseStart_593831 baseEnd_593831 := by
    simpa [prefixWord, tailWord_593831, baseEnd_593831] using wordTrace_append hprefix tailTrace_593831
  have hstable : (prefixWord ++ tailWord_593831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593831).length < 2 ^ (prefixWord ++ tailWord_593831).sum := by decide
  have hdescent : baseEnd_593831 < baseStart_593831 := by decide
  rcases family_descends (prefixWord ++ tailWord_593831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593854 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_593854 : Nat := 118140960795 + 593854 * 2 ^ 59
def prefixEnd_593854 : Nat := 4983230072969 + 3 ^ 40 * 593854 * 2
def baseEnd_593854 : Nat := 304932540595224777193921

theorem tailTrace_593854 : CollatzResearch.WordTrace tailWord_593854 prefixEnd_593854 304932540595224777193921 := by
  unfold tailWord_593854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2707454348821981879209577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14439756527050570022451077 2707454348821981879209577)
  ·
    refine ⟨2030590761616486409407183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2707454348821981879209577 2030590761616486409407183)
    ·
      refine ⟨3045886142424729614110775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2030590761616486409407183 3045886142424729614110775)
      ·
        refine ⟨4568829213637094421166163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3045886142424729614110775 4568829213637094421166163)
        ·
          refine ⟨6853243820455641631749245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4568829213637094421166163 6853243820455641631749245)
          ·
            refine ⟨2569966432670865611905967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6853243820455641631749245 2569966432670865611905967)
            ·
              refine ⟨3854949649006298417858951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2569966432670865611905967 3854949649006298417858951)
              ·
                refine ⟨5782424473509447626788427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3854949649006298417858951 5782424473509447626788427)
                ·
                  refine ⟨8673636710264171440182641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5782424473509447626788427 8673636710264171440182641)
                  ·
                    refine ⟨6505227532698128580136981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8673636710264171440182641 6505227532698128580136981)
                    ·
                      refine ⟨304932540595224777193921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6505227532698128580136981 304932540595224777193921)
                      ·
                        rfl

theorem cell23_593854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_593854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593854 prefixEnd_593854 := by exact prefixLift 593854
  have htrace : WordTrace (prefixWord ++ tailWord_593854) baseStart_593854 baseEnd_593854 := by
    simpa [prefixWord, tailWord_593854, baseEnd_593854] using wordTrace_append hprefix tailTrace_593854
  have hstable : (prefixWord ++ tailWord_593854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593854).length < 2 ^ (prefixWord ++ tailWord_593854).sum := by decide
  have hdescent : baseEnd_593854 < baseStart_593854 := by decide
  rcases family_descends (prefixWord ++ tailWord_593854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593904 : List Nat := [2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 5]
def baseStart_593904 : Nat := 118140960795 + 593904 * 2 ^ 59
def prefixEnd_593904 : Nat := 4983230072969 + 3 ^ 40 * 593904 * 2
def baseEnd_593904 : Nat := 304958214627949581568691

theorem tailTrace_593904 : CollatzResearch.WordTrace tailWord_593904 prefixEnd_593904 304958214627949581568691 := by
  unfold tailWord_593904
  simp only [CollatzResearch.WordTrace]
  refine ⟨10830729220197356786498383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14440972293596475715331177 10830729220197356786498383)
  ·
    refine ⟨16246093830296035179747575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10830729220197356786498383 16246093830296035179747575)
    ·
      refine ⟨24369140745444052769621363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16246093830296035179747575 24369140745444052769621363)
      ·
        refine ⟨36553711118166079154432045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24369140745444052769621363 36553711118166079154432045)
        ·
          refine ⟨13707641669312279682912017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36553711118166079154432045 13707641669312279682912017)
          ·
            refine ⟨10280731251984209762184013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13707641669312279682912017 10280731251984209762184013)
            ·
              refine ⟨3855274219494078660819005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10280731251984209762184013 3855274219494078660819005)
              ·
                refine ⟨1445727832310279497807127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3855274219494078660819005 1445727832310279497807127)
                ·
                  refine ⟨2168591748465419246710691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1445727832310279497807127 2168591748465419246710691)
                  ·
                    refine ⟨3252887622698128870066037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2168591748465419246710691 3252887622698128870066037)
                    ·
                      refine ⟨304958214627949581568691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3252887622698128870066037 304958214627949581568691)
                      ·
                        rfl

theorem cell23_593904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 5].length) (baseStart_593904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593904 prefixEnd_593904 := by exact prefixLift 593904
  have htrace : WordTrace (prefixWord ++ tailWord_593904) baseStart_593904 baseEnd_593904 := by
    simpa [prefixWord, tailWord_593904, baseEnd_593904] using wordTrace_append hprefix tailTrace_593904
  have hstable : (prefixWord ++ tailWord_593904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593904).length < 2 ^ (prefixWord ++ tailWord_593904).sum := by decide
  have hdescent : baseEnd_593904 < baseStart_593904 := by decide
  rcases family_descends (prefixWord ++ tailWord_593904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593921 : List Nat := [1, 2, 4, 1, 2, 1, 2, 2, 3, 2, 3]
def baseStart_593921 : Nat := 118140960795 + 593921 * 2 ^ 59
def prefixEnd_593921 : Nat := 4983230072969 + 3 ^ 40 * 593921 * 2
def baseEnd_593921 : Nat := 304966943799076015056113

theorem tailTrace_593921 : CollatzResearch.WordTrace tailWord_593921 prefixEnd_593921 304966943799076015056113 := by
  unfold tailWord_593921
  simp only [CollatzResearch.WordTrace]
  refine ⟨21662078481333125476365617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14441385654222083650910411 21662078481333125476365617)
  ·
    refine ⟨16246558860999844107274213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21662078481333125476365617 16246558860999844107274213)
    ·
      refine ⟨3046229786437470770113915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16246558860999844107274213 3046229786437470770113915)
      ·
        refine ⟨4569344679656206155170873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3046229786437470770113915 4569344679656206155170873)
        ·
          refine ⟨3427008509742154616378155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4569344679656206155170873 3427008509742154616378155)
          ·
            refine ⟨5140512764613231924567233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3427008509742154616378155 5140512764613231924567233)
            ·
              refine ⟨3855384573459923943425425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5140512764613231924567233 3855384573459923943425425)
              ·
                refine ⟨2891538430094942957569069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3855384573459923943425425 2891538430094942957569069)
                ·
                  refine ⟨1084326911285603609088401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2891538430094942957569069 1084326911285603609088401)
                  ·
                    refine ⟨813245183464202706816301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1084326911285603609088401 813245183464202706816301)
                    ·
                      refine ⟨304966943799076015056113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 813245183464202706816301 304966943799076015056113)
                      ·
                        rfl

theorem cell23_593921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_593921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593921 prefixEnd_593921 := by exact prefixLift 593921
  have htrace : WordTrace (prefixWord ++ tailWord_593921) baseStart_593921 baseEnd_593921 := by
    simpa [prefixWord, tailWord_593921, baseEnd_593921] using wordTrace_append hprefix tailTrace_593921
  have hstable : (prefixWord ++ tailWord_593921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593921).length < 2 ^ (prefixWord ++ tailWord_593921).sum := by decide
  have hdescent : baseEnd_593921 < baseStart_593921 := by decide
  rcases family_descends (prefixWord ++ tailWord_593921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593951 : List Nat := [1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 3]
def baseStart_593951 : Nat := 118140960795 + 593951 * 2 ^ 59
def prefixEnd_593951 : Nat := 4983230072969 + 3 ^ 40 * 593951 * 2
def baseEnd_593951 : Nat := 304982348218710897680975

theorem tailTrace_593951 : CollatzResearch.WordTrace tailWord_593951 prefixEnd_593951 304982348218710897680975 := by
  unfold tailWord_593951
  simp only [CollatzResearch.WordTrace]
  refine ⟨21663172671224440599957707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14442115114149627066638471 21663172671224440599957707)
  ·
    refine ⟨32494759006836660899936561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21663172671224440599957707 32494759006836660899936561)
    ·
      refine ⟨24371069255127495674952421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32494759006836660899936561 24371069255127495674952421)
      ·
        refine ⟨4569575485336405439053579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24371069255127495674952421 4569575485336405439053579)
        ·
          refine ⟨6854363228004608158580369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4569575485336405439053579 6854363228004608158580369)
          ·
            refine ⟨5140772421003456118935277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6854363228004608158580369 5140772421003456118935277)
            ·
              refine ⟨1927789657876296044600729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5140772421003456118935277 1927789657876296044600729)
              ·
                refine ⟨1445842243407222033450547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1927789657876296044600729 1445842243407222033450547)
                ·
                  refine ⟨2168763365110833050175821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1445842243407222033450547 2168763365110833050175821)
                  ·
                    refine ⟨813286261916562393815933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2168763365110833050175821 813286261916562393815933)
                    ·
                      refine ⟨304982348218710897680975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 813286261916562393815933 304982348218710897680975)
                      ·
                        rfl

theorem cell23_593951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_593951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593951 prefixEnd_593951 := by exact prefixLift 593951
  have htrace : WordTrace (prefixWord ++ tailWord_593951) baseStart_593951 baseEnd_593951 := by
    simpa [prefixWord, tailWord_593951, baseEnd_593951] using wordTrace_append hprefix tailTrace_593951
  have hstable : (prefixWord ++ tailWord_593951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593951).length < 2 ^ (prefixWord ++ tailWord_593951).sum := by decide
  have hdescent : baseEnd_593951 < baseStart_593951 := by decide
  rcases family_descends (prefixWord ++ tailWord_593951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593968 : List Nat := [2, 1, 1, 1, 2, 5, 1, 4, 2, 1, 3]
def baseStart_593968 : Nat := 118140960795 + 593968 * 2 ^ 59
def prefixEnd_593968 : Nat := 4983230072969 + 3 ^ 40 * 593968 * 2
def baseEnd_593968 : Nat := 304991077389837331168397

theorem tailTrace_593968 : CollatzResearch.WordTrace tailWord_593968 prefixEnd_593968 304991077389837331168397 := by
  unfold tailWord_593968
  simp only [CollatzResearch.WordTrace]
  refine ⟨10831896356081426251663279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14442528474775235002217705 10831896356081426251663279)
  ·
    refine ⟨16247844534122139377494919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10831896356081426251663279 16247844534122139377494919)
    ·
      refine ⟨24371766801183209066242379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16247844534122139377494919 24371766801183209066242379)
      ·
        refine ⟨36557650201774813599363569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24371766801183209066242379 36557650201774813599363569)
        ·
          refine ⟨27418237651331110199522677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36557650201774813599363569 27418237651331110199522677)
          ·
            refine ⟨2570459779812291581205251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27418237651331110199522677 2570459779812291581205251)
            ·
              refine ⟨3855689669718437371807877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2570459779812291581205251 3855689669718437371807877)
              ·
                refine ⟨722941813072207007213977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3855689669718437371807877 722941813072207007213977)
                ·
                  refine ⟨542206359804155255410483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 722941813072207007213977 542206359804155255410483)
                  ·
                    refine ⟨813309539706232883115725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 542206359804155255410483 813309539706232883115725)
                    ·
                      refine ⟨304991077389837331168397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 813309539706232883115725 304991077389837331168397)
                      ·
                        rfl

theorem cell23_593968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 2, 1, 3].length) (baseStart_593968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593968 prefixEnd_593968 := by exact prefixLift 593968
  have htrace : WordTrace (prefixWord ++ tailWord_593968) baseStart_593968 baseEnd_593968 := by
    simpa [prefixWord, tailWord_593968, baseEnd_593968] using wordTrace_append hprefix tailTrace_593968
  have hstable : (prefixWord ++ tailWord_593968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593968).length < 2 ^ (prefixWord ++ tailWord_593968).sum := by decide
  have hdescent : baseEnd_593968 < baseStart_593968 := by decide
  rcases family_descends (prefixWord ++ tailWord_593968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593969 : List Nat := [1, 2, 2, 3, 1, 5, 2, 2, 1, 2, 2]
def baseStart_593969 : Nat := 118140960795 + 593969 * 2 ^ 59
def prefixEnd_593969 : Nat := 4983230072969 + 3 ^ 40 * 593969 * 2
def baseEnd_593969 : Nat := 304991590870491827255893

theorem tailTrace_593969 : CollatzResearch.WordTrace tailWord_593969 prefixEnd_593969 304991590870491827255893 := by
  unfold tailWord_593969
  simp only [CollatzResearch.WordTrace]
  refine ⟨21663829185159229674112961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14442552790106153116075307 21663829185159229674112961)
  ·
    refine ⟨16247871888869422255584721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21663829185159229674112961 16247871888869422255584721)
    ·
      refine ⟨12185903916652066691688541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16247871888869422255584721 12185903916652066691688541)
      ·
        refine ⟨4569713968744525009383203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12185903916652066691688541 4569713968744525009383203)
        ·
          refine ⟨6854570953116787514074805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4569713968744525009383203 6854570953116787514074805)
          ·
            refine ⟨642616026854698829444513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6854570953116787514074805 642616026854698829444513)
            ·
              refine ⟨481962020141024122083385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 642616026854698829444513 481962020141024122083385)
              ·
                refine ⟨361471515105768091562539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 481962020141024122083385 361471515105768091562539)
                ·
                  refine ⟨542207272658652137343809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 361471515105768091562539 542207272658652137343809)
                  ·
                    refine ⟨406655454493989103007857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 542207272658652137343809 406655454493989103007857)
                    ·
                      refine ⟨304991590870491827255893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 406655454493989103007857 304991590870491827255893)
                      ·
                        rfl

theorem cell23_593969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_593969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593969 prefixEnd_593969 := by exact prefixLift 593969
  have htrace : WordTrace (prefixWord ++ tailWord_593969) baseStart_593969 baseEnd_593969 := by
    simpa [prefixWord, tailWord_593969, baseEnd_593969] using wordTrace_append hprefix tailTrace_593969
  have hstable : (prefixWord ++ tailWord_593969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593969).length < 2 ^ (prefixWord ++ tailWord_593969).sum := by decide
  have hdescent : baseEnd_593969 < baseStart_593969 := by decide
  rcases family_descends (prefixWord ++ tailWord_593969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593984 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 1, 8]
def baseStart_593984 : Nat := 118140960795 + 593984 * 2 ^ 59
def prefixEnd_593984 : Nat := 4983230072969 + 3 ^ 40 * 593984 * 2
def baseEnd_593984 : Nat := 101666431026769756189441

theorem tailTrace_593984 : CollatzResearch.WordTrace tailWord_593984 prefixEnd_593984 101666431026769756189441 := by
  unfold tailWord_593984
  simp only [CollatzResearch.WordTrace]
  refine ⟨10832188140052443617954503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14442917520069924823939337 10832188140052443617954503)
  ·
    refine ⟨16248282210078665426931755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10832188140052443617954503 16248282210078665426931755)
    ·
      refine ⟨24372423315117998140397633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16248282210078665426931755 24372423315117998140397633)
      ·
        refine ⟨18279317486338498605298225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24372423315117998140397633 18279317486338498605298225)
        ·
          refine ⟨13709488114753873953973669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18279317486338498605298225 13709488114753873953973669)
          ·
            refine ⟨2570529021516351366370063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13709488114753873953973669 2570529021516351366370063)
            ·
              refine ⟨3855793532274527049555095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2570529021516351366370063 3855793532274527049555095)
              ·
                refine ⟨5783690298411790574332643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3855793532274527049555095 5783690298411790574332643)
                ·
                  refine ⟨8675535447617685861498965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5783690298411790574332643 8675535447617685861498965)
                  ·
                    refine ⟨101666431026769756189441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8675535447617685861498965 101666431026769756189441)
                    ·
                      rfl

theorem cell23_593984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 1, 8].length) (baseStart_593984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593984 prefixEnd_593984 := by exact prefixLift 593984
  have htrace : WordTrace (prefixWord ++ tailWord_593984) baseStart_593984 baseEnd_593984 := by
    simpa [prefixWord, tailWord_593984, baseEnd_593984] using wordTrace_append hprefix tailTrace_593984
  have hstable : (prefixWord ++ tailWord_593984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593984).length < 2 ^ (prefixWord ++ tailWord_593984).sum := by decide
  have hdescent : baseEnd_593984 < baseStart_593984 := by decide
  rcases family_descends (prefixWord ++ tailWord_593984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593985 : List Nat := [1, 2, 5, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_593985 : Nat := 118140960795 + 593985 * 2 ^ 59
def prefixEnd_593985 : Nat := 4983230072969 + 3 ^ 40 * 593985 * 2
def baseEnd_593985 : Nat := 304999806560963764655819

theorem tailTrace_593985 : CollatzResearch.WordTrace tailWord_593985 prefixEnd_593985 304999806560963764655819 := by
  unfold tailWord_593985
  simp only [CollatzResearch.WordTrace]
  refine ⟨21664412753101264406695409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14442941835400842937796939 21664412753101264406695409)
  ·
    refine ⟨16248309564825948305021557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21664412753101264406695409 16248309564825948305021557)
    ·
      refine ⟨1523279021702432653595771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16248309564825948305021557 1523279021702432653595771)
      ·
        refine ⟨2284918532553648980393657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1523279021702432653595771 2284918532553648980393657)
        ·
          refine ⟨1713688899415236735295243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2284918532553648980393657 1713688899415236735295243)
          ·
            refine ⟨2570533349122855102942865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1713688899415236735295243 2570533349122855102942865)
            ·
              refine ⟨1927900011842141327207149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2570533349122855102942865 1927900011842141327207149)
              ·
                refine ⟨722962504440802997702681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1927900011842141327207149 722962504440802997702681)
                ·
                  refine ⟨542221878330602248277011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 722962504440802997702681 542221878330602248277011)
                  ·
                    refine ⟨813332817495903372415517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 542221878330602248277011 813332817495903372415517)
                    ·
                      refine ⟨304999806560963764655819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 813332817495903372415517 304999806560963764655819)
                      ·
                        rfl

theorem cell23_593985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_593985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_593985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_593985 prefixEnd_593985 := by exact prefixLift 593985
  have htrace : WordTrace (prefixWord ++ tailWord_593985) baseStart_593985 baseEnd_593985 := by
    simpa [prefixWord, tailWord_593985, baseEnd_593985] using wordTrace_append hprefix tailTrace_593985
  have hstable : (prefixWord ++ tailWord_593985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593985).length < 2 ^ (prefixWord ++ tailWord_593985).sum := by decide
  have hdescent : baseEnd_593985 < baseStart_593985 := by decide
  rcases family_descends (prefixWord ++ tailWord_593985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594008 : List Nat := [2, 1, 2, 2, 1, 4, 2, 2, 1, 4, 2]
def baseStart_594008 : Nat := 118140960795 + 594008 * 2 ^ 59
def prefixEnd_594008 : Nat := 4983230072969 + 3 ^ 40 * 594008 * 2
def baseEnd_594008 : Nat := 305011616616017174668213

theorem tailTrace_594008 : CollatzResearch.WordTrace tailWord_594008 prefixEnd_594008 305011616616017174668213 := by
  unfold tailWord_594008
  simp only [CollatzResearch.WordTrace]
  refine ⟨10832625816008969667391339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14443501088011959556521785 10832625816008969667391339)
  ·
    refine ⟨16248938724013454501087009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10832625816008969667391339 16248938724013454501087009)
    ·
      refine ⟨12186704043010090875815257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16248938724013454501087009 12186704043010090875815257)
      ·
        refine ⟨9140028032257568156861443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12186704043010090875815257 9140028032257568156861443)
        ·
          refine ⟨13710042048386352235292165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9140028032257568156861443 13710042048386352235292165)
          ·
            refine ⟨2570632884072441044117281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13710042048386352235292165 2570632884072441044117281)
            ·
              refine ⟨1927974663054330783087961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2570632884072441044117281 1927974663054330783087961)
              ·
                refine ⟨1445980997290748087315971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1927974663054330783087961 1445980997290748087315971)
                ·
                  refine ⟨2168971495936122130973957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1445980997290748087315971 2168971495936122130973957)
                  ·
                    refine ⟨406682155488022899557617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2168971495936122130973957 406682155488022899557617)
                    ·
                      refine ⟨305011616616017174668213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 406682155488022899557617 305011616616017174668213)
                      ·
                        rfl

theorem cell23_594008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 1, 4, 2].length) (baseStart_594008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594008 prefixEnd_594008 := by exact prefixLift 594008
  have htrace : WordTrace (prefixWord ++ tailWord_594008) baseStart_594008 baseEnd_594008 := by
    simpa [prefixWord, tailWord_594008, baseEnd_594008] using wordTrace_append hprefix tailTrace_594008
  have hstable : (prefixWord ++ tailWord_594008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594008).length < 2 ^ (prefixWord ++ tailWord_594008).sum := by decide
  have hdescent : baseEnd_594008 < baseStart_594008 := by decide
  rcases family_descends (prefixWord ++ tailWord_594008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594012 : List Nat := [2, 2, 4, 1, 1, 2, 4, 1, 1, 3, 2]
def baseStart_594012 : Nat := 118140960795 + 594012 * 2 ^ 59
def prefixEnd_594012 : Nat := 4983230072969 + 3 ^ 40 * 594012 * 2
def baseEnd_594012 : Nat := 305013670538635159018195

theorem tailTrace_594012 : CollatzResearch.WordTrace tailWord_594012 prefixEnd_594012 305013670538635159018195 := by
  unfold tailWord_594012
  simp only [CollatzResearch.WordTrace]
  refine ⟨10832698762001724008964145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14443598349335632011952193 10832698762001724008964145)
  ·
    refine ⟨8124524071501293006723109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10832698762001724008964145 8124524071501293006723109)
    ·
      refine ⟨1523348263406492438760583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8124524071501293006723109 1523348263406492438760583)
      ·
        refine ⟨2285022395109738658140875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1523348263406492438760583 2285022395109738658140875)
        ·
          refine ⟨3427533592664607987211313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2285022395109738658140875 3427533592664607987211313)
          ·
            refine ⟨2570650194498455990408485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3427533592664607987211313 2570650194498455990408485)
            ·
              refine ⟨481996911468460498201591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2570650194498455990408485 481996911468460498201591)
              ·
                refine ⟨722995367202690747302387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 481996911468460498201591 722995367202690747302387)
                ·
                  refine ⟨1084493050804036120953581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 722995367202690747302387 1084493050804036120953581)
                  ·
                    refine ⟨406684894051513545357593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1084493050804036120953581 406684894051513545357593)
                    ·
                      refine ⟨305013670538635159018195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 406684894051513545357593 305013670538635159018195)
                      ·
                        rfl

theorem cell23_594012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_594012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594012 prefixEnd_594012 := by exact prefixLift 594012
  have htrace : WordTrace (prefixWord ++ tailWord_594012) baseStart_594012 baseEnd_594012 := by
    simpa [prefixWord, tailWord_594012, baseEnd_594012] using wordTrace_append hprefix tailTrace_594012
  have hstable : (prefixWord ++ tailWord_594012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594012).length < 2 ^ (prefixWord ++ tailWord_594012).sum := by decide
  have hdescent : baseEnd_594012 < baseStart_594012 := by decide
  rcases family_descends (prefixWord ++ tailWord_594012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594021 : List Nat := [1, 3, 1, 3, 2, 2, 1, 2, 2, 2, 4]
def baseStart_594021 : Nat := 118140960795 + 594021 * 2 ^ 59
def prefixEnd_594021 : Nat := 4983230072969 + 3 ^ 40 * 594021 * 2
def baseEnd_594021 : Nat := 305018291864525623805653

theorem tailTrace_594021 : CollatzResearch.WordTrace tailWord_594021 prefixEnd_594021 305018291864525623805653 := by
  unfold tailWord_594021
  simp only [CollatzResearch.WordTrace]
  refine ⟨21665725780970842555005917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14443817187313895036670611 21665725780970842555005917)
  ·
    refine ⟨8124647167864065958127219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21665725780970842555005917 8124647167864065958127219)
    ·
      refine ⟨12186970751796098937190829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8124647167864065958127219 12186970751796098937190829)
      ·
        refine ⟨4570114031923537101446561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12186970751796098937190829 4570114031923537101446561)
        ·
          refine ⟨3427585523942652826084921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4570114031923537101446561 3427585523942652826084921)
          ·
            refine ⟨2570689142956989619563691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3427585523942652826084921 2570689142956989619563691)
            ·
              refine ⟨3856033714435484429345537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2570689142956989619563691 3856033714435484429345537)
              ·
                refine ⟨2892025285826613322009153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3856033714435484429345537 2892025285826613322009153)
                ·
                  refine ⟨2169018964369959991506865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2892025285826613322009153 2169018964369959991506865)
                  ·
                    refine ⟨1626764223277469993630149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2169018964369959991506865 1626764223277469993630149)
                    ·
                      refine ⟨305018291864525623805653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1626764223277469993630149 305018291864525623805653)
                      ·
                        rfl

theorem cell23_594021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_594021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594021 prefixEnd_594021 := by exact prefixLift 594021
  have htrace : WordTrace (prefixWord ++ tailWord_594021) baseStart_594021 baseEnd_594021 := by
    simpa [prefixWord, tailWord_594021, baseEnd_594021] using wordTrace_append hprefix tailTrace_594021
  have hstable : (prefixWord ++ tailWord_594021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594021).length < 2 ^ (prefixWord ++ tailWord_594021).sum := by decide
  have hdescent : baseEnd_594021 < baseStart_594021 := by decide
  rcases family_descends (prefixWord ++ tailWord_594021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594031 : List Nat := [1, 1, 2, 1, 3, 5, 2, 1, 7]
def baseStart_594031 : Nat := 118140960795 + 594031 * 2 ^ 59
def prefixEnd_594031 : Nat := 4983230072969 + 3 ^ 40 * 594031 * 2
def baseEnd_594031 : Nat := 33891491852341176075623

theorem tailTrace_594031 : CollatzResearch.WordTrace tailWord_594031 prefixEnd_594031 33891491852341176075623 := by
  unfold tailWord_594031
  simp only [CollatzResearch.WordTrace]
  refine ⟨21666090510934614262869947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14444060340623076175246631 21666090510934614262869947)
  ·
    refine ⟨32499135766401921394304921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21666090510934614262869947 32499135766401921394304921)
    ·
      refine ⟨24374351824801441045728691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32499135766401921394304921 24374351824801441045728691)
      ·
        refine ⟨36561527737202161568593037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24374351824801441045728691 36561527737202161568593037)
        ·
          refine ⟨13710572901450810588222389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36561527737202161568593037 13710572901450810588222389)
          ·
            refine ⟨1285366209511013492645849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13710572901450810588222389 1285366209511013492645849)
            ·
              refine ⟨964024657133260119484387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1285366209511013492645849 964024657133260119484387)
              ·
                refine ⟨1446036985699890179226581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 964024657133260119484387 1446036985699890179226581)
                ·
                  refine ⟨33891491852341176075623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1446036985699890179226581 33891491852341176075623)
                  ·
                    rfl

theorem cell23_594031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 7].length) (baseStart_594031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594031 prefixEnd_594031 := by exact prefixLift 594031
  have htrace : WordTrace (prefixWord ++ tailWord_594031) baseStart_594031 baseEnd_594031 := by
    simpa [prefixWord, tailWord_594031, baseEnd_594031] using wordTrace_append hprefix tailTrace_594031
  have hstable : (prefixWord ++ tailWord_594031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594031).length < 2 ^ (prefixWord ++ tailWord_594031).sum := by decide
  have hdescent : baseEnd_594031 < baseStart_594031 := by decide
  rcases family_descends (prefixWord ++ tailWord_594031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594038 : List Nat := [5, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_594038 : Nat := 118140960795 + 594038 * 2 ^ 59
def prefixEnd_594038 : Nat := 4983230072969 + 3 ^ 40 * 594038 * 2
def baseEnd_594038 : Nat := 305027021035652057293075

theorem tailTrace_594038 : CollatzResearch.WordTrace tailWord_594038 prefixEnd_594038 305027021035652057293075 := by
  unfold tailWord_594038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1354146613869328403648423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14444230547939502972249845 1354146613869328403648423)
  ·
    refine ⟨2031219920803992605472635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1354146613869328403648423 2031219920803992605472635)
    ·
      refine ⟨3046829881205988908208953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2031219920803992605472635 3046829881205988908208953)
      ·
        refine ⟨2285122410904491681156715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3046829881205988908208953 2285122410904491681156715)
        ·
          refine ⟨3427683616356737521735073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2285122410904491681156715 3427683616356737521735073)
          ·
            refine ⟨2570762712267553141301305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3427683616356737521735073 2570762712267553141301305)
            ·
              refine ⟨1928072034200664855975979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2570762712267553141301305 1928072034200664855975979)
              ·
                refine ⟨2892108051300997283963969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1928072034200664855975979 2892108051300997283963969)
                ·
                  refine ⟨2169081038475747962972977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2892108051300997283963969 2169081038475747962972977)
                  ·
                    refine ⟨1626810778856810972229733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2169081038475747962972977 1626810778856810972229733)
                    ·
                      refine ⟨305027021035652057293075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1626810778856810972229733 305027021035652057293075)
                      ·
                        rfl

theorem cell23_594038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_594038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594038 prefixEnd_594038 := by exact prefixLift 594038
  have htrace : WordTrace (prefixWord ++ tailWord_594038) baseStart_594038 baseEnd_594038 := by
    simpa [prefixWord, tailWord_594038, baseEnd_594038] using wordTrace_append hprefix tailTrace_594038
  have hstable : (prefixWord ++ tailWord_594038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594038).length < 2 ^ (prefixWord ++ tailWord_594038).sum := by decide
  have hdescent : baseEnd_594038 < baseStart_594038 := by decide
  rcases family_descends (prefixWord ++ tailWord_594038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594082 : List Nat := [3, 3, 1, 3, 1, 2, 3, 2, 5]
def baseStart_594082 : Nat := 118140960795 + 594082 * 2 ^ 59
def prefixEnd_594082 : Nat := 4983230072969 + 3 ^ 40 * 594082 * 2
def baseEnd_594082 : Nat := 33894401576049987238097

theorem tailTrace_594082 : CollatzResearch.WordTrace tailWord_594082 prefixEnd_594082 33894401576049987238097 := by
  unfold tailWord_594082
  simp only [CollatzResearch.WordTrace]
  refine ⟨5416987658437462493244125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14445300422499899981984333 5416987658437462493244125)
  ·
    refine ⟨2031370371914048434966547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5416987658437462493244125 2031370371914048434966547)
    ·
      refine ⟨3047055557871072652449821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2031370371914048434966547 3047055557871072652449821)
      ·
        refine ⟨1142645834201652244668683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3047055557871072652449821 1142645834201652244668683)
        ·
          refine ⟨1713968751302478367003025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1142645834201652244668683 1713968751302478367003025)
          ·
            refine ⟨1285476563476858775252269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1713968751302478367003025 1285476563476858775252269)
            ·
              refine ⟨482053711303822040719601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1285476563476858775252269 482053711303822040719601)
              ·
                refine ⟨361540283477866530539701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 482053711303822040719601 361540283477866530539701)
                ·
                  refine ⟨33894401576049987238097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 361540283477866530539701 33894401576049987238097)
                  ·
                    rfl

theorem cell23_594082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_594082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594082 prefixEnd_594082 := by exact prefixLift 594082
  have htrace : WordTrace (prefixWord ++ tailWord_594082) baseStart_594082 baseEnd_594082 := by
    simpa [prefixWord, tailWord_594082, baseEnd_594082] using wordTrace_append hprefix tailTrace_594082
  have hstable : (prefixWord ++ tailWord_594082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594082).length < 2 ^ (prefixWord ++ tailWord_594082).sum := by decide
  have hdescent : baseEnd_594082 < baseStart_594082 := by decide
  rcases family_descends (prefixWord ++ tailWord_594082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594098 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2]
def baseStart_594098 : Nat := 118140960795 + 594098 * 2 ^ 59
def prefixEnd_594098 : Nat := 4983230072969 + 3 ^ 40 * 594098 * 2
def baseEnd_594098 : Nat := 305057829874921822542799

theorem tailTrace_594098 : CollatzResearch.WordTrace tailWord_594098 prefixEnd_594098 305057829874921822542799 := by
  unfold tailWord_594098
  simp only [CollatzResearch.WordTrace]
  refine ⟨5417133550422971176389737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14445689467794589803705965 5417133550422971176389737)
  ·
    refine ⟨4062850162817228382292303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5417133550422971176389737 4062850162817228382292303)
    ·
      refine ⟨6094275244225842573438455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4062850162817228382292303 6094275244225842573438455)
      ·
        refine ⟨9141412866338763860157683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6094275244225842573438455 9141412866338763860157683)
        ·
          refine ⟨13712119299508145790236525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9141412866338763860157683 13712119299508145790236525)
          ·
            refine ⟨5142044737315554671338697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13712119299508145790236525 5142044737315554671338697)
            ·
              refine ⟨3856533552986666003504023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5142044737315554671338697 3856533552986666003504023)
              ·
                refine ⟨5784800329479999005256035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3856533552986666003504023 5784800329479999005256035)
                ·
                  refine ⟨8677200494219998507884053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5784800329479999005256035 8677200494219998507884053)
                  ·
                    refine ⟨406743773166562430057065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8677200494219998507884053 406743773166562430057065)
                    ·
                      refine ⟨305057829874921822542799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 406743773166562430057065 305057829874921822542799)
                      ·
                        rfl

theorem cell23_594098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2].length) (baseStart_594098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594098 prefixEnd_594098 := by exact prefixLift 594098
  have htrace : WordTrace (prefixWord ++ tailWord_594098) baseStart_594098 baseEnd_594098 := by
    simpa [prefixWord, tailWord_594098, baseEnd_594098] using wordTrace_append hprefix tailTrace_594098
  have hstable : (prefixWord ++ tailWord_594098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594098).length < 2 ^ (prefixWord ++ tailWord_594098).sum := by decide
  have hdescent : baseEnd_594098 < baseStart_594098 := by decide
  rcases family_descends (prefixWord ++ tailWord_594098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594181 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 3, 6]
def baseStart_594181 : Nat := 118140960795 + 594181 * 2 ^ 59
def prefixEnd_594181 : Nat := 4983230072969 + 3 ^ 40 * 594181 * 2
def baseEnd_594181 : Nat := 101700149589748332601639

theorem tailTrace_594181 : CollatzResearch.WordTrace tailWord_594181 prefixEnd_594181 101700149589748332601639 := by
  unfold tailWord_594181
  simp only [CollatzResearch.WordTrace]
  refine ⟨21671561460391189880830397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14447707640260793253886931 21671561460391189880830397)
  ·
    refine ⟨8126835547646696205311399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21671561460391189880830397 8126835547646696205311399)
    ·
      refine ⟨12190253321470044307967099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8126835547646696205311399 12190253321470044307967099)
      ·
        refine ⟨18285379982205066461950649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12190253321470044307967099 18285379982205066461950649)
        ·
          refine ⟨13714034986653799846462987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18285379982205066461950649 13714034986653799846462987)
          ·
            refine ⟨20571052479980699769694481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13714034986653799846462987 20571052479980699769694481)
            ·
              refine ⟨15428289359985524827270861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20571052479980699769694481 15428289359985524827270861)
              ·
                refine ⟨5785608509994571810226573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15428289359985524827270861 5785608509994571810226573)
                ·
                  refine ⟨2169603191247964428834965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5785608509994571810226573 2169603191247964428834965)
                  ·
                    refine ⟨101700149589748332601639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2169603191247964428834965 101700149589748332601639)
                    ·
                      rfl

theorem cell23_594181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_594181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594181 prefixEnd_594181 := by exact prefixLift 594181
  have htrace : WordTrace (prefixWord ++ tailWord_594181) baseStart_594181 baseEnd_594181 := by
    simpa [prefixWord, tailWord_594181, baseEnd_594181] using wordTrace_append hprefix tailTrace_594181
  have hstable : (prefixWord ++ tailWord_594181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594181).length < 2 ^ (prefixWord ++ tailWord_594181).sum := by decide
  have hdescent : baseEnd_594181 < baseStart_594181 := by decide
  rcases family_descends (prefixWord ++ tailWord_594181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594185 : List Nat := [1, 2, 1, 1, 3, 4, 4, 1, 1, 5]
def baseStart_594185 : Nat := 118140960795 + 594185 * 2 ^ 59
def prefixEnd_594185 : Nat := 4983230072969 + 3 ^ 40 * 594185 * 2
def baseEnd_594185 : Nat := 101700834230620994051633

theorem tailTrace_594185 : CollatzResearch.WordTrace tailWord_594185 prefixEnd_594185 101700834230620994051633 := by
  unfold tailWord_594185
  simp only [CollatzResearch.WordTrace]
  refine ⟨21671707352376698563976009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14447804901584465709317339 21671707352376698563976009)
  ·
    refine ⟨16253780514282523922982007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21671707352376698563976009 16253780514282523922982007)
    ·
      refine ⟨24380670771423785884473011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16253780514282523922982007 24380670771423785884473011)
      ·
        refine ⟨36571006157135678826709517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24380670771423785884473011 36571006157135678826709517)
        ·
          refine ⟨13714127308925879560016069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36571006157135678826709517 13714127308925879560016069)
          ·
            refine ⟨2571398870423602417503013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13714127308925879560016069 2571398870423602417503013)
            ·
              refine ⟨482137288204425453281815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2571398870423602417503013 482137288204425453281815)
              ·
                refine ⟨723205932306638179922723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 482137288204425453281815 723205932306638179922723)
                ·
                  refine ⟨1084808898459957269884085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 723205932306638179922723 1084808898459957269884085)
                  ·
                    refine ⟨101700834230620994051633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1084808898459957269884085 101700834230620994051633)
                    ·
                      rfl

theorem cell23_594185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 1, 5].length) (baseStart_594185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594185 prefixEnd_594185 := by exact prefixLift 594185
  have htrace : WordTrace (prefixWord ++ tailWord_594185) baseStart_594185 baseEnd_594185 := by
    simpa [prefixWord, tailWord_594185, baseEnd_594185] using wordTrace_append hprefix tailTrace_594185
  have hstable : (prefixWord ++ tailWord_594185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594185).length < 2 ^ (prefixWord ++ tailWord_594185).sum := by decide
  have hdescent : baseEnd_594185 < baseStart_594185 := by decide
  rcases family_descends (prefixWord ++ tailWord_594185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594191 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 5]
def baseStart_594191 : Nat := 118140960795 + 594191 * 2 ^ 59
def prefixEnd_594191 : Nat := 4983230072969 + 3 ^ 40 * 594191 * 2
def baseEnd_594191 : Nat := 305105583575789958679871

theorem tailTrace_594191 : CollatzResearch.WordTrace tailWord_594191 prefixEnd_594191 305105583575789958679871 := by
  unfold tailWord_594191
  simp only [CollatzResearch.WordTrace]
  refine ⟨21671926190354961588694427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14447950793569974392462951 21671926190354961588694427)
  ·
    refine ⟨32507889285532442383041641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21671926190354961588694427 32507889285532442383041641)
    ·
      refine ⟨24380916964149331787281231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32507889285532442383041641 24380916964149331787281231)
      ·
        refine ⟨36571375446223997680921847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24380916964149331787281231 36571375446223997680921847)
        ·
          refine ⟨54857063169335996521382771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36571375446223997680921847 54857063169335996521382771)
          ·
            refine ⟨82285594754003994782074157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54857063169335996521382771 82285594754003994782074157)
            ·
              refine ⟨30857098032751498043277809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82285594754003994782074157 30857098032751498043277809)
              ·
                refine ⟨23142823524563623532458357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30857098032751498043277809 23142823524563623532458357)
                ·
                  refine ⟨2169639705427839706167971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23142823524563623532458357 2169639705427839706167971)
                  ·
                    refine ⟨3254459558141759559251957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2169639705427839706167971 3254459558141759559251957)
                    ·
                      refine ⟨305105583575789958679871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3254459558141759559251957 305105583575789958679871)
                      ·
                        rfl

theorem cell23_594191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 5].length) (baseStart_594191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594191 prefixEnd_594191 := by exact prefixLift 594191
  have htrace : WordTrace (prefixWord ++ tailWord_594191) baseStart_594191 baseEnd_594191 := by
    simpa [prefixWord, tailWord_594191, baseEnd_594191] using wordTrace_append hprefix tailTrace_594191
  have hstable : (prefixWord ++ tailWord_594191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594191).length < 2 ^ (prefixWord ++ tailWord_594191).sum := by decide
  have hdescent : baseEnd_594191 < baseStart_594191 := by decide
  rcases family_descends (prefixWord ++ tailWord_594191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594201 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 1, 8, 4]
def baseStart_594201 : Nat := 118140960795 + 594201 * 2 ^ 59
def prefixEnd_594201 : Nat := 4983230072969 + 3 ^ 40 * 594201 * 2
def baseEnd_594201 : Nat := 305110718382334919554825

theorem tailTrace_594201 : CollatzResearch.WordTrace tailWord_594201 prefixEnd_594201 305110718382334919554825 := by
  unfold tailWord_594201
  simp only [CollatzResearch.WordTrace]
  refine ⟨21672290920318733296558457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14448193946879155531038971 21672290920318733296558457)
  ·
    refine ⟨16254218190239049972418843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21672290920318733296558457 16254218190239049972418843)
    ·
      refine ⟨24381327285358574958628265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16254218190239049972418843 24381327285358574958628265)
      ·
        refine ⟨18285995464018931218971199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24381327285358574958628265 18285995464018931218971199)
        ·
          refine ⟨27428993196028396828456799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18285995464018931218971199 27428993196028396828456799)
          ·
            refine ⟨41143489794042595242685199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27428993196028396828456799 41143489794042595242685199)
            ·
              refine ⟨61715234691063892864027799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41143489794042595242685199 61715234691063892864027799)
              ·
                refine ⟨92572852036595839296041699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61715234691063892864027799 92572852036595839296041699)
                ·
                  refine ⟨138859278054893758944062549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92572852036595839296041699 138859278054893758944062549)
                  ·
                    refine ⟨1627257164705786237625733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 138859278054893758944062549 1627257164705786237625733)
                    ·
                      refine ⟨305110718382334919554825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1627257164705786237625733 305110718382334919554825)
                      ·
                        rfl

theorem cell23_594201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_594201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594201 prefixEnd_594201 := by exact prefixLift 594201
  have htrace : WordTrace (prefixWord ++ tailWord_594201) baseStart_594201 baseEnd_594201 := by
    simpa [prefixWord, tailWord_594201, baseEnd_594201] using wordTrace_append hprefix tailTrace_594201
  have hstable : (prefixWord ++ tailWord_594201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594201).length < 2 ^ (prefixWord ++ tailWord_594201).sum := by decide
  have hdescent : baseEnd_594201 < baseStart_594201 := by decide
  rcases family_descends (prefixWord ++ tailWord_594201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594208 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 5]
def baseStart_594208 : Nat := 118140960795 + 594208 * 2 ^ 59
def prefixEnd_594208 : Nat := 4983230072969 + 3 ^ 40 * 594208 * 2
def baseEnd_594208 : Nat := 305114312746916392167293

theorem tailTrace_594208 : CollatzResearch.WordTrace tailWord_594208 prefixEnd_594208 305114312746916392167293 := by
  unfold tailWord_594208
  simp only [CollatzResearch.WordTrace]
  refine ⟨10836273115646686746031639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14448364154195582328042185 10836273115646686746031639)
  ·
    refine ⟨16254409673470030119047459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10836273115646686746031639 16254409673470030119047459)
    ·
      refine ⟨24381614510205045178571189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16254409673470030119047459 24381614510205045178571189)
      ·
        refine ⟨2285776360331722985491049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24381614510205045178571189 2285776360331722985491049)
        ·
          refine ⟨1714332270248792239118287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2285776360331722985491049 1714332270248792239118287)
          ·
            refine ⟨2571498405373188358677431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1714332270248792239118287 2571498405373188358677431)
            ·
              refine ⟨3857247608059782538016147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2571498405373188358677431 3857247608059782538016147)
              ·
                refine ⟨5785871412089673807024221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3857247608059782538016147 5785871412089673807024221)
                ·
                  refine ⟨2169701779533627677634083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5785871412089673807024221 2169701779533627677634083)
                  ·
                    refine ⟨3254552669300441516451125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2169701779533627677634083 3254552669300441516451125)
                    ·
                      refine ⟨305114312746916392167293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3254552669300441516451125 305114312746916392167293)
                      ·
                        rfl

theorem cell23_594208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_594208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594208 prefixEnd_594208 := by exact prefixLift 594208
  have htrace : WordTrace (prefixWord ++ tailWord_594208) baseStart_594208 baseEnd_594208 := by
    simpa [prefixWord, tailWord_594208, baseEnd_594208] using wordTrace_append hprefix tailTrace_594208
  have hstable : (prefixWord ++ tailWord_594208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594208).length < 2 ^ (prefixWord ++ tailWord_594208).sum := by decide
  have hdescent : baseEnd_594208 < baseStart_594208 := by decide
  rcases family_descends (prefixWord ++ tailWord_594208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594211 : List Nat := [1, 1, 1, 4, 2, 2, 2, 10]
def baseStart_594211 : Nat := 118140960795 + 594211 * 2 ^ 59
def prefixEnd_594211 : Nat := 4983230072969 + 3 ^ 40 * 594211 * 2
def baseEnd_594211 : Nat := 11300587155143699275177

theorem tailTrace_594211 : CollatzResearch.WordTrace tailWord_594211 prefixEnd_594211 11300587155143699275177 := by
  unfold tailWord_594211
  simp only [CollatzResearch.WordTrace]
  refine ⟨21672655650282505004422487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14448437100188336669614991 21672655650282505004422487)
  ·
    refine ⟨32508983475423757506633731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21672655650282505004422487 32508983475423757506633731)
    ·
      refine ⟨48763475213135636259950597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32508983475423757506633731 48763475213135636259950597)
      ·
        refine ⟨9143151602462931798740737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48763475213135636259950597 9143151602462931798740737)
        ·
          refine ⟨6857363701847198849055553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9143151602462931798740737 6857363701847198849055553)
          ·
            refine ⟨5143022776385399136791665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6857363701847198849055553 5143022776385399136791665)
            ·
              refine ⟨3857267082289049352593749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5143022776385399136791665 3857267082289049352593749)
              ·
                refine ⟨11300587155143699275177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3857267082289049352593749 11300587155143699275177)
                ·
                  rfl

theorem cell23_594211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 10].length) (baseStart_594211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594211 prefixEnd_594211 := by exact prefixLift 594211
  have htrace : WordTrace (prefixWord ++ tailWord_594211) baseStart_594211 baseEnd_594211 := by
    simpa [prefixWord, tailWord_594211, baseEnd_594211] using wordTrace_append hprefix tailTrace_594211
  have hstable : (prefixWord ++ tailWord_594211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594211).length < 2 ^ (prefixWord ++ tailWord_594211).sum := by decide
  have hdescent : baseEnd_594211 < baseStart_594211 := by decide
  rcases family_descends (prefixWord ++ tailWord_594211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594231 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 6]
def baseStart_594231 : Nat := 118140960795 + 594231 * 2 ^ 59
def prefixEnd_594231 : Nat := 4983230072969 + 3 ^ 40 * 594231 * 2
def baseEnd_594231 : Nat := 305126122801969802179687

theorem tailTrace_594231 : CollatzResearch.WordTrace tailWord_594231 prefixEnd_594231 305126122801969802179687 := by
  unfold tailWord_594231
  simp only [CollatzResearch.WordTrace]
  refine ⟨21673385110210048420150547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14448923406806698946767031 21673385110210048420150547)
  ·
    refine ⟨32510077665315072630225821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21673385110210048420150547 32510077665315072630225821)
    ·
      refine ⟨12191279124493152236334683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32510077665315072630225821 12191279124493152236334683)
      ·
        refine ⟨18286918686739728354502025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12191279124493152236334683 18286918686739728354502025)
        ·
          refine ⟨13715189015054796265876519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18286918686739728354502025 13715189015054796265876519)
          ·
            refine ⟨20572783522582194398814779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13715189015054796265876519 20572783522582194398814779)
            ·
              refine ⟨30859175283873291598222169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20572783522582194398814779 30859175283873291598222169)
              ·
                refine ⟨23144381462904968698666627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30859175283873291598222169 23144381462904968698666627)
                ·
                  refine ⟨34716572194357453047999941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23144381462904968698666627 34716572194357453047999941)
                  ·
                    refine ⟨6509357286442022446499989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34716572194357453047999941 6509357286442022446499989)
                    ·
                      refine ⟨305126122801969802179687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6509357286442022446499989 305126122801969802179687)
                      ·
                        rfl

theorem cell23_594231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_594231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594231 prefixEnd_594231 := by exact prefixLift 594231
  have htrace : WordTrace (prefixWord ++ tailWord_594231) baseStart_594231 baseEnd_594231 := by
    simpa [prefixWord, tailWord_594231, baseEnd_594231] using wordTrace_append hprefix tailTrace_594231
  have hstable : (prefixWord ++ tailWord_594231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594231).length < 2 ^ (prefixWord ++ tailWord_594231).sum := by decide
  have hdescent : baseEnd_594231 < baseStart_594231 := by decide
  rcases family_descends (prefixWord ++ tailWord_594231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594256 : List Nat := [2, 1, 1, 1, 1, 7, 3, 2, 1, 2, 2]
def baseStart_594256 : Nat := 118140960795 + 594256 * 2 ^ 59
def prefixEnd_594256 : Nat := 4983230072969 + 3 ^ 40 * 594256 * 2
def baseEnd_594256 : Nat := 305138959818332204367073

theorem tailTrace_594256 : CollatzResearch.WordTrace tailWord_594256 prefixEnd_594256 305138959818332204367073 := by
  unfold tailWord_594256
  simp only [CollatzResearch.WordTrace]
  refine ⟨10837148467559738844905311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14449531290079651793207081 10837148467559738844905311)
  ·
    refine ⟨16255722701339608267357967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10837148467559738844905311 16255722701339608267357967)
    ·
      refine ⟨24383584052009412401036951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16255722701339608267357967 24383584052009412401036951)
      ·
        refine ⟨36575376078014118601555427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24383584052009412401036951 36575376078014118601555427)
        ·
          refine ⟨54863064117021177902333141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36575376078014118601555427 54863064117021177902333141)
          ·
            refine ⟨1285853065242683857085933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 54863064117021177902333141 1285853065242683857085933)
            ·
              refine ⟨482194899466006446407225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1285853065242683857085933 482194899466006446407225)
              ·
                refine ⟨361646174599504834805419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 482194899466006446407225 361646174599504834805419)
                ·
                  refine ⟨542469261899257252208129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 361646174599504834805419 542469261899257252208129)
                  ·
                    refine ⟨406851946424442939156097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 542469261899257252208129 406851946424442939156097)
                    ·
                      refine ⟨305138959818332204367073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 406851946424442939156097 305138959818332204367073)
                      ·
                        rfl

theorem cell23_594256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 1, 2, 2].length) (baseStart_594256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594256 prefixEnd_594256 := by exact prefixLift 594256
  have htrace : WordTrace (prefixWord ++ tailWord_594256) baseStart_594256 baseEnd_594256 := by
    simpa [prefixWord, tailWord_594256, baseEnd_594256] using wordTrace_append hprefix tailTrace_594256
  have hstable : (prefixWord ++ tailWord_594256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594256).length < 2 ^ (prefixWord ++ tailWord_594256).sum := by decide
  have hdescent : baseEnd_594256 < baseStart_594256 := by decide
  rcases family_descends (prefixWord ++ tailWord_594256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594265 : List Nat := [1, 2, 1, 2, 2, 2, 1, 4, 3, 3, 2]
def baseStart_594265 : Nat := 118140960795 + 594265 * 2 ^ 59
def prefixEnd_594265 : Nat := 4983230072969 + 3 ^ 40 * 594265 * 2
def baseEnd_594265 : Nat := 305143581144222669154531

theorem tailTrace_594265 : CollatzResearch.WordTrace tailWord_594265 prefixEnd_594265 305143581144222669154531 := by
  unfold tailWord_594265
  simp only [CollatzResearch.WordTrace]
  refine ⟨21674625192086872226888249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14449750128057914817925499 21674625192086872226888249)
  ·
    refine ⟨16255968894065154170166187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21674625192086872226888249 16255968894065154170166187)
    ·
      refine ⟨24383953341097731255249281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16255968894065154170166187 24383953341097731255249281)
      ·
        refine ⟨18287965005823298441436961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24383953341097731255249281 18287965005823298441436961)
        ·
          refine ⟨13715973754367473831077721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18287965005823298441436961 13715973754367473831077721)
          ·
            refine ⟨10286980315775605373308291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13715973754367473831077721 10286980315775605373308291)
            ·
              refine ⟨15430470473663408059962437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10286980315775605373308291 15430470473663408059962437)
              ·
                refine ⟨2893213213811889011242957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15430470473663408059962437 2893213213811889011242957)
                ·
                  refine ⟨1084954955179458379216109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2893213213811889011242957 1084954955179458379216109)
                  ·
                    refine ⟨406858108192296892206041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1084954955179458379216109 406858108192296892206041)
                    ·
                      refine ⟨305143581144222669154531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 406858108192296892206041 305143581144222669154531)
                      ·
                        rfl

theorem cell23_594265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 3, 2].length) (baseStart_594265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594265 prefixEnd_594265 := by exact prefixLift 594265
  have htrace : WordTrace (prefixWord ++ tailWord_594265) baseStart_594265 baseEnd_594265 := by
    simpa [prefixWord, tailWord_594265, baseEnd_594265] using wordTrace_append hprefix tailTrace_594265
  have hstable : (prefixWord ++ tailWord_594265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594265).length < 2 ^ (prefixWord ++ tailWord_594265).sum := by decide
  have hdescent : baseEnd_594265 < baseStart_594265 := by decide
  rcases family_descends (prefixWord ++ tailWord_594265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594270 : List Nat := [4, 4, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_594270 : Nat := 118140960795 + 594270 * 2 ^ 59
def prefixEnd_594270 : Nat := 4983230072969 + 3 ^ 40 * 594270 * 2
def baseEnd_594270 : Nat := 101715382849165049864003

theorem tailTrace_594270 : CollatzResearch.WordTrace tailWord_594270 prefixEnd_594270 101715382849165049864003 := by
  unfold tailWord_594270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2709350944633594760102533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14449871704712505387213509 2709350944633594760102533)
  ·
    refine ⟨508003302118799017519225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2709350944633594760102533 508003302118799017519225)
    ·
      refine ⟨381002476589099263139419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 508003302118799017519225 381002476589099263139419)
      ·
        refine ⟨571503714883648894709129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381002476589099263139419 571503714883648894709129)
        ·
          refine ⟨428627786162736671031847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 571503714883648894709129 428627786162736671031847)
          ·
            refine ⟨642941679244105006547771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428627786162736671031847 642941679244105006547771)
            ·
              refine ⟨964412518866157509821657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 642941679244105006547771 964412518866157509821657)
              ·
                refine ⟨723309389149618132366243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 964412518866157509821657 723309389149618132366243)
                ·
                  refine ⟨1084964083724427198549365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 723309389149618132366243 1084964083724427198549365)
                  ·
                    refine ⟨101715382849165049864003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1084964083724427198549365 101715382849165049864003)
                    ·
                      rfl

theorem cell23_594270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_594270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594270 prefixEnd_594270 := by exact prefixLift 594270
  have htrace : WordTrace (prefixWord ++ tailWord_594270) baseStart_594270 baseEnd_594270 := by
    simpa [prefixWord, tailWord_594270, baseEnd_594270] using wordTrace_append hprefix tailTrace_594270
  have hstable : (prefixWord ++ tailWord_594270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594270).length < 2 ^ (prefixWord ++ tailWord_594270).sum := by decide
  have hdescent : baseEnd_594270 < baseStart_594270 := by decide
  rcases family_descends (prefixWord ++ tailWord_594270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594298 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3]
def baseStart_594298 : Nat := 118140960795 + 594298 * 2 ^ 59
def prefixEnd_594298 : Nat := 4983230072969 + 3 ^ 40 * 594298 * 2
def baseEnd_594298 : Nat := 305160526005821040041879

theorem tailTrace_594298 : CollatzResearch.WordTrace tailWord_594298 prefixEnd_594298 305160526005821040041879 := by
  unfold tailWord_594298
  simp only [CollatzResearch.WordTrace]
  refine ⟨5418957200241829715709887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14450552533978212575226365 5418957200241829715709887)
  ·
    refine ⟨8128435800362744573564831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5418957200241829715709887 8128435800362744573564831)
    ·
      refine ⟨12192653700544116860347247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8128435800362744573564831 12192653700544116860347247)
      ·
        refine ⟨18288980550816175290520871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12192653700544116860347247 18288980550816175290520871)
        ·
          refine ⟨27433470826224262935781307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18288980550816175290520871 27433470826224262935781307)
          ·
            refine ⟨41150206239336394403671961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27433470826224262935781307 41150206239336394403671961)
            ·
              refine ⟨30862654679502295802753971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41150206239336394403671961 30862654679502295802753971)
              ·
                refine ⟨46293982019253443704130957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30862654679502295802753971 46293982019253443704130957)
                ·
                  refine ⟨17360243257220041389049109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46293982019253443704130957 17360243257220041389049109)
                  ·
                    refine ⟨813761402682189440111677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17360243257220041389049109 813761402682189440111677)
                    ·
                      refine ⟨305160526005821040041879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 813761402682189440111677 305160526005821040041879)
                      ·
                        rfl

theorem cell23_594298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3].length) (baseStart_594298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594298 prefixEnd_594298 := by exact prefixLift 594298
  have htrace : WordTrace (prefixWord ++ tailWord_594298) baseStart_594298 baseEnd_594298 := by
    simpa [prefixWord, tailWord_594298, baseEnd_594298] using wordTrace_append hprefix tailTrace_594298
  have hstable : (prefixWord ++ tailWord_594298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594298).length < 2 ^ (prefixWord ++ tailWord_594298).sum := by decide
  have hdescent : baseEnd_594298 < baseStart_594298 := by decide
  rcases family_descends (prefixWord ++ tailWord_594298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594299 : List Nat := [1, 1, 1, 1, 1, 8, 3, 1, 1, 3, 2]
def baseStart_594299 : Nat := 118140960795 + 594299 * 2 ^ 59
def prefixEnd_594299 : Nat := 4983230072969 + 3 ^ 40 * 594299 * 2
def baseEnd_594299 : Nat := 305161039486475536129375

theorem tailTrace_594299 : CollatzResearch.WordTrace tailWord_594299 prefixEnd_594299 305161039486475536129375 := by
  unfold tailWord_594299
  simp only [CollatzResearch.WordTrace]
  refine ⟨21675865273963696033625951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14450576849309130689083967 21675865273963696033625951)
  ·
    refine ⟨32513797910945544050438927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21675865273963696033625951 32513797910945544050438927)
    ·
      refine ⟨48770696866418316075658391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32513797910945544050438927 48770696866418316075658391)
      ·
        refine ⟨73156045299627474113487587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48770696866418316075658391 73156045299627474113487587)
        ·
          refine ⟨109734067949441211170231381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73156045299627474113487587 109734067949441211170231381)
          ·
            refine ⟨1285946108782514193401149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 109734067949441211170231381 1285946108782514193401149)
            ·
              refine ⟨482229790793442822525431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1285946108782514193401149 482229790793442822525431)
              ·
                refine ⟨723344686190164233788147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 482229790793442822525431 723344686190164233788147)
                ·
                  refine ⟨1085017029285246350682221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 723344686190164233788147 1085017029285246350682221)
                  ·
                    refine ⟨406881385981967381505833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1085017029285246350682221 406881385981967381505833)
                    ·
                      refine ⟨305161039486475536129375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 406881385981967381505833 305161039486475536129375)
                      ·
                        rfl

theorem cell23_594299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 1, 3, 2].length) (baseStart_594299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594299 prefixEnd_594299 := by exact prefixLift 594299
  have htrace : WordTrace (prefixWord ++ tailWord_594299) baseStart_594299 baseEnd_594299 := by
    simpa [prefixWord, tailWord_594299, baseEnd_594299] using wordTrace_append hprefix tailTrace_594299
  have hstable : (prefixWord ++ tailWord_594299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594299).length < 2 ^ (prefixWord ++ tailWord_594299).sum := by decide
  have hdescent : baseEnd_594299 < baseStart_594299 := by decide
  rcases family_descends (prefixWord ++ tailWord_594299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594485 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 3, 6]
def baseStart_594485 : Nat := 118140960795 + 594485 * 2 ^ 59
def prefixEnd_594485 : Nat := 4983230072969 + 3 ^ 40 * 594485 * 2
def baseEnd_594485 : Nat := 101752182296070602801173

theorem tailTrace_594485 : CollatzResearch.WordTrace tailWord_594485 prefixEnd_594485 101752182296070602801173 := by
  unfold tailWord_594485
  simp only [CollatzResearch.WordTrace]
  refine ⟨21682649251289849799896909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14455099500859899866597939 21682649251289849799896909)
  ·
    refine ⟨8130993469233693674961341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21682649251289849799896909 8130993469233693674961341)
    ·
      refine ⟨3049122550962635128110503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8130993469233693674961341 3049122550962635128110503)
      ·
        refine ⟨4573683826443952692165755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3049122550962635128110503 4573683826443952692165755)
        ·
          refine ⟨6860525739665929038248633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4573683826443952692165755 6860525739665929038248633)
          ·
            refine ⟨5145394304749446778686475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6860525739665929038248633 5145394304749446778686475)
            ·
              refine ⟨7718091457124170168029713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5145394304749446778686475 7718091457124170168029713)
              ·
                refine ⟨5788568592843127626022285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7718091457124170168029713 5788568592843127626022285)
                ·
                  refine ⟨2170713222316172859758357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5788568592843127626022285 2170713222316172859758357)
                  ·
                    refine ⟨101752182296070602801173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2170713222316172859758357 101752182296070602801173)
                    ·
                      rfl

theorem cell23_594485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_594485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594485 prefixEnd_594485 := by exact prefixLift 594485
  have htrace : WordTrace (prefixWord ++ tailWord_594485) baseStart_594485 baseEnd_594485 := by
    simpa [prefixWord, tailWord_594485, baseEnd_594485] using wordTrace_append hprefix tailTrace_594485
  have hstable : (prefixWord ++ tailWord_594485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594485).length < 2 ^ (prefixWord ++ tailWord_594485).sum := by decide
  have hdescent : baseEnd_594485 < baseStart_594485 := by decide
  rcases family_descends (prefixWord ++ tailWord_594485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594492 : List Nat := [2, 2, 2, 2, 3, 1, 1, 2, 3, 1, 4]
def baseStart_594492 : Nat := 118140960795 + 594492 * 2 ^ 59
def prefixEnd_594492 : Nat := 4983230072969 + 3 ^ 40 * 594492 * 2
def baseEnd_594492 : Nat := 305260141252793281015987

theorem tailTrace_594492 : CollatzResearch.WordTrace tailWord_594492 prefixEnd_594492 305260141252793281015987 := by
  unfold tailWord_594492
  simp only [CollatzResearch.WordTrace]
  refine ⟨10841452281132244997700865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14455269708176326663601153 10841452281132244997700865)
  ·
    refine ⟨8131089210849183748275649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10841452281132244997700865 8131089210849183748275649)
    ·
      refine ⟨6098316908136887811206737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8131089210849183748275649 6098316908136887811206737)
      ·
        refine ⟨4573737681102665858405053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6098316908136887811206737 4573737681102665858405053)
        ·
          refine ⟨1715151630413499696901895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4573737681102665858405053 1715151630413499696901895)
          ·
            refine ⟨2572727445620249545352843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1715151630413499696901895 2572727445620249545352843)
            ·
              refine ⟨3859091168430374318029265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2572727445620249545352843 3859091168430374318029265)
              ·
                refine ⟨2894318376322780738521949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3859091168430374318029265 2894318376322780738521949)
                ·
                  refine ⟨1085369391121042776945731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2894318376322780738521949 1085369391121042776945731)
                  ·
                    refine ⟨1628054086681564165418597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1085369391121042776945731 1628054086681564165418597)
                    ·
                      refine ⟨305260141252793281015987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1628054086681564165418597 305260141252793281015987)
                      ·
                        rfl

theorem cell23_594492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_594492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594492 prefixEnd_594492 := by exact prefixLift 594492
  have htrace : WordTrace (prefixWord ++ tailWord_594492) baseStart_594492 baseEnd_594492 := by
    simpa [prefixWord, tailWord_594492, baseEnd_594492] using wordTrace_append hprefix tailTrace_594492
  have hstable : (prefixWord ++ tailWord_594492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594492).length < 2 ^ (prefixWord ++ tailWord_594492).sum := by decide
  have hdescent : baseEnd_594492 < baseStart_594492 := by decide
  rcases family_descends (prefixWord ++ tailWord_594492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594495 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 5]
def baseStart_594495 : Nat := 118140960795 + 594495 * 2 ^ 59
def prefixEnd_594495 : Nat := 4983230072969 + 3 ^ 40 * 594495 * 2
def baseEnd_594495 : Nat := 305261681694756769278473

theorem tailTrace_594495 : CollatzResearch.WordTrace tailWord_594495 prefixEnd_594495 305261681694756769278473 := by
  unfold tailWord_594495
  simp only [CollatzResearch.WordTrace]
  refine ⟨21683013981253621507760939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14455342654169081005173959 21683013981253621507760939)
  ·
    refine ⟨32524520971880432261641409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21683013981253621507760939 32524520971880432261641409)
    ·
      refine ⟨24393390728910324196231057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32524520971880432261641409 24393390728910324196231057)
      ·
        refine ⟨18295043046682743147173293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24393390728910324196231057 18295043046682743147173293)
        ·
          refine ⟨6860641142506028680189985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18295043046682743147173293 6860641142506028680189985)
          ·
            refine ⟨5145480856879521510142489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6860641142506028680189985 5145480856879521510142489)
            ·
              refine ⟨3859110642659641132606867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5145480856879521510142489 3859110642659641132606867)
              ·
                refine ⟨5788665963989461698910301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3859110642659641132606867 5788665963989461698910301)
                ·
                  refine ⟨2170749736496048137091363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5788665963989461698910301 2170749736496048137091363)
                  ·
                    refine ⟨3256124604744072205637045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2170749736496048137091363 3256124604744072205637045)
                    ·
                      refine ⟨305261681694756769278473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3256124604744072205637045 305261681694756769278473)
                      ·
                        rfl

theorem cell23_594495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_594495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594495 prefixEnd_594495 := by exact prefixLift 594495
  have htrace : WordTrace (prefixWord ++ tailWord_594495) baseStart_594495 baseEnd_594495 := by
    simpa [prefixWord, tailWord_594495, baseEnd_594495] using wordTrace_append hprefix tailTrace_594495
  have hstable : (prefixWord ++ tailWord_594495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594495).length < 2 ^ (prefixWord ++ tailWord_594495).sum := by decide
  have hdescent : baseEnd_594495 < baseStart_594495 := by decide
  rcases family_descends (prefixWord ++ tailWord_594495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594509 : List Nat := [1, 6, 1, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_594509 : Nat := 118140960795 + 594509 * 2 ^ 59
def prefixEnd_594509 : Nat := 4983230072969 + 3 ^ 40 * 594509 * 2
def baseEnd_594509 : Nat := 305268870423919714503409

theorem tailTrace_594509 : CollatzResearch.WordTrace tailWord_594509 prefixEnd_594509 305268870423919714503409 := by
  unfold tailWord_594509
  simp only [CollatzResearch.WordTrace]
  refine ⟨21683524603202901898770581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14455683068801934599180387 21683524603202901898770581)
  ·
    refine ⟨1016415215775136026504871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21683524603202901898770581 1016415215775136026504871)
    ·
      refine ⟨1524622823662704039757307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1016415215775136026504871 1524622823662704039757307)
      ·
        refine ⟨2286934235494056059635961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1524622823662704039757307 2286934235494056059635961)
        ·
          refine ⟨1715200676620542044726971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2286934235494056059635961 1715200676620542044726971)
          ·
            refine ⟨2572801014930813067090457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1715200676620542044726971 2572801014930813067090457)
            ·
              refine ⟨1929600761198109800317843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2572801014930813067090457 1929600761198109800317843)
              ·
                refine ⟨2894401141797164700476765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1929600761198109800317843 2894401141797164700476765)
                ·
                  refine ⟨1085400428173936762678787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2894401141797164700476765 1085400428173936762678787)
                  ·
                    refine ⟨1628100642260905144018181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1085400428173936762678787 1628100642260905144018181)
                    ·
                      refine ⟨305268870423919714503409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1628100642260905144018181 305268870423919714503409)
                      ·
                        rfl

theorem cell23_594509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_594509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594509 prefixEnd_594509 := by exact prefixLift 594509
  have htrace : WordTrace (prefixWord ++ tailWord_594509) baseStart_594509 baseEnd_594509 := by
    simpa [prefixWord, tailWord_594509, baseEnd_594509] using wordTrace_append hprefix tailTrace_594509
  have hstable : (prefixWord ++ tailWord_594509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594509).length < 2 ^ (prefixWord ++ tailWord_594509).sum := by decide
  have hdescent : baseEnd_594509 < baseStart_594509 := by decide
  rcases family_descends (prefixWord ++ tailWord_594509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594529 : List Nat := [1, 2, 3, 1, 1, 5, 1, 3, 1, 2, 3]
def baseStart_594529 : Nat := 118140960795 + 594529 * 2 ^ 59
def prefixEnd_594529 : Nat := 4983230072969 + 3 ^ 40 * 594529 * 2
def baseEnd_594529 : Nat := 305279140037009636253317

theorem tailTrace_594529 : CollatzResearch.WordTrace tailWord_594529 prefixEnd_594529 305279140037009636253317 := by
  unfold tailWord_594529
  simp only [CollatzResearch.WordTrace]
  refine ⟨21684254063130445314498641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14456169375420296876332427 21684254063130445314498641)
  ·
    refine ⟨16263190547347833985873981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21684254063130445314498641 16263190547347833985873981)
    ·
      refine ⟨6098696455255437744702743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16263190547347833985873981 6098696455255437744702743)
      ·
        refine ⟨9148044682883156617054115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6098696455255437744702743 9148044682883156617054115)
        ·
          refine ⟨13722067024324734925581173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9148044682883156617054115 13722067024324734925581173)
          ·
            refine ⟨1286443783530443899273235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13722067024324734925581173 1286443783530443899273235)
            ·
              refine ⟨1929665675295665848909853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1286443783530443899273235 1929665675295665848909853)
              ·
                refine ⟨723624628235874693341195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1929665675295665848909853 723624628235874693341195)
                ·
                  refine ⟨1085436942353812040011793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 723624628235874693341195 1085436942353812040011793)
                  ·
                    refine ⟨814077706765359030008845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1085436942353812040011793 814077706765359030008845)
                    ·
                      refine ⟨305279140037009636253317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 814077706765359030008845 305279140037009636253317)
                      ·
                        rfl

theorem cell23_594529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_594529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594529 prefixEnd_594529 := by exact prefixLift 594529
  have htrace : WordTrace (prefixWord ++ tailWord_594529) baseStart_594529 baseEnd_594529 := by
    simpa [prefixWord, tailWord_594529, baseEnd_594529] using wordTrace_append hprefix tailTrace_594529
  have hstable : (prefixWord ++ tailWord_594529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594529).length < 2 ^ (prefixWord ++ tailWord_594529).sum := by decide
  have hdescent : baseEnd_594529 < baseStart_594529 := by decide
  rcases family_descends (prefixWord ++ tailWord_594529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594535 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_594535 : Nat := 118140960795 + 594535 * 2 ^ 59
def prefixEnd_594535 : Nat := 4983230072969 + 3 ^ 40 * 594535 * 2
def baseEnd_594535 : Nat := 305282220920936612778289

theorem tailTrace_594535 : CollatzResearch.WordTrace tailWord_594535 prefixEnd_594535 305282220920936612778289 := by
  unfold tailWord_594535
  simp only [CollatzResearch.WordTrace]
  refine ⟨21684472901108708339217059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14456315267405805559478039 21684472901108708339217059)
  ·
    refine ⟨32526709351663062508825589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21684472901108708339217059 32526709351663062508825589)
    ·
      refine ⟨3049379001718412110202399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32526709351663062508825589 3049379001718412110202399)
      ·
        refine ⟨4574068502577618165303599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3049379001718412110202399 4574068502577618165303599)
        ·
          refine ⟨6861102753866427247955399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4574068502577618165303599 6861102753866427247955399)
          ·
            refine ⟨10291654130799640871933099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6861102753866427247955399 10291654130799640871933099)
            ·
              refine ⟨15437481196199461307899649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10291654130799640871933099 15437481196199461307899649)
              ·
                refine ⟨11578110897149595980924737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15437481196199461307899649 11578110897149595980924737)
                ·
                  refine ⟨8683583172862196985693553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11578110897149595980924737 8683583172862196985693553)
                  ·
                    refine ⟨6512687379646647739270165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8683583172862196985693553 6512687379646647739270165)
                    ·
                      refine ⟨305282220920936612778289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6512687379646647739270165 305282220920936612778289)
                      ·
                        rfl

theorem cell23_594535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_594535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594535 prefixEnd_594535 := by exact prefixLift 594535
  have htrace : WordTrace (prefixWord ++ tailWord_594535) baseStart_594535 baseEnd_594535 := by
    simpa [prefixWord, tailWord_594535, baseEnd_594535] using wordTrace_append hprefix tailTrace_594535
  have hstable : (prefixWord ++ tailWord_594535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594535).length < 2 ^ (prefixWord ++ tailWord_594535).sum := by decide
  have hdescent : baseEnd_594535 < baseStart_594535 := by decide
  rcases family_descends (prefixWord ++ tailWord_594535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594595 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 6]
def baseStart_594595 : Nat := 118140960795 + 594595 * 2 ^ 59
def prefixEnd_594595 : Nat := 4983230072969 + 3 ^ 40 * 594595 * 2
def baseEnd_594595 : Nat := 305313029760206378028013

theorem tailTrace_594595 : CollatzResearch.WordTrace tailWord_594595 prefixEnd_594595 305313029760206378028013 := by
  unfold tailWord_594595
  simp only [CollatzResearch.WordTrace]
  refine ⟨21686661280891338586401239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14457774187260892390934159 21686661280891338586401239)
  ·
    refine ⟨32529991921337007879601859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21686661280891338586401239 32529991921337007879601859)
    ·
      refine ⟨48794987882005511819402789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32529991921337007879601859 48794987882005511819402789)
      ·
        refine ⟨9149060227876033466138023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48794987882005511819402789 9149060227876033466138023)
        ·
          refine ⟨13723590341814050199207035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9149060227876033466138023 13723590341814050199207035)
          ·
            refine ⟨20585385512721075298810553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13723590341814050199207035 20585385512721075298810553)
            ·
              refine ⟨15439039134540806474107915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20585385512721075298810553 15439039134540806474107915)
              ·
                refine ⟨23158558701811209711161873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15439039134540806474107915 23158558701811209711161873)
                ·
                  refine ⟨17368919026358407283371405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23158558701811209711161873 17368919026358407283371405)
                  ·
                    refine ⟨6513344634884402731264277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17368919026358407283371405 6513344634884402731264277)
                    ·
                      refine ⟨305313029760206378028013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6513344634884402731264277 305313029760206378028013)
                      ·
                        rfl

theorem cell23_594595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_594595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594595 prefixEnd_594595 := by exact prefixLift 594595
  have htrace : WordTrace (prefixWord ++ tailWord_594595) baseStart_594595 baseEnd_594595 := by
    simpa [prefixWord, tailWord_594595, baseEnd_594595] using wordTrace_append hprefix tailTrace_594595
  have hstable : (prefixWord ++ tailWord_594595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594595).length < 2 ^ (prefixWord ++ tailWord_594595).sum := by decide
  have hdescent : baseEnd_594595 < baseStart_594595 := by decide
  rcases family_descends (prefixWord ++ tailWord_594595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594622 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 9]
def baseStart_594622 : Nat := 118140960795 + 594622 * 2 ^ 59
def prefixEnd_594622 : Nat := 4983230072969 + 3 ^ 40 * 594622 * 2
def baseEnd_594622 : Nat := 33925210415319752487821

theorem tailTrace_594622 : CollatzResearch.WordTrace tailWord_594622 prefixEnd_594622 33925210415319752487821 := by
  unfold tailWord_594622
  simp only [CollatzResearch.WordTrace]
  refine ⟨2710955756474190274704265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14458430701195681465089413 2710955756474190274704265)
  ·
    refine ⟨2033216817355642706028199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2710955756474190274704265 2033216817355642706028199)
    ·
      refine ⟨3049825226033464059042299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2033216817355642706028199 3049825226033464059042299)
      ·
        refine ⟨4574737839050196088563449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3049825226033464059042299 4574737839050196088563449)
        ·
          refine ⟨3431053379287647066422587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4574737839050196088563449 3431053379287647066422587)
          ·
            refine ⟨5146580068931470599633881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3431053379287647066422587 5146580068931470599633881)
            ·
              refine ⟨3859935051698602949725411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5146580068931470599633881 3859935051698602949725411)
              ·
                refine ⟨5789902577547904424588117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3859935051698602949725411 5789902577547904424588117)
                ·
                  refine ⟨33925210415319752487821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5789902577547904424588117 33925210415319752487821)
                  ·
                    rfl

theorem cell23_594622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_594622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594622 prefixEnd_594622 := by exact prefixLift 594622
  have htrace : WordTrace (prefixWord ++ tailWord_594622) baseStart_594622 baseEnd_594622 := by
    simpa [prefixWord, tailWord_594622, baseEnd_594622] using wordTrace_append hprefix tailTrace_594622
  have hstable : (prefixWord ++ tailWord_594622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594622).length < 2 ^ (prefixWord ++ tailWord_594622).sum := by decide
  have hdescent : baseEnd_594622 < baseStart_594622 := by decide
  rcases family_descends (prefixWord ++ tailWord_594622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594637 : List Nat := [1, 6, 2, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_594637 : Nat := 118140960795 + 594637 * 2 ^ 59
def prefixEnd_594637 : Nat := 4983230072969 + 3 ^ 40 * 594637 * 2
def baseEnd_594637 : Nat := 305334595947695213702821

theorem tailTrace_594637 : CollatzResearch.WordTrace tailWord_594637 prefixEnd_594637 305334595947695213702821 := by
  unfold tailWord_594637
  simp only [CollatzResearch.WordTrace]
  refine ⟨21688193146739179759430165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14458795431159453172953443 21688193146739179759430165)
  ·
    refine ⟨1016634053753399051223289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21688193146739179759430165 1016634053753399051223289)
    ·
      refine ⟨762475540315049288417467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1016634053753399051223289 762475540315049288417467)
      ·
        refine ⟨1143713310472573932626201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 762475540315049288417467 1143713310472573932626201)
        ·
          refine ⟨857784982854430449469651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1143713310472573932626201 857784982854430449469651)
          ·
            refine ⟨1286677474281645674204477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 857784982854430449469651 1286677474281645674204477)
            ·
              refine ⟨482504052855617127826679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1286677474281645674204477 482504052855617127826679)
              ·
                refine ⟨723756079283425691740019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 482504052855617127826679 723756079283425691740019)
                ·
                  refine ⟨1085634118925138537610029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 723756079283425691740019 1085634118925138537610029)
                  ·
                    refine ⟨407112794596926951603761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1085634118925138537610029 407112794596926951603761)
                    ·
                      refine ⟨305334595947695213702821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 407112794596926951603761 305334595947695213702821)
                      ·
                        rfl

theorem cell23_594637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_594637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594637 prefixEnd_594637 := by exact prefixLift 594637
  have htrace : WordTrace (prefixWord ++ tailWord_594637) baseStart_594637 baseEnd_594637 := by
    simpa [prefixWord, tailWord_594637, baseEnd_594637] using wordTrace_append hprefix tailTrace_594637
  have hstable : (prefixWord ++ tailWord_594637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594637).length < 2 ^ (prefixWord ++ tailWord_594637).sum := by decide
  have hdescent : baseEnd_594637 < baseStart_594637 := by decide
  rcases family_descends (prefixWord ++ tailWord_594637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594672 : List Nat := [2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 4]
def baseStart_594672 : Nat := 118140960795 + 594672 * 2 ^ 59
def prefixEnd_594672 : Nat := 4983230072969 + 3 ^ 40 * 594672 * 2
def baseEnd_594672 : Nat := 305352567770602576765159

theorem tailTrace_594672 : CollatzResearch.WordTrace tailWord_594672 prefixEnd_594672 305352567770602576765159 := by
  unfold tailWord_594672
  simp only [CollatzResearch.WordTrace]
  refine ⟨10844734850806190368477135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14459646467741587157969513 10844734850806190368477135)
  ·
    refine ⟨16267102276209285552715703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10844734850806190368477135 16267102276209285552715703)
    ·
      refine ⟨24400653414313928329073555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16267102276209285552715703 24400653414313928329073555)
      ·
        refine ⟨36600980121470892493610333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24400653414313928329073555 36600980121470892493610333)
        ·
          refine ⟨13725367545551584685103875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36600980121470892493610333 13725367545551584685103875)
          ·
            refine ⟨20588051318327377027655813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13725367545551584685103875 20588051318327377027655813)
            ·
              refine ⟨3860259622186383192685465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20588051318327377027655813 3860259622186383192685465)
              ·
                refine ⟨2895194716639787394514099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3860259622186383192685465 2895194716639787394514099)
                ·
                  refine ⟨4342792074959681091771149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2895194716639787394514099 4342792074959681091771149)
                  ·
                    refine ⟨1628547028109880409414181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4342792074959681091771149 1628547028109880409414181)
                    ·
                      refine ⟨305352567770602576765159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1628547028109880409414181 305352567770602576765159)
                      ·
                        rfl

theorem cell23_594672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 4].length) (baseStart_594672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594672 prefixEnd_594672 := by exact prefixLift 594672
  have htrace : WordTrace (prefixWord ++ tailWord_594672) baseStart_594672 baseEnd_594672 := by
    simpa [prefixWord, tailWord_594672, baseEnd_594672] using wordTrace_append hprefix tailTrace_594672
  have hstable : (prefixWord ++ tailWord_594672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594672).length < 2 ^ (prefixWord ++ tailWord_594672).sum := by decide
  have hdescent : baseEnd_594672 < baseStart_594672 := by decide
  rcases family_descends (prefixWord ++ tailWord_594672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594686 : List Nat := [4, 2, 2, 1, 2, 1, 3, 1, 2, 5]
def baseStart_594686 : Nat := 118140960795 + 594686 * 2 ^ 59
def prefixEnd_594686 : Nat := 4983230072969 + 3 ^ 40 * 594686 * 2
def baseEnd_594686 : Nat := 101786585499921840663365

theorem tailTrace_594686 : CollatzResearch.WordTrace tailWord_594686 prefixEnd_594686 101786585499921840663365 := by
  unfold tailWord_594686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2711247540445207640995489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14459986882374440751975941 2711247540445207640995489)
  ·
    refine ⟨2033435655333905730746617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2711247540445207640995489 2033435655333905730746617)
    ·
      refine ⟨1525076741500429298059963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2033435655333905730746617 1525076741500429298059963)
      ·
        refine ⟨2287615112250643947089945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1525076741500429298059963 2287615112250643947089945)
        ·
          refine ⟨1715711334187982960317459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2287615112250643947089945 1715711334187982960317459)
          ·
            refine ⟨2573567001281974440476189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1715711334187982960317459 2573567001281974440476189)
            ·
              refine ⟨965087625480740415178571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2573567001281974440476189 965087625480740415178571)
              ·
                refine ⟨1447631438221110622767857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 965087625480740415178571 1447631438221110622767857)
                ·
                  refine ⟨1085723578665832967075893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1447631438221110622767857 1085723578665832967075893)
                  ·
                    refine ⟨101786585499921840663365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1085723578665832967075893 101786585499921840663365)
                    ·
                      rfl

theorem cell23_594686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_594686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594686 prefixEnd_594686 := by exact prefixLift 594686
  have htrace : WordTrace (prefixWord ++ tailWord_594686) baseStart_594686 baseEnd_594686 := by
    simpa [prefixWord, tailWord_594686, baseEnd_594686] using wordTrace_append hprefix tailTrace_594686
  have hstable : (prefixWord ++ tailWord_594686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594686).length < 2 ^ (prefixWord ++ tailWord_594686).sum := by decide
  have hdescent : baseEnd_594686 < baseStart_594686 := by decide
  rcases family_descends (prefixWord ++ tailWord_594686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594689 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 3, 6, 2]
def baseStart_594689 : Nat := 118140960795 + 594689 * 2 ^ 59
def prefixEnd_594689 : Nat := 4983230072969 + 3 ^ 40 * 594689 * 2
def baseEnd_594689 : Nat := 305361296941729010252581

theorem tailTrace_594689 : CollatzResearch.WordTrace tailWord_594689 prefixEnd_594689 305361296941729010252581 := by
  unfold tailWord_594689
  simp only [CollatzResearch.WordTrace]
  refine ⟨21690089742550792640323121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14460059828367195093548747 21690089742550792640323121)
  ·
    refine ⟨16267567306913094480242341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21690089742550792640323121 16267567306913094480242341)
    ·
      refine ⟨3050168870046205215045439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16267567306913094480242341 3050168870046205215045439)
      ·
        refine ⟨4575253305069307822568159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3050168870046205215045439 4575253305069307822568159)
        ·
          refine ⟨6862879957603961733852239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4575253305069307822568159 6862879957603961733852239)
          ·
            refine ⟨10294319936405942600778359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6862879957603961733852239 10294319936405942600778359)
            ·
              refine ⟨15441479904608913901167539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10294319936405942600778359 15441479904608913901167539)
              ·
                refine ⟨23162219856913370851751309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15441479904608913901167539 23162219856913370851751309)
                ·
                  refine ⟨8685832446342514069406741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23162219856913370851751309 8685832446342514069406741)
                  ·
                    refine ⟨407148395922305347003441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8685832446342514069406741 407148395922305347003441)
                    ·
                      refine ⟨305361296941729010252581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 407148395922305347003441 305361296941729010252581)
                      ·
                        rfl

theorem cell23_594689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_594689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594689 prefixEnd_594689 := by exact prefixLift 594689
  have htrace : WordTrace (prefixWord ++ tailWord_594689) baseStart_594689 baseEnd_594689 := by
    simpa [prefixWord, tailWord_594689, baseEnd_594689] using wordTrace_append hprefix tailTrace_594689
  have hstable : (prefixWord ++ tailWord_594689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594689).length < 2 ^ (prefixWord ++ tailWord_594689).sum := by decide
  have hdescent : baseEnd_594689 < baseStart_594689 := by decide
  rcases family_descends (prefixWord ++ tailWord_594689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594709 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 4, 2, 3]
def baseStart_594709 : Nat := 118140960795 + 594709 * 2 ^ 59
def prefixEnd_594709 : Nat := 4983230072969 + 3 ^ 40 * 594709 * 2
def baseEnd_594709 : Nat := 305371566554818932002489

theorem tailTrace_594709 : CollatzResearch.WordTrace tailWord_594709 prefixEnd_594709 305371566554818932002489 := by
  unfold tailWord_594709
  simp only [CollatzResearch.WordTrace]
  refine ⟨21690819202478336056051181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14460546134985557370700787 21690819202478336056051181)
  ·
    refine ⟨8134057200929376021019193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21690819202478336056051181 8134057200929376021019193)
    ·
      refine ⟨6100542900697032015764395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8134057200929376021019193 6100542900697032015764395)
      ·
        refine ⟨9150814351045548023646593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6100542900697032015764395 9150814351045548023646593)
        ·
          refine ⟨6863110763284161017734945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9150814351045548023646593 6863110763284161017734945)
          ·
            refine ⟨5147333072463120763301209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6863110763284161017734945 5147333072463120763301209)
            ·
              refine ⟨3860499804347340572475907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5147333072463120763301209 3860499804347340572475907)
              ·
                refine ⟨5790749706521010858713861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3860499804347340572475907 5790749706521010858713861)
                ·
                  refine ⟨1085765569972689536008849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5790749706521010858713861 1085765569972689536008849)
                  ·
                    refine ⟨814324177479517152006637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1085765569972689536008849 814324177479517152006637)
                    ·
                      refine ⟨305371566554818932002489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 814324177479517152006637 305371566554818932002489)
                      ·
                        rfl

theorem cell23_594709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_594709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594709 prefixEnd_594709 := by exact prefixLift 594709
  have htrace : WordTrace (prefixWord ++ tailWord_594709) baseStart_594709 baseEnd_594709 := by
    simpa [prefixWord, tailWord_594709, baseEnd_594709] using wordTrace_append hprefix tailTrace_594709
  have hstable : (prefixWord ++ tailWord_594709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594709).length < 2 ^ (prefixWord ++ tailWord_594709).sum := by decide
  have hdescent : baseEnd_594709 < baseStart_594709 := by decide
  rcases family_descends (prefixWord ++ tailWord_594709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594716 : List Nat := [2, 2, 3, 1, 1, 4, 2, 1, 3, 4]
def baseStart_594716 : Nat := 118140960795 + 594716 * 2 ^ 59
def prefixEnd_594716 : Nat := 4983230072969 + 3 ^ 40 * 594716 * 2
def baseEnd_594716 : Nat := 101791720306466801538319

theorem tailTrace_594716 : CollatzResearch.WordTrace tailWord_594716 prefixEnd_594716 101791720306466801538319 := by
  unfold tailWord_594716
  simp only [CollatzResearch.WordTrace]
  refine ⟨10845537256726488125778001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14460716342301984167704001 10845537256726488125778001)
  ·
    refine ⟨8134152942544866094333501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10845537256726488125778001 8134152942544866094333501)
    ·
      refine ⟨3050307353454324785375063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8134152942544866094333501 3050307353454324785375063)
      ·
        refine ⟨4575461030181487178062595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3050307353454324785375063 4575461030181487178062595)
        ·
          refine ⟨6863191545272230767093893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4575461030181487178062595 6863191545272230767093893)
          ·
            refine ⟨1286848414738543268830105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6863191545272230767093893 1286848414738543268830105)
            ·
              refine ⟨965136311053907451622579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1286848414738543268830105 965136311053907451622579)
              ·
                refine ⟨1447704466580861177433869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 965136311053907451622579 1447704466580861177433869)
                ·
                  refine ⟨542889174967822941537701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1447704466580861177433869 542889174967822941537701)
                  ·
                    refine ⟨101791720306466801538319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 542889174967822941537701 101791720306466801538319)
                    ·
                      rfl

theorem cell23_594716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_594716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594716 prefixEnd_594716 := by exact prefixLift 594716
  have htrace : WordTrace (prefixWord ++ tailWord_594716) baseStart_594716 baseEnd_594716 := by
    simpa [prefixWord, tailWord_594716, baseEnd_594716] using wordTrace_append hprefix tailTrace_594716
  have hstable : (prefixWord ++ tailWord_594716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594716).length < 2 ^ (prefixWord ++ tailWord_594716).sum := by decide
  have hdescent : baseEnd_594716 < baseStart_594716 := by decide
  rcases family_descends (prefixWord ++ tailWord_594716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594732 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 6]
def baseStart_594732 : Nat := 118140960795 + 594732 * 2 ^ 59
def prefixEnd_594732 : Nat := 4983230072969 + 3 ^ 40 * 594732 * 2
def baseEnd_594732 : Nat := 305383376609872342014883

theorem tailTrace_594732 : CollatzResearch.WordTrace tailWord_594732 prefixEnd_594732 305383376609872342014883 := by
  unfold tailWord_594732
  simp only [CollatzResearch.WordTrace]
  refine ⟨10845829040697505492069225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14461105387596673989425633 10845829040697505492069225)
  ·
    refine ⟨8134371780523129119051919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10845829040697505492069225 8134371780523129119051919)
    ·
      refine ⟨12201557670784693678577879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8134371780523129119051919 12201557670784693678577879)
      ·
        refine ⟨18302336506177040517866819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12201557670784693678577879 18302336506177040517866819)
        ·
          refine ⟨27453504759265560776800229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18302336506177040517866819 27453504759265560776800229)
          ·
            refine ⟨5147532142362292645650043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27453504759265560776800229 5147532142362292645650043)
            ·
              refine ⟨7721298213543438968475065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5147532142362292645650043 7721298213543438968475065)
              ·
                refine ⟨5790973660157579226356299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7721298213543438968475065 5790973660157579226356299)
                ·
                  refine ⟨8686460490236368839534449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5790973660157579226356299 8686460490236368839534449)
                  ·
                    refine ⟨6514845367677276629650837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8686460490236368839534449 6514845367677276629650837)
                    ·
                      refine ⟨305383376609872342014883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6514845367677276629650837 305383376609872342014883)
                      ·
                        rfl

theorem cell23_594732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_594732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594732 prefixEnd_594732 := by exact prefixLift 594732
  have htrace : WordTrace (prefixWord ++ tailWord_594732) baseStart_594732 baseEnd_594732 := by
    simpa [prefixWord, tailWord_594732, baseEnd_594732] using wordTrace_append hprefix tailTrace_594732
  have hstable : (prefixWord ++ tailWord_594732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594732).length < 2 ^ (prefixWord ++ tailWord_594732).sum := by decide
  have hdescent : baseEnd_594732 < baseStart_594732 := by decide
  rcases family_descends (prefixWord ++ tailWord_594732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594779 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 5, 8, 2]
def baseStart_594779 : Nat := 118140960795 + 594779 * 2 ^ 59
def prefixEnd_594779 : Nat := 4983230072969 + 3 ^ 40 * 594779 * 2
def baseEnd_594779 : Nat := 305407510200633658127167

theorem tailTrace_594779 : CollatzResearch.WordTrace tailWord_594779 prefixEnd_594779 305407510200633658127167 := by
  unfold tailWord_594779
  simp only [CollatzResearch.WordTrace]
  refine ⟨21693372312224738011099391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14462248208149825340732927 21693372312224738011099391)
  ·
    refine ⟨32540058468337107016649087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21693372312224738011099391 32540058468337107016649087)
    ·
      refine ⟨48810087702505660524973631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32540058468337107016649087 48810087702505660524973631)
      ·
        refine ⟨73215131553758490787460447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48810087702505660524973631 73215131553758490787460447)
        ·
          refine ⟨109822697330637736181190671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73215131553758490787460447 109822697330637736181190671)
          ·
            refine ⟨164734045995956604271786007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109822697330637736181190671 164734045995956604271786007)
            ·
              refine ⟨247101068993934906407679011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164734045995956604271786007 247101068993934906407679011)
              ·
                refine ⟨370651603490902359611518517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247101068993934906407679011 370651603490902359611518517)
                ·
                  refine ⟨34748587827272096213579861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 370651603490902359611518517 34748587827272096213579861)
                  ·
                    refine ⟨407210013600844877502889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34748587827272096213579861 407210013600844877502889)
                    ·
                      refine ⟨305407510200633658127167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 407210013600844877502889 305407510200633658127167)
                      ·
                        rfl

theorem cell23_594779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 8, 2].length) (baseStart_594779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594779 prefixEnd_594779 := by exact prefixLift 594779
  have htrace : WordTrace (prefixWord ++ tailWord_594779) baseStart_594779 baseEnd_594779 := by
    simpa [prefixWord, tailWord_594779, baseEnd_594779] using wordTrace_append hprefix tailTrace_594779
  have hstable : (prefixWord ++ tailWord_594779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594779).length < 2 ^ (prefixWord ++ tailWord_594779).sum := by decide
  have hdescent : baseEnd_594779 < baseStart_594779 := by decide
  rcases family_descends (prefixWord ++ tailWord_594779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594806 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 3, 6]
def baseStart_594806 : Nat := 118140960795 + 594806 * 2 ^ 59
def prefixEnd_594806 : Nat := 4983230072969 + 3 ^ 40 * 594806 * 2
def baseEnd_594806 : Nat := 101807124726101684163181

theorem tailTrace_594806 : CollatzResearch.WordTrace tailWord_594806 prefixEnd_594806 101807124726101684163181 := by
  unfold tailWord_594806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1355897317695432601395767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14462904722084614414888181 1355897317695432601395767)
  ·
    refine ⟨2033845976543148902093651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1355897317695432601395767 2033845976543148902093651)
    ·
      refine ⟨3050768964814723353140477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2033845976543148902093651 3050768964814723353140477)
      ·
        refine ⟨1144038361805521257427679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3050768964814723353140477 1144038361805521257427679)
        ·
          refine ⟨1716057542708281886141519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1144038361805521257427679 1716057542708281886141519)
          ·
            refine ⟨2574086314062422829212279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1716057542708281886141519 2574086314062422829212279)
            ·
              refine ⟨3861129471093634243818419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2574086314062422829212279 3861129471093634243818419)
              ·
                refine ⟨5791694206640451365727629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3861129471093634243818419 5791694206640451365727629)
                ·
                  refine ⟨2171885327490169262147861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5791694206640451365727629 2171885327490169262147861)
                  ·
                    refine ⟨101807124726101684163181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2171885327490169262147861 101807124726101684163181)
                    ·
                      rfl

theorem cell23_594806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_594806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594806 prefixEnd_594806 := by exact prefixLift 594806
  have htrace : WordTrace (prefixWord ++ tailWord_594806) baseStart_594806 baseEnd_594806 := by
    simpa [prefixWord, tailWord_594806, baseEnd_594806] using wordTrace_append hprefix tailTrace_594806
  have hstable : (prefixWord ++ tailWord_594806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594806).length < 2 ^ (prefixWord ++ tailWord_594806).sum := by decide
  have hdescent : baseEnd_594806 < baseStart_594806 := by decide
  rcases family_descends (prefixWord ++ tailWord_594806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594809 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 3, 2, 4]
def baseStart_594809 : Nat := 118140960795 + 594809 * 2 ^ 59
def prefixEnd_594809 : Nat := 4983230072969 + 3 ^ 40 * 594809 * 2
def baseEnd_594809 : Nat := 305422914620268540752029

theorem tailTrace_594809 : CollatzResearch.WordTrace tailWord_594809 prefixEnd_594809 305422914620268540752029 := by
  unfold tailWord_594809
  simp only [CollatzResearch.WordTrace]
  refine ⟨21694466502116053134691481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14462977668077368756460987 21694466502116053134691481)
  ·
    refine ⟨16270849876587039851018611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21694466502116053134691481 16270849876587039851018611)
    ·
      refine ⟨24406274814880559776527917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16270849876587039851018611 24406274814880559776527917)
      ·
        refine ⟨9152353055580209916197969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24406274814880559776527917 9152353055580209916197969)
        ·
          refine ⟨6864264791685157437148477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9152353055580209916197969 6864264791685157437148477)
          ·
            refine ⟨2574099296881934038930679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6864264791685157437148477 2574099296881934038930679)
            ·
              refine ⟨3861148945322901058396019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2574099296881934038930679 3861148945322901058396019)
              ·
                refine ⟨5791723417984351587594029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3861148945322901058396019 5791723417984351587594029)
                ·
                  refine ⟨2171896281744131845347761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5791723417984351587594029 2171896281744131845347761)
                  ·
                    refine ⟨1628922211308098884010821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2171896281744131845347761 1628922211308098884010821)
                    ·
                      refine ⟨305422914620268540752029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1628922211308098884010821 305422914620268540752029)
                      ·
                        rfl

theorem cell23_594809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_594809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594809 prefixEnd_594809 := by exact prefixLift 594809
  have htrace : WordTrace (prefixWord ++ tailWord_594809) baseStart_594809 baseEnd_594809 := by
    simpa [prefixWord, tailWord_594809, baseEnd_594809] using wordTrace_append hprefix tailTrace_594809
  have hstable : (prefixWord ++ tailWord_594809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594809).length < 2 ^ (prefixWord ++ tailWord_594809).sum := by decide
  have hdescent : baseEnd_594809 < baseStart_594809 := by decide
  rcases family_descends (prefixWord ++ tailWord_594809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594823 : List Nat := [1, 1, 4, 2, 3, 2, 2, 2, 2, 4]
def baseStart_594823 : Nat := 118140960795 + 594823 * 2 ^ 59
def prefixEnd_594823 : Nat := 4983230072969 + 3 ^ 40 * 594823 * 2
def baseEnd_594823 : Nat := 101810034449810495325655

theorem tailTrace_594823 : CollatzResearch.WordTrace tailWord_594823 prefixEnd_594823 101810034449810495325655 := by
  unfold tailWord_594823
  simp only [CollatzResearch.WordTrace]
  refine ⟨21694977124065333525701123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14463318082710222350467415 21694977124065333525701123)
  ·
    refine ⟨32542465686098000288551685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21694977124065333525701123 32542465686098000288551685)
    ·
      refine ⟨6101712316143375054103441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32542465686098000288551685 6101712316143375054103441)
      ·
        refine ⟨4576284237107531290577581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6101712316143375054103441 4576284237107531290577581)
        ·
          refine ⟨1716106588915324233966593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4576284237107531290577581 1716106588915324233966593)
          ·
            refine ⟨1287079941686493175474945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1716106588915324233966593 1287079941686493175474945)
            ·
              refine ⟨965309956264869881606209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1287079941686493175474945 965309956264869881606209)
              ·
                refine ⟨723982467198652411204657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 965309956264869881606209 723982467198652411204657)
                ·
                  refine ⟨542986850398989308403493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 723982467198652411204657 542986850398989308403493)
                  ·
                    refine ⟨101810034449810495325655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 542986850398989308403493 101810034449810495325655)
                    ·
                      rfl

theorem cell23_594823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_594823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594823 prefixEnd_594823 := by exact prefixLift 594823
  have htrace : WordTrace (prefixWord ++ tailWord_594823) baseStart_594823 baseEnd_594823 := by
    simpa [prefixWord, tailWord_594823, baseEnd_594823] using wordTrace_append hprefix tailTrace_594823
  have hstable : (prefixWord ++ tailWord_594823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594823).length < 2 ^ (prefixWord ++ tailWord_594823).sum := by decide
  have hdescent : baseEnd_594823 < baseStart_594823 := by decide
  rcases family_descends (prefixWord ++ tailWord_594823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594870 : List Nat := [5, 1, 4, 1, 1, 1, 10]
def baseStart_594870 : Nat := 118140960795 + 594870 * 2 ^ 59
def prefixEnd_594870 : Nat := 4983230072969 + 3 ^ 40 * 594870 * 2
def baseEnd_594870 : Nat := 3771039962224602494929

theorem tailTrace_594870 : CollatzResearch.WordTrace tailWord_594870 prefixEnd_594870 3771039962224602494929 := by
  unfold tailWord_594870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1356043209680941284541379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14464460903263373701774709 1356043209680941284541379)
  ·
    refine ⟨2034064814521411926812069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1356043209680941284541379 2034064814521411926812069)
    ·
      refine ⟨381387152722764736277263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2034064814521411926812069 381387152722764736277263)
      ·
        refine ⟨572080729084147104415895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381387152722764736277263 572080729084147104415895)
        ·
          refine ⟨858121093626220656623843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572080729084147104415895 858121093626220656623843)
          ·
            refine ⟨1287181640439330984935765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 858121093626220656623843 1287181640439330984935765)
            ·
              refine ⟨3771039962224602494929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1287181640439330984935765 3771039962224602494929)
              ·
                rfl

theorem cell23_594870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 10].length) (baseStart_594870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594870 prefixEnd_594870 := by exact prefixLift 594870
  have htrace : WordTrace (prefixWord ++ tailWord_594870) baseStart_594870 baseEnd_594870 := by
    simpa [prefixWord, tailWord_594870, baseEnd_594870] using wordTrace_append hprefix tailTrace_594870
  have hstable : (prefixWord ++ tailWord_594870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594870).length < 2 ^ (prefixWord ++ tailWord_594870).sum := by decide
  have hdescent : baseEnd_594870 < baseStart_594870 := by decide
  rcases family_descends (prefixWord ++ tailWord_594870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594880 : List Nat := [2, 1, 1, 2, 3, 5, 1, 2, 2, 1, 3]
def baseStart_594880 : Nat := 118140960795 + 594880 * 2 ^ 59
def prefixEnd_594880 : Nat := 4983230072969 + 3 ^ 40 * 594880 * 2
def baseEnd_594880 : Nat := 305459371746737762964203

theorem tailTrace_594880 : CollatzResearch.WordTrace tailWord_594880 prefixEnd_594880 305459371746737762964203 := by
  unfold tailWord_594880
  simp only [CollatzResearch.WordTrace]
  refine ⟨10848528042429416130263047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14464704056572554840350729 10848528042429416130263047)
  ·
    refine ⟨16272792063644124195394571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10848528042429416130263047 16272792063644124195394571)
    ·
      refine ⟨24409188095466186293091857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16272792063644124195394571 24409188095466186293091857)
      ·
        refine ⟨18306891071599639719818893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24409188095466186293091857 18306891071599639719818893)
        ·
          refine ⟨6865084151849864894932085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18306891071599639719818893 6865084151849864894932085)
          ·
            refine ⟨643601639235924833899883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6865084151849864894932085 643601639235924833899883)
            ·
              refine ⟨965402458853887250849825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 643601639235924833899883 965402458853887250849825)
              ·
                refine ⟨724051844140415438137369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 965402458853887250849825 724051844140415438137369)
                ·
                  refine ⟨543038883105311578603027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 724051844140415438137369 543038883105311578603027)
                  ·
                    refine ⟨814558324657967367904541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 543038883105311578603027 814558324657967367904541)
                    ·
                      refine ⟨305459371746737762964203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 814558324657967367904541 305459371746737762964203)
                      ·
                        rfl

theorem cell23_594880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 2, 1, 3].length) (baseStart_594880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594880 prefixEnd_594880 := by exact prefixLift 594880
  have htrace : WordTrace (prefixWord ++ tailWord_594880) baseStart_594880 baseEnd_594880 := by
    simpa [prefixWord, tailWord_594880, baseEnd_594880] using wordTrace_append hprefix tailTrace_594880
  have hstable : (prefixWord ++ tailWord_594880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594880).length < 2 ^ (prefixWord ++ tailWord_594880).sum := by decide
  have hdescent : baseEnd_594880 < baseStart_594880 := by decide
  rcases family_descends (prefixWord ++ tailWord_594880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594954 : List Nat := [3, 1, 2, 2, 3, 3, 2, 1, 2, 2, 2]
def baseStart_594954 : Nat := 118140960795 + 594954 * 2 ^ 59
def prefixEnd_594954 : Nat := 4983230072969 + 3 ^ 40 * 594954 * 2
def baseEnd_594954 : Nat := 305497369315170473438863

theorem tailTrace_594954 : CollatzResearch.WordTrace tailWord_594954 prefixEnd_594954 305497369315170473438863 := by
  unfold tailWord_594954
  simp only [CollatzResearch.WordTrace]
  refine ⟨5424938771647685724679979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14466503391060495265813277 5424938771647685724679979)
  ·
    refine ⟨8137408157471528587019969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5424938771647685724679979 8137408157471528587019969)
    ·
      refine ⟨6103056118103646440264977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8137408157471528587019969 6103056118103646440264977)
      ·
        refine ⟨4577292088577734830198733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6103056118103646440264977 4577292088577734830198733)
        ·
          refine ⟨1716484533216650561324525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4577292088577734830198733 1716484533216650561324525)
          ·
            refine ⟨643681699956243960496697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1716484533216650561324525 643681699956243960496697)
            ·
              refine ⟨482761274967182970372523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 643681699956243960496697 482761274967182970372523)
              ·
                refine ⟨724141912450774455558785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 482761274967182970372523 724141912450774455558785)
                ·
                  refine ⟨543106434338080841669089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 724141912450774455558785 543106434338080841669089)
                  ·
                    refine ⟨407329825753560631251817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 543106434338080841669089 407329825753560631251817)
                    ·
                      refine ⟨305497369315170473438863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 407329825753560631251817 305497369315170473438863)
                      ·
                        rfl

theorem cell23_594954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_594954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594954 prefixEnd_594954 := by exact prefixLift 594954
  have htrace : WordTrace (prefixWord ++ tailWord_594954) baseStart_594954 baseEnd_594954 := by
    simpa [prefixWord, tailWord_594954, baseEnd_594954] using wordTrace_append hprefix tailTrace_594954
  have hstable : (prefixWord ++ tailWord_594954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594954).length < 2 ^ (prefixWord ++ tailWord_594954).sum := by decide
  have hdescent : baseEnd_594954 < baseStart_594954 := by decide
  rcases family_descends (prefixWord ++ tailWord_594954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594969 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 2, 8]
def baseStart_594969 : Nat := 118140960795 + 594969 * 2 ^ 59
def prefixEnd_594969 : Nat := 4983230072969 + 3 ^ 40 * 594969 * 2
def baseEnd_594969 : Nat := 101835023841662638250431

theorem tailTrace_594969 : CollatzResearch.WordTrace tailWord_594969 prefixEnd_594969 101835023841662638250431 := by
  unfold tailWord_594969
  simp only [CollatzResearch.WordTrace]
  refine ⟨21700302181536400460515961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14466868121024266973677307 21700302181536400460515961)
  ·
    refine ⟨16275226636152300345386971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21700302181536400460515961 16275226636152300345386971)
    ·
      refine ⟨24412839954228450518080457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16275226636152300345386971 24412839954228450518080457)
      ·
        refine ⟨18309629965671337888560343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24412839954228450518080457 18309629965671337888560343)
        ·
          refine ⟨27464444948507006832840515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18309629965671337888560343 27464444948507006832840515)
          ·
            refine ⟨41196667422760510249260773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27464444948507006832840515 41196667422760510249260773)
            ·
              refine ⟨7724375141767595671736395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41196667422760510249260773 7724375141767595671736395)
              ·
                refine ⟨11586562712651393507604593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7724375141767595671736395 11586562712651393507604593)
                ·
                  refine ⟨8689922034488545130703445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11586562712651393507604593 8689922034488545130703445)
                  ·
                    refine ⟨101835023841662638250431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8689922034488545130703445 101835023841662638250431)
                    ·
                      rfl

theorem cell23_594969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 8].length) (baseStart_594969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594969 prefixEnd_594969 := by exact prefixLift 594969
  have htrace : WordTrace (prefixWord ++ tailWord_594969) baseStart_594969 baseEnd_594969 := by
    simpa [prefixWord, tailWord_594969, baseEnd_594969] using wordTrace_append hprefix tailTrace_594969
  have hstable : (prefixWord ++ tailWord_594969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594969).length < 2 ^ (prefixWord ++ tailWord_594969).sum := by decide
  have hdescent : baseEnd_594969 < baseStart_594969 := by decide
  rcases family_descends (prefixWord ++ tailWord_594969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594983 : List Nat := [1, 1, 7, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_594983 : Nat := 118140960795 + 594983 * 2 ^ 59
def prefixEnd_594983 : Nat := 4983230072969 + 3 ^ 40 * 594983 * 2
def baseEnd_594983 : Nat := 305512260254150859976229

theorem tailTrace_594983 : CollatzResearch.WordTrace tailWord_594983 prefixEnd_594983 305512260254150859976229 := by
  unfold tailWord_594983
  simp only [CollatzResearch.WordTrace]
  refine ⟨21700812803485680851525603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14467208535657120567683735 21700812803485680851525603)
  ·
    refine ⟨32551219205228521277288405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21700812803485680851525603 32551219205228521277288405)
    ·
      refine ⟨762919200122543467436447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 32551219205228521277288405 762919200122543467436447)
      ·
        refine ⟨1144378800183815201154671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 762919200122543467436447 1144378800183815201154671)
        ·
          refine ⟨1716568200275722801732007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1144378800183815201154671 1716568200275722801732007)
          ·
            refine ⟨2574852300413584202598011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1716568200275722801732007 2574852300413584202598011)
            ·
              refine ⟨3862278450620376303897017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2574852300413584202598011 3862278450620376303897017)
              ·
                refine ⟨2896708837965282227922763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3862278450620376303897017 2896708837965282227922763)
                ·
                  refine ⟨4345063256947923341884145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2896708837965282227922763 4345063256947923341884145)
                  ·
                    refine ⟨3258797442710942506413109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4345063256947923341884145 3258797442710942506413109)
                    ·
                      refine ⟨305512260254150859976229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3258797442710942506413109 305512260254150859976229)
                      ·
                        rfl

theorem cell23_594983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_594983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594983 prefixEnd_594983 := by exact prefixLift 594983
  have htrace : WordTrace (prefixWord ++ tailWord_594983) baseStart_594983 baseEnd_594983 := by
    simpa [prefixWord, tailWord_594983, baseEnd_594983] using wordTrace_append hprefix tailTrace_594983
  have hstable : (prefixWord ++ tailWord_594983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594983).length < 2 ^ (prefixWord ++ tailWord_594983).sum := by decide
  have hdescent : baseEnd_594983 < baseStart_594983 := by decide
  rcases family_descends (prefixWord ++ tailWord_594983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594993 : List Nat := [1, 2, 2, 3, 1, 2, 2, 2, 2, 4, 2]
def baseStart_594993 : Nat := 118140960795 + 594993 * 2 ^ 59
def prefixEnd_594993 : Nat := 4983230072969 + 3 ^ 40 * 594993 * 2
def baseEnd_594993 : Nat := 305517395060695820851183

theorem tailTrace_594993 : CollatzResearch.WordTrace tailWord_594993 prefixEnd_594993 305517395060695820851183 := by
  unfold tailWord_594993
  simp only [CollatzResearch.WordTrace]
  refine ⟨21701177533449452559389633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14467451688966301706259755 21701177533449452559389633)
  ·
    refine ⟨16275883150087089419542225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21701177533449452559389633 16275883150087089419542225)
    ·
      refine ⟨12206912362565317064656669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16275883150087089419542225 12206912362565317064656669)
      ·
        refine ⟨4577592135961993899246251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12206912362565317064656669 4577592135961993899246251)
        ·
          refine ⟨6866388203942990848869377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4577592135961993899246251 6866388203942990848869377)
          ·
            refine ⟨5149791152957243136652033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6866388203942990848869377 5149791152957243136652033)
            ·
              refine ⟨3862343364717932352489025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5149791152957243136652033 3862343364717932352489025)
              ·
                refine ⟨2896757523538449264366769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3862343364717932352489025 2896757523538449264366769)
                ·
                  refine ⟨2172568142653836948275077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2896757523538449264366769 2172568142653836948275077)
                  ·
                    refine ⟨407356526747594427801577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2172568142653836948275077 407356526747594427801577)
                    ·
                      refine ⟨305517395060695820851183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 407356526747594427801577 305517395060695820851183)
                      ·
                        rfl

theorem cell23_594993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_594993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_594993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_594993 prefixEnd_594993 := by exact prefixLift 594993
  have htrace : WordTrace (prefixWord ++ tailWord_594993) baseStart_594993 baseEnd_594993 := by
    simpa [prefixWord, tailWord_594993, baseEnd_594993] using wordTrace_append hprefix tailTrace_594993
  have hstable : (prefixWord ++ tailWord_594993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594993).length < 2 ^ (prefixWord ++ tailWord_594993).sum := by decide
  have hdescent : baseEnd_594993 < baseStart_594993 := by decide
  rcases family_descends (prefixWord ++ tailWord_594993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595016 : List Nat := [2, 1, 3, 1, 1, 1, 3, 5, 6]
def baseStart_595016 : Nat := 118140960795 + 595016 * 2 ^ 59
def prefixEnd_595016 : Nat := 4983230072969 + 3 ^ 40 * 595016 * 2
def baseEnd_595016 : Nat := 33947689457305470095953

theorem tailTrace_595016 : CollatzResearch.WordTrace tailWord_595016 prefixEnd_595016 33947689457305470095953 := by
  unfold tailWord_595016
  simp only [CollatzResearch.WordTrace]
  refine ⟨10851008206183063743738451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14468010941577418324984601 10851008206183063743738451)
  ·
    refine ⟨16276512309274595615607677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10851008206183063743738451 16276512309274595615607677)
    ·
      refine ⟨6103692115977973355852879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16276512309274595615607677 6103692115977973355852879)
      ·
        refine ⟨9155538173966960033779319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6103692115977973355852879 9155538173966960033779319)
        ·
          refine ⟨13733307260950440050668979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9155538173966960033779319 13733307260950440050668979)
          ·
            refine ⟨20599960891425660076003469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13733307260950440050668979 20599960891425660076003469)
            ·
              refine ⟨7724985334284622528501301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20599960891425660076003469 7724985334284622528501301)
              ·
                refine ⟨724217375089183362046997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7724985334284622528501301 724217375089183362046997)
                ·
                  refine ⟨33947689457305470095953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 724217375089183362046997 33947689457305470095953)
                  ·
                    rfl

theorem cell23_595016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 6].length) (baseStart_595016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595016 prefixEnd_595016 := by exact prefixLift 595016
  have htrace : WordTrace (prefixWord ++ tailWord_595016) baseStart_595016 baseEnd_595016 := by
    simpa [prefixWord, tailWord_595016, baseEnd_595016] using wordTrace_append hprefix tailTrace_595016
  have hstable : (prefixWord ++ tailWord_595016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595016).length < 2 ^ (prefixWord ++ tailWord_595016).sum := by decide
  have hdescent : baseEnd_595016 < baseStart_595016 := by decide
  rcases family_descends (prefixWord ++ tailWord_595016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595043 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 7, 1, 3]
def baseStart_595043 : Nat := 118140960795 + 595043 * 2 ^ 59
def prefixEnd_595043 : Nat := 4983230072969 + 3 ^ 40 * 595043 * 2
def baseEnd_595043 : Nat := 305543069093420625225953

theorem tailTrace_595043 : CollatzResearch.WordTrace tailWord_595043 prefixEnd_595043 305543069093420625225953 := by
  unfold tailWord_595043
  simp only [CollatzResearch.WordTrace]
  refine ⟨21703001183268311098709783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14468667455512207399139855 21703001183268311098709783)
  ·
    refine ⟨32554501774902466648064675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21703001183268311098709783 32554501774902466648064675)
    ·
      refine ⟨48831752662353699972097013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32554501774902466648064675 48831752662353699972097013)
      ·
        refine ⟨4577976812095659372384095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48831752662353699972097013 4577976812095659372384095)
        ·
          refine ⟨6866965218143489058576143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4577976812095659372384095 6866965218143489058576143)
          ·
            refine ⟨10300447827215233587864215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6866965218143489058576143 10300447827215233587864215)
            ·
              refine ⟨15450671740822850381796323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10300447827215233587864215 15450671740822850381796323)
              ·
                refine ⟨23176007611234275572694485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15450671740822850381796323 23176007611234275572694485)
                ·
                  refine ⟨543187678388303333735027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 23176007611234275572694485 543187678388303333735027)
                  ·
                    refine ⟨814781517582455000602541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 543187678388303333735027 814781517582455000602541)
                    ·
                      refine ⟨305543069093420625225953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 814781517582455000602541 305543069093420625225953)
                      ·
                        rfl

theorem cell23_595043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_595043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595043 prefixEnd_595043 := by exact prefixLift 595043
  have htrace : WordTrace (prefixWord ++ tailWord_595043) baseStart_595043 baseEnd_595043 := by
    simpa [prefixWord, tailWord_595043, baseEnd_595043] using wordTrace_append hprefix tailTrace_595043
  have hstable : (prefixWord ++ tailWord_595043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595043).length < 2 ^ (prefixWord ++ tailWord_595043).sum := by decide
  have hdescent : baseEnd_595043 < baseStart_595043 := by decide
  rcases family_descends (prefixWord ++ tailWord_595043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595050 : List Nat := [3, 1, 3, 2, 2, 3, 1, 2, 6]
def baseStart_595050 : Nat := 118140960795 + 595050 * 2 ^ 59
def prefixEnd_595050 : Nat := 4983230072969 + 3 ^ 40 * 595050 * 2
def baseEnd_595050 : Nat := 33949629273111344204269

theorem tailTrace_595050 : CollatzResearch.WordTrace tailWord_595050 prefixEnd_595050 33949629273111344204269 := by
  unfold tailWord_595050
  simp only [CollatzResearch.WordTrace]
  refine ⟨5425814123560737823553651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14468837662828634196143069 5425814123560737823553651)
  ·
    refine ⟨8138721185341106735330477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5425814123560737823553651 8138721185341106735330477)
    ·
      refine ⟨3052020444502915025748929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8138721185341106735330477 3052020444502915025748929)
      ·
        refine ⟨2289015333377186269311697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3052020444502915025748929 2289015333377186269311697)
        ·
          refine ⟨1716761500032889701983773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2289015333377186269311697 1716761500032889701983773)
          ·
            refine ⟨643785562512333638243915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1716761500032889701983773 643785562512333638243915)
            ·
              refine ⟨965678343768500457365873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 643785562512333638243915 965678343768500457365873)
              ·
                refine ⟨724258757826375343024405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 965678343768500457365873 724258757826375343024405)
                ·
                  refine ⟨33949629273111344204269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 724258757826375343024405 33949629273111344204269)
                  ·
                    rfl

theorem cell23_595050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 6].length) (baseStart_595050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595050 prefixEnd_595050 := by exact prefixLift 595050
  have htrace : WordTrace (prefixWord ++ tailWord_595050) baseStart_595050 baseEnd_595050 := by
    simpa [prefixWord, tailWord_595050, baseEnd_595050] using wordTrace_append hprefix tailTrace_595050
  have hstable : (prefixWord ++ tailWord_595050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595050).length < 2 ^ (prefixWord ++ tailWord_595050).sum := by decide
  have hdescent : baseEnd_595050 < baseStart_595050 := by decide
  rcases family_descends (prefixWord ++ tailWord_595050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595100 : List Nat := [2, 2, 3, 2, 1, 2, 2, 3, 1, 1, 4]
def baseStart_595100 : Nat := 118140960795 + 595100 * 2 ^ 59
def prefixEnd_595100 : Nat := 4983230072969 + 3 ^ 40 * 595100 * 2
def baseEnd_595100 : Nat := 305572337490726902213191

theorem tailTrace_595100 : CollatzResearch.WordTrace tailWord_595100 prefixEnd_595100 305572337490726902213191 := by
  unfold tailWord_595100
  simp only [CollatzResearch.WordTrace]
  refine ⟨10852540072030904916767377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14470053429374539889023169 10852540072030904916767377)
  ·
    refine ⟨8139405054023178687575533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10852540072030904916767377 8139405054023178687575533)
    ·
      refine ⟨3052276895258692007840825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8139405054023178687575533 3052276895258692007840825)
      ·
        refine ⟨2289207671444019005880619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3052276895258692007840825 2289207671444019005880619)
        ·
          refine ⟨3433811507166028508820929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2289207671444019005880619 3433811507166028508820929)
          ·
            refine ⟨2575358630374521381615697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3433811507166028508820929 2575358630374521381615697)
            ·
              refine ⟨1931518972780891036211773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2575358630374521381615697 1931518972780891036211773)
              ·
                refine ⟨724319614792834138579415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1931518972780891036211773 724319614792834138579415)
                ·
                  refine ⟨1086479422189251207869123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 724319614792834138579415 1086479422189251207869123)
                  ·
                    refine ⟨1629719133283876811803685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1086479422189251207869123 1629719133283876811803685)
                    ·
                      refine ⟨305572337490726902213191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1629719133283876811803685 305572337490726902213191)
                      ·
                        rfl

theorem cell23_595100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_595100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595100 prefixEnd_595100 := by exact prefixLift 595100
  have htrace : WordTrace (prefixWord ++ tailWord_595100) baseStart_595100 baseEnd_595100 := by
    simpa [prefixWord, tailWord_595100, baseEnd_595100] using wordTrace_append hprefix tailTrace_595100
  have hstable : (prefixWord ++ tailWord_595100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595100).length < 2 ^ (prefixWord ++ tailWord_595100).sum := by decide
  have hdescent : baseEnd_595100 < baseStart_595100 := by decide
  rcases family_descends (prefixWord ++ tailWord_595100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595111 : List Nat := [1, 1, 6, 2, 1, 2, 3, 2, 1, 1, 3]
def baseStart_595111 : Nat := 118140960795 + 595111 * 2 ^ 59
def prefixEnd_595111 : Nat := 4983230072969 + 3 ^ 40 * 595111 * 2
def baseEnd_595111 : Nat := 305577985777926359175641

theorem tailTrace_595111 : CollatzResearch.WordTrace tailWord_595111 prefixEnd_595111 305577985777926359175641 := by
  unfold tailWord_595111
  simp only [CollatzResearch.WordTrace]
  refine ⟨21705481347021958712185187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14470320898014639141456791 21705481347021958712185187)
  ·
    refine ⟨32558222020532938068277781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21705481347021958712185187 32558222020532938068277781)
    ·
      refine ⟨1526166657212481471950521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32558222020532938068277781 1526166657212481471950521)
      ·
        refine ⟨1144624992909361103962891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1526166657212481471950521 1144624992909361103962891)
        ·
          refine ⟨1716937489364041655944337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1144624992909361103962891 1716937489364041655944337)
          ·
            refine ⟨1287703117023031241958253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1716937489364041655944337 1287703117023031241958253)
            ·
              refine ⟨482888668883636715734345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1287703117023031241958253 482888668883636715734345)
              ·
                refine ⟨362166501662727536800759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 482888668883636715734345 362166501662727536800759)
                ·
                  refine ⟨543249752494091305201139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 362166501662727536800759 543249752494091305201139)
                  ·
                    refine ⟨814874628741136957801709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 543249752494091305201139 814874628741136957801709)
                    ·
                      refine ⟨305577985777926359175641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 814874628741136957801709 305577985777926359175641)
                      ·
                        rfl

theorem cell23_595111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_595111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595111 prefixEnd_595111 := by exact prefixLift 595111
  have htrace : WordTrace (prefixWord ++ tailWord_595111) baseStart_595111 baseEnd_595111 := by
    simpa [prefixWord, tailWord_595111, baseEnd_595111] using wordTrace_append hprefix tailTrace_595111
  have hstable : (prefixWord ++ tailWord_595111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595111).length < 2 ^ (prefixWord ++ tailWord_595111).sum := by decide
  have hdescent : baseEnd_595111 < baseStart_595111 := by decide
  rcases family_descends (prefixWord ++ tailWord_595111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595137 : List Nat := [1, 2, 6, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_595137 : Nat := 118140960795 + 595137 * 2 ^ 59
def prefixEnd_595137 : Nat := 4983230072969 + 3 ^ 40 * 595137 * 2
def baseEnd_595137 : Nat := 305591336274943257450521

theorem tailTrace_595137 : CollatzResearch.WordTrace tailWord_595137 prefixEnd_595137 305591336274943257450521 := by
  unfold tailWord_595137
  simp only [CollatzResearch.WordTrace]
  refine ⟨21706429644927765152631665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14470953096618510101754443 21706429644927765152631665)
  ·
    refine ⟨16279822233695823864473749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21706429644927765152631665 16279822233695823864473749)
    ·
      refine ⟨763116667204491743647207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16279822233695823864473749 763116667204491743647207)
      ·
        refine ⟨1144675000806737615470811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 763116667204491743647207 1144675000806737615470811)
        ·
          refine ⟨1717012501210106423206217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1144675000806737615470811 1717012501210106423206217)
          ·
            refine ⟨1287759375907579817404663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1717012501210106423206217 1287759375907579817404663)
            ·
              refine ⟨1931639063861369726106995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1287759375907579817404663 1931639063861369726106995)
              ·
                refine ⟨2897458595792054589160493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1931639063861369726106995 2897458595792054589160493)
                ·
                  refine ⟨1086546973422020470935185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2897458595792054589160493 1086546973422020470935185)
                  ·
                    refine ⟨814910230066515353201389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1086546973422020470935185 814910230066515353201389)
                    ·
                      refine ⟨305591336274943257450521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 814910230066515353201389 305591336274943257450521)
                      ·
                        rfl

theorem cell23_595137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_595137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595137 prefixEnd_595137 := by exact prefixLift 595137
  have htrace : WordTrace (prefixWord ++ tailWord_595137) baseStart_595137 baseEnd_595137 := by
    simpa [prefixWord, tailWord_595137, baseEnd_595137] using wordTrace_append hprefix tailTrace_595137
  have hstable : (prefixWord ++ tailWord_595137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595137).length < 2 ^ (prefixWord ++ tailWord_595137).sum := by decide
  have hdescent : baseEnd_595137 < baseStart_595137 := by decide
  rcases family_descends (prefixWord ++ tailWord_595137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595193 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 2, 4, 3]
def baseStart_595193 : Nat := 118140960795 + 595193 * 2 ^ 59
def prefixEnd_595193 : Nat := 4983230072969 + 3 ^ 40 * 595193 * 2
def baseEnd_595193 : Nat := 305620091191595038350263

theorem tailTrace_595193 : CollatzResearch.WordTrace tailWord_595193 prefixEnd_595193 305620091191595038350263 := by
  unfold tailWord_595193
  simp only [CollatzResearch.WordTrace]
  refine ⟨21708472132724886716670233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14472314755149924477780155 21708472132724886716670233)
  ·
    refine ⟨16281354099543665037502675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21708472132724886716670233 16281354099543665037502675)
    ·
      refine ⟨24422031149315497556254013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16281354099543665037502675 24422031149315497556254013)
      ·
        refine ⟨9158261680993311583595255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24422031149315497556254013 9158261680993311583595255)
        ·
          refine ⟨13737392521489967375392883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9158261680993311583595255 13737392521489967375392883)
          ·
            refine ⟨20606088782234951063089325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13737392521489967375392883 20606088782234951063089325)
            ·
              refine ⟨7727283293338106648658497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20606088782234951063089325 7727283293338106648658497)
              ·
                refine ⟨5795462470003579986493873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7727283293338106648658497 5795462470003579986493873)
                ·
                  refine ⟨4346596852502684989870405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5795462470003579986493873 4346596852502684989870405)
                  ·
                    refine ⟨814986909844253435600701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4346596852502684989870405 814986909844253435600701)
                    ·
                      refine ⟨305620091191595038350263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 814986909844253435600701 305620091191595038350263)
                      ·
                        rfl

theorem cell23_595193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_595193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595193 prefixEnd_595193 := by exact prefixLift 595193
  have htrace : WordTrace (prefixWord ++ tailWord_595193) baseStart_595193 baseEnd_595193 := by
    simpa [prefixWord, tailWord_595193, baseEnd_595193] using wordTrace_append hprefix tailTrace_595193
  have hstable : (prefixWord ++ tailWord_595193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595193).length < 2 ^ (prefixWord ++ tailWord_595193).sum := by decide
  have hdescent : baseEnd_595193 < baseStart_595193 := by decide
  rcases family_descends (prefixWord ++ tailWord_595193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595218 : List Nat := [3, 2, 4, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_595218 : Nat := 118140960795 + 595218 * 2 ^ 59
def prefixEnd_595218 : Nat := 4983230072969 + 3 ^ 40 * 595218 * 2
def baseEnd_595218 : Nat := 305632928207957440537649

theorem tailTrace_595218 : CollatzResearch.WordTrace tailWord_595218 prefixEnd_595218 305632928207957440537649 := by
  unfold tailWord_595218
  simp only [CollatzResearch.WordTrace]
  refine ⟨5427345989408578996582577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14472922638422877324220205 5427345989408578996582577)
  ·
    refine ⟨4070509492056434247436933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5427345989408578996582577 4070509492056434247436933)
    ·
      refine ⟨763220529760581421394425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4070509492056434247436933 763220529760581421394425)
      ·
        refine ⟨572415397320436066045819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 763220529760581421394425 572415397320436066045819)
        ·
          refine ⟨858623095980654099068729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572415397320436066045819 858623095980654099068729)
          ·
            refine ⟨643967321985490574301547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 858623095980654099068729 643967321985490574301547)
            ·
              refine ⟨965950982978235861452321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 643967321985490574301547 965950982978235861452321)
              ·
                refine ⟨724463237233676896089241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 965950982978235861452321 724463237233676896089241)
                ·
                  refine ⟨543347427925257672066931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 724463237233676896089241 543347427925257672066931)
                  ·
                    refine ⟨815021141887886508100397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 543347427925257672066931 815021141887886508100397)
                    ·
                      refine ⟨305632928207957440537649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 815021141887886508100397 305632928207957440537649)
                      ·
                        rfl

theorem cell23_595218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_595218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595218 prefixEnd_595218 := by exact prefixLift 595218
  have htrace : WordTrace (prefixWord ++ tailWord_595218) baseStart_595218 baseEnd_595218 := by
    simpa [prefixWord, tailWord_595218, baseEnd_595218] using wordTrace_append hprefix tailTrace_595218
  have hstable : (prefixWord ++ tailWord_595218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595218).length < 2 ^ (prefixWord ++ tailWord_595218).sum := by decide
  have hdescent : baseEnd_595218 < baseStart_595218 := by decide
  rcases family_descends (prefixWord ++ tailWord_595218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595224 : List Nat := [2, 1, 2, 3, 1, 3, 3, 2, 2, 2, 2]
def baseStart_595224 : Nat := 118140960795 + 595224 * 2 ^ 59
def prefixEnd_595224 : Nat := 4983230072969 + 3 ^ 40 * 595224 * 2
def baseEnd_595224 : Nat := 305636009091884417062621

theorem tailTrace_595224 : CollatzResearch.WordTrace tailWord_595224 prefixEnd_595224 305636009091884417062621 := by
  unfold tailWord_595224
  simp only [CollatzResearch.WordTrace]
  refine ⟨10854801397806289505524363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14473068530408386007365817 10854801397806289505524363)
  ·
    refine ⟨16282202096709434258286545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10854801397806289505524363 16282202096709434258286545)
    ·
      refine ⟨12211651572532075693714909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16282202096709434258286545 12211651572532075693714909)
      ·
        refine ⟨4579369339699528385143091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12211651572532075693714909 4579369339699528385143091)
        ·
          refine ⟨6869054009549292577714637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4579369339699528385143091 6869054009549292577714637)
          ·
            refine ⟨2575895253580984716642989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6869054009549292577714637 2575895253580984716642989)
            ·
              refine ⟨965960720092869268741121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2575895253580984716642989 965960720092869268741121)
              ·
                refine ⟨724470540069651951555841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 965960720092869268741121 724470540069651951555841)
                ·
                  refine ⟨543352905052238963666881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 724470540069651951555841 543352905052238963666881)
                  ·
                    refine ⟨407514678789179222750161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 543352905052238963666881 407514678789179222750161)
                    ·
                      refine ⟨305636009091884417062621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 407514678789179222750161 305636009091884417062621)
                      ·
                        rfl

theorem cell23_595224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_595224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595224 prefixEnd_595224 := by exact prefixLift 595224
  have htrace : WordTrace (prefixWord ++ tailWord_595224) baseStart_595224 baseEnd_595224 := by
    simpa [prefixWord, tailWord_595224, baseEnd_595224] using wordTrace_append hprefix tailTrace_595224
  have hstable : (prefixWord ++ tailWord_595224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595224).length < 2 ^ (prefixWord ++ tailWord_595224).sum := by decide
  have hdescent : baseEnd_595224 < baseStart_595224 := by decide
  rcases family_descends (prefixWord ++ tailWord_595224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595280 : List Nat := [2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 4]
def baseStart_595280 : Nat := 118140960795 + 595280 * 2 ^ 59
def prefixEnd_595280 : Nat := 4983230072969 + 3 ^ 40 * 595280 * 2
def baseEnd_595280 : Nat := 305664764008536197962363

theorem tailTrace_595280 : CollatzResearch.WordTrace tailWord_595280 prefixEnd_595280 305664764008536197962363 := by
  unfold tailWord_595280
  simp only [CollatzResearch.WordTrace]
  refine ⟨10855822641704850287543647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14474430188939800383391529 10855822641704850287543647)
  ·
    refine ⟨16283733962557275431315471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10855822641704850287543647 16283733962557275431315471)
    ·
      refine ⟨24425600943835913146973207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16283733962557275431315471 24425600943835913146973207)
      ·
        refine ⟨36638401415753869720459811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24425600943835913146973207 36638401415753869720459811)
        ·
          refine ⟨54957602123630804580689717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36638401415753869720459811 54957602123630804580689717)
          ·
            refine ⟨5152275199090387929439661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54957602123630804580689717 5152275199090387929439661)
            ·
              refine ⟨1932103199658895473539873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5152275199090387929439661 1932103199658895473539873)
              ·
                refine ⟨1449077399744171605154905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1932103199658895473539873 1449077399744171605154905)
                ·
                  refine ⟨1086808049808128703866179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1449077399744171605154905 1086808049808128703866179)
                  ·
                    refine ⟨1630212074712193055799269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1086808049808128703866179 1630212074712193055799269)
                    ·
                      refine ⟨305664764008536197962363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1630212074712193055799269 305664764008536197962363)
                      ·
                        rfl

theorem cell23_595280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 4].length) (baseStart_595280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595280 prefixEnd_595280 := by exact prefixLift 595280
  have htrace : WordTrace (prefixWord ++ tailWord_595280) baseStart_595280 baseEnd_595280 := by
    simpa [prefixWord, tailWord_595280, baseEnd_595280] using wordTrace_append hprefix tailTrace_595280
  have hstable : (prefixWord ++ tailWord_595280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595280).length < 2 ^ (prefixWord ++ tailWord_595280).sum := by decide
  have hdescent : baseEnd_595280 < baseStart_595280 := by decide
  rcases family_descends (prefixWord ++ tailWord_595280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595337 : List Nat := [1, 2, 1, 1, 7, 1, 2, 2, 6]
def baseStart_595337 : Nat := 118140960795 + 595337 * 2 ^ 59
def prefixEnd_595337 : Nat := 4983230072969 + 3 ^ 40 * 595337 * 2
def baseEnd_595337 : Nat := 33966003600649163883289

theorem tailTrace_595337 : CollatzResearch.WordTrace tailWord_595337 prefixEnd_595337 33966003600649163883289 := by
  unfold tailWord_595337
  simp only [CollatzResearch.WordTrace]
  refine ⟨21713724244203199309912265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14475816162802132873274843 21713724244203199309912265)
  ·
    refine ⟨16285293183152399482434199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21713724244203199309912265 16285293183152399482434199)
    ·
      refine ⟨24427939774728599223651299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16285293183152399482434199 24427939774728599223651299)
      ·
        refine ⟨36641909662092898835476949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24427939774728599223651299 36641909662092898835476949)
        ·
          refine ⟨858794757705302316456491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 36641909662092898835476949 858794757705302316456491)
          ·
            refine ⟨1288192136557953474684737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 858794757705302316456491 1288192136557953474684737)
            ·
              refine ⟨966144102418465106013553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1288192136557953474684737 966144102418465106013553)
              ·
                refine ⟨724608076813848829510165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 966144102418465106013553 724608076813848829510165)
                ·
                  refine ⟨33966003600649163883289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 724608076813848829510165 33966003600649163883289)
                  ·
                    rfl

theorem cell23_595337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 6].length) (baseStart_595337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595337 prefixEnd_595337 := by exact prefixLift 595337
  have htrace : WordTrace (prefixWord ++ tailWord_595337) baseStart_595337 baseEnd_595337 := by
    simpa [prefixWord, tailWord_595337, baseEnd_595337] using wordTrace_append hprefix tailTrace_595337
  have hstable : (prefixWord ++ tailWord_595337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595337).length < 2 ^ (prefixWord ++ tailWord_595337).sum := by decide
  have hdescent : baseEnd_595337 < baseStart_595337 := by decide
  rcases family_descends (prefixWord ++ tailWord_595337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595367 : List Nat := [1, 1, 6, 1, 1, 1, 2, 4, 1, 5]
def baseStart_595367 : Nat := 118140960795 + 595367 * 2 ^ 59
def prefixEnd_595367 : Nat := 4983230072969 + 3 ^ 40 * 595367 * 2
def baseEnd_595367 : Nat := 101903145608492452524821

theorem tailTrace_595367 : CollatzResearch.WordTrace tailWord_595367 prefixEnd_595367 101903145608492452524821 := by
  unfold tailWord_595367
  simp only [CollatzResearch.WordTrace]
  refine ⟨21714818434094514433504355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14476545622729676289002903 21714818434094514433504355)
  ·
    refine ⟨32572227651141771650256533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21714818434094514433504355 32572227651141771650256533)
    ·
      refine ⟨1526823171147270546105775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32572227651141771650256533 1526823171147270546105775)
      ·
        refine ⟨2290234756720905819158663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1526823171147270546105775 2290234756720905819158663)
        ·
          refine ⟨3435352135081358728737995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2290234756720905819158663 3435352135081358728737995)
          ·
            refine ⟨5153028202622038093106993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3435352135081358728737995 5153028202622038093106993)
            ·
              refine ⟨3864771151966528569830245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5153028202622038093106993 3864771151966528569830245)
              ·
                refine ⟨724644590993724106843171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3864771151966528569830245 724644590993724106843171)
                ·
                  refine ⟨1086966886490586160264757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 724644590993724106843171 1086966886490586160264757)
                  ·
                    refine ⟨101903145608492452524821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1086966886490586160264757 101903145608492452524821)
                    ·
                      rfl

theorem cell23_595367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_595367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595367 prefixEnd_595367 := by exact prefixLift 595367
  have htrace : WordTrace (prefixWord ++ tailWord_595367) baseStart_595367 baseEnd_595367 := by
    simpa [prefixWord, tailWord_595367, baseEnd_595367] using wordTrace_append hprefix tailTrace_595367
  have hstable : (prefixWord ++ tailWord_595367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595367).length < 2 ^ (prefixWord ++ tailWord_595367).sum := by decide
  have hdescent : baseEnd_595367 < baseStart_595367 := by decide
  rcases family_descends (prefixWord ++ tailWord_595367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595368 : List Nat := [2, 1, 6, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_595368 : Nat := 118140960795 + 595368 * 2 ^ 59
def prefixEnd_595368 : Nat := 4983230072969 + 3 ^ 40 * 595368 * 2
def baseEnd_595368 : Nat := 305709950306131853661959

theorem tailTrace_595368 : CollatzResearch.WordTrace tailWord_595368 prefixEnd_595368 305709950306131853661959 := by
  unfold tailWord_595368
  simp only [CollatzResearch.WordTrace]
  refine ⟨10857427453545445802145379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14476569938060594402860505 10857427453545445802145379)
  ·
    refine ⟨16286141180318168703218069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10857427453545445802145379 16286141180318168703218069)
    ·
      refine ⟨763412867827414157963347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16286141180318168703218069 763412867827414157963347)
      ·
        refine ⟨1145119301741121236945021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 763412867827414157963347 1145119301741121236945021)
        ·
          refine ⟨429419738152920463854383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1145119301741121236945021 429419738152920463854383)
          ·
            refine ⟨644129607229380695781575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429419738152920463854383 644129607229380695781575)
            ·
              refine ⟨966194410844071043672363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 644129607229380695781575 966194410844071043672363)
              ·
                refine ⟨1449291616266106565508545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 966194410844071043672363 1449291616266106565508545)
                ·
                  refine ⟨1086968712199579924131409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1449291616266106565508545 1086968712199579924131409)
                  ·
                    refine ⟨815226534149684943098557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1086968712199579924131409 815226534149684943098557)
                    ·
                      refine ⟨305709950306131853661959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 815226534149684943098557 305709950306131853661959)
                      ·
                        rfl

theorem cell23_595368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_595368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595368 prefixEnd_595368 := by exact prefixLift 595368
  have htrace : WordTrace (prefixWord ++ tailWord_595368) baseStart_595368 baseEnd_595368 := by
    simpa [prefixWord, tailWord_595368, baseEnd_595368] using wordTrace_append hprefix tailTrace_595368
  have hstable : (prefixWord ++ tailWord_595368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595368).length < 2 ^ (prefixWord ++ tailWord_595368).sum := by decide
  have hdescent : baseEnd_595368 < baseStart_595368 := by decide
  rcases family_descends (prefixWord ++ tailWord_595368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595381 : List Nat := [1, 3, 3, 2, 2, 1, 1, 5, 1, 1, 3]
def baseStart_595381 : Nat := 118140960795 + 595381 * 2 ^ 59
def prefixEnd_595381 : Nat := 4983230072969 + 3 ^ 40 * 595381 * 2
def baseEnd_595381 : Nat := 305716625554640302799399

theorem tailTrace_595381 : CollatzResearch.WordTrace tailWord_595381 prefixEnd_595381 305716625554640302799399 := by
  unfold tailWord_595381
  simp only [CollatzResearch.WordTrace]
  refine ⟨21715329056043794824513997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14476886037362529883009331 21715329056043794824513997)
  ·
    refine ⟨8143248396016423059192749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21715329056043794824513997 8143248396016423059192749)
    ·
      refine ⟨3053718148506158647197281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8143248396016423059192749 3053718148506158647197281)
      ·
        refine ⟨2290288611379618985397961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3053718148506158647197281 2290288611379618985397961)
        ·
          refine ⟨1717716458534714239048471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2290288611379618985397961 1717716458534714239048471)
          ·
            refine ⟨2576574687802071358572707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1717716458534714239048471 2576574687802071358572707)
            ·
              refine ⟨3864862031703107037859061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2576574687802071358572707 3864862031703107037859061)
              ·
                refine ⟨362330815472166284799287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3864862031703107037859061 362330815472166284799287)
                ·
                  refine ⟨543496223208249427198931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 362330815472166284799287 543496223208249427198931)
                  ·
                    refine ⟨815244334812374140798397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 543496223208249427198931 815244334812374140798397)
                    ·
                      refine ⟨305716625554640302799399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 815244334812374140798397 305716625554640302799399)
                      ·
                        rfl

theorem cell23_595381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_595381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595381 prefixEnd_595381 := by exact prefixLift 595381
  have htrace : WordTrace (prefixWord ++ tailWord_595381) baseStart_595381 baseEnd_595381 := by
    simpa [prefixWord, tailWord_595381, baseEnd_595381] using wordTrace_append hprefix tailTrace_595381
  have hstable : (prefixWord ++ tailWord_595381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595381).length < 2 ^ (prefixWord ++ tailWord_595381).sum := by decide
  have hdescent : baseEnd_595381 < baseStart_595381 := by decide
  rcases family_descends (prefixWord ++ tailWord_595381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595400 : List Nat := [2, 1, 3, 1, 3, 1, 2, 2, 1, 1, 6]
def baseStart_595400 : Nat := 118140960795 + 595400 * 2 ^ 59
def prefixEnd_595400 : Nat := 4983230072969 + 3 ^ 40 * 595400 * 2
def baseEnd_595400 : Nat := 305726381687075728461811

theorem tailTrace_595400 : CollatzResearch.WordTrace tailWord_595400 prefixEnd_595400 305726381687075728461811 := by
  unfold tailWord_595400
  simp only [CollatzResearch.WordTrace]
  refine ⟨10858011021487480534727827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14477348028649974046303769 10858011021487480534727827)
  ·
    refine ⟨16287016532231220802091741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10858011021487480534727827 16287016532231220802091741)
    ·
      refine ⟨6107631199586707800784403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16287016532231220802091741 6107631199586707800784403)
      ·
        refine ⟨9161446799380061701176605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6107631199586707800784403 9161446799380061701176605)
        ·
          refine ⟨3435542549767523137941227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9161446799380061701176605 3435542549767523137941227)
          ·
            refine ⟨5153313824651284706911841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3435542549767523137941227 5153313824651284706911841)
            ·
              refine ⟨3864985368488463530183881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5153313824651284706911841 3864985368488463530183881)
              ·
                refine ⟨2898739026366347647637911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3864985368488463530183881 2898739026366347647637911)
                ·
                  refine ⟨4348108539549521471456867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2898739026366347647637911 4348108539549521471456867)
                  ·
                    refine ⟨6522162809324282207185301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4348108539549521471456867 6522162809324282207185301)
                    ·
                      refine ⟨305726381687075728461811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6522162809324282207185301 305726381687075728461811)
                      ·
                        rfl

theorem cell23_595400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_595400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595400 prefixEnd_595400 := by exact prefixLift 595400
  have htrace : WordTrace (prefixWord ++ tailWord_595400) baseStart_595400 baseEnd_595400 := by
    simpa [prefixWord, tailWord_595400, baseEnd_595400] using wordTrace_append hprefix tailTrace_595400
  have hstable : (prefixWord ++ tailWord_595400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595400).length < 2 ^ (prefixWord ++ tailWord_595400).sum := by decide
  have hdescent : baseEnd_595400 < baseStart_595400 := by decide
  rcases family_descends (prefixWord ++ tailWord_595400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595414 : List Nat := [5, 2, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_595414 : Nat := 118140960795 + 595414 * 2 ^ 59
def prefixEnd_595414 : Nat := 4983230072969 + 3 ^ 40 * 595414 * 2
def baseEnd_595414 : Nat := 101911190138746224562249

theorem tailTrace_595414 : CollatzResearch.WordTrace tailWord_595414 prefixEnd_595414 101911190138746224562249 := by
  unfold tailWord_595414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1357283291557765091279081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14477688443282827640310197 1357283291557765091279081)
  ·
    refine ⟨1017962468668323818459311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1357283291557765091279081 1017962468668323818459311)
    ·
      refine ⟨1526943703002485727688967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1017962468668323818459311 1526943703002485727688967)
      ·
        refine ⟨2290415554503728591533451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1526943703002485727688967 2290415554503728591533451)
        ·
          refine ⟨3435623331755592887300177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2290415554503728591533451 3435623331755592887300177)
          ·
            refine ⟨2576717498816694665475133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3435623331755592887300177 2576717498816694665475133)
            ·
              refine ⟨966269062056260499553175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2576717498816694665475133 966269062056260499553175)
              ·
                refine ⟨1449403593084390749329763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 966269062056260499553175 1449403593084390749329763)
                ·
                  refine ⟨2174105389626586123994645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1449403593084390749329763 2174105389626586123994645)
                  ·
                    refine ⟨101911190138746224562249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2174105389626586123994645 101911190138746224562249)
                    ·
                      rfl

theorem cell23_595414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_595414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595414 prefixEnd_595414 := by exact prefixLift 595414
  have htrace : WordTrace (prefixWord ++ tailWord_595414) baseStart_595414 baseEnd_595414 := by
    simpa [prefixWord, tailWord_595414, baseEnd_595414] using wordTrace_append hprefix tailTrace_595414
  have hstable : (prefixWord ++ tailWord_595414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595414).length < 2 ^ (prefixWord ++ tailWord_595414).sum := by decide
  have hdescent : baseEnd_595414 < baseStart_595414 := by decide
  rcases family_descends (prefixWord ++ tailWord_595414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595417 : List Nat := [1, 2, 1, 2, 4, 2, 3, 1, 1, 2, 4]
def baseStart_595417 : Nat := 118140960795 + 595417 * 2 ^ 59
def prefixEnd_595417 : Nat := 4983230072969 + 3 ^ 40 * 595417 * 2
def baseEnd_595417 : Nat := 305735110858202161949233

theorem tailTrace_595417 : CollatzResearch.WordTrace tailWord_595417 prefixEnd_595417 305735110858202161949233 := by
  unfold tailWord_595417
  simp only [CollatzResearch.WordTrace]
  refine ⟨21716642083913372972824505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14477761389275581981883003 21716642083913372972824505)
  ·
    refine ⟨16287481562935029729618379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21716642083913372972824505 16287481562935029729618379)
    ·
      refine ⟨24431222344402544594427569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16287481562935029729618379 24431222344402544594427569)
      ·
        refine ⟨18323416758301908445820677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24431222344402544594427569 18323416758301908445820677)
        ·
          refine ⟨3435640642181607833591377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18323416758301908445820677 3435640642181607833591377)
          ·
            refine ⟨2576730481636205875193533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3435640642181607833591377 2576730481636205875193533)
            ·
              refine ⟨966273930613577203197575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2576730481636205875193533 966273930613577203197575)
              ·
                refine ⟨1449410895920365804796363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 966273930613577203197575 1449410895920365804796363)
                ·
                  refine ⟨2174116343880548707194545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1449410895920365804796363 2174116343880548707194545)
                  ·
                    refine ⟨1630587257910411530395909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2174116343880548707194545 1630587257910411530395909)
                    ·
                      refine ⟨305735110858202161949233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1630587257910411530395909 305735110858202161949233)
                      ·
                        rfl

theorem cell23_595417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 2, 4].length) (baseStart_595417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595417 prefixEnd_595417 := by exact prefixLift 595417
  have htrace : WordTrace (prefixWord ++ tailWord_595417) baseStart_595417 baseEnd_595417 := by
    simpa [prefixWord, tailWord_595417, baseEnd_595417] using wordTrace_append hprefix tailTrace_595417
  have hstable : (prefixWord ++ tailWord_595417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595417).length < 2 ^ (prefixWord ++ tailWord_595417).sum := by decide
  have hdescent : baseEnd_595417 < baseStart_595417 := by decide
  rcases family_descends (prefixWord ++ tailWord_595417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595421 : List Nat := [1, 4, 3, 1, 1, 2, 2, 2, 3, 2, 2]
def baseStart_595421 : Nat := 118140960795 + 595421 * 2 ^ 59
def prefixEnd_595421 : Nat := 4983230072969 + 3 ^ 40 * 595421 * 2
def baseEnd_595421 : Nat := 305737164780820146299215

theorem tailTrace_595421 : CollatzResearch.WordTrace tailWord_595421 prefixEnd_595421 305737164780820146299215 := by
  unfold tailWord_595421
  simp only [CollatzResearch.WordTrace]
  refine ⟨21716787975898881655970117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14477858650599254437313411 21716787975898881655970117)
  ·
    refine ⟨4071897745481040310494397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21716787975898881655970117 4071897745481040310494397)
    ·
      refine ⟨1526961654555390116435399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4071897745481040310494397 1526961654555390116435399)
      ·
        refine ⟨2290442481833085174653099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1526961654555390116435399 2290442481833085174653099)
        ·
          refine ⟨3435663722749627761979649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2290442481833085174653099 3435663722749627761979649)
          ·
            refine ⟨2576747792062220821484737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3435663722749627761979649 2576747792062220821484737)
            ·
              refine ⟨1932560844046665616113553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2576747792062220821484737 1932560844046665616113553)
              ·
                refine ⟨1449420633034999212085165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1932560844046665616113553 1449420633034999212085165)
                ·
                  refine ⟨543532737388124704531937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1449420633034999212085165 543532737388124704531937)
                  ·
                    refine ⟨407649553041093528398953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 543532737388124704531937 407649553041093528398953)
                    ·
                      refine ⟨305737164780820146299215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 407649553041093528398953 305737164780820146299215)
                      ·
                        rfl

theorem cell23_595421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_595421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595421 prefixEnd_595421 := by exact prefixLift 595421
  have htrace : WordTrace (prefixWord ++ tailWord_595421) baseStart_595421 baseEnd_595421 := by
    simpa [prefixWord, tailWord_595421, baseEnd_595421] using wordTrace_append hprefix tailTrace_595421
  have hstable : (prefixWord ++ tailWord_595421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595421).length < 2 ^ (prefixWord ++ tailWord_595421).sum := by decide
  have hdescent : baseEnd_595421 < baseStart_595421 := by decide
  rcases family_descends (prefixWord ++ tailWord_595421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595427 : List Nat := [1, 1, 1, 6, 2, 1, 4, 7]
def baseStart_595427 : Nat := 118140960795 + 595427 * 2 ^ 59
def prefixEnd_595427 : Nat := 4983230072969 + 3 ^ 40 * 595427 * 2
def baseEnd_595427 : Nat := 11323712802398041586081

theorem tailTrace_595427 : CollatzResearch.WordTrace tailWord_595427 prefixEnd_595427 11323712802398041586081 := by
  unfold tailWord_595427
  simp only [CollatzResearch.WordTrace]
  refine ⟨21717006813877144680688535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14478004542584763120459023 21717006813877144680688535)
  ·
    refine ⟨32575510220815717021032803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21717006813877144680688535 32575510220815717021032803)
    ·
      refine ⟨48863265331223575531549205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32575510220815717021032803 48863265331223575531549205)
      ·
        refine ⟨2290465562401105103041369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 48863265331223575531549205 2290465562401105103041369)
        ·
          refine ⟨1717849171800828827281027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2290465562401105103041369 1717849171800828827281027)
          ·
            refine ⟨2576773757701243240921541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1717849171800828827281027 2576773757701243240921541)
            ·
              refine ⟨483145079568983107672789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2576773757701243240921541 483145079568983107672789)
              ·
                refine ⟨11323712802398041586081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 483145079568983107672789 11323712802398041586081)
                ·
                  rfl

theorem cell23_595427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 7].length) (baseStart_595427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595427 prefixEnd_595427 := by exact prefixLift 595427
  have htrace : WordTrace (prefixWord ++ tailWord_595427) baseStart_595427 baseEnd_595427 := by
    simpa [prefixWord, tailWord_595427, baseEnd_595427] using wordTrace_append hprefix tailTrace_595427
  have hstable : (prefixWord ++ tailWord_595427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595427).length < 2 ^ (prefixWord ++ tailWord_595427).sum := by decide
  have hdescent : baseEnd_595427 < baseStart_595427 := by decide
  rcases family_descends (prefixWord ++ tailWord_595427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595450 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5]
def baseStart_595450 : Nat := 118140960795 + 595450 * 2 ^ 59
def prefixEnd_595450 : Nat := 4983230072969 + 3 ^ 40 * 595450 * 2
def baseEnd_595450 : Nat := 305752055719800532836581

theorem tailTrace_595450 : CollatzResearch.WordTrace tailWord_595450 prefixEnd_595450 305752055719800532836581 := by
  unfold tailWord_595450
  simp only [CollatzResearch.WordTrace]
  refine ⟨5429461423198454902193951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14478563795195879739183869 5429461423198454902193951)
  ·
    refine ⟨8144192134797682353290927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5429461423198454902193951 8144192134797682353290927)
    ·
      refine ⟨12216288202196523529936391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8144192134797682353290927 12216288202196523529936391)
      ·
        refine ⟨18324432303294785294904587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12216288202196523529936391 18324432303294785294904587)
        ·
          refine ⟨27486648454942177942356881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18324432303294785294904587 27486648454942177942356881)
          ·
            refine ⟨20614986341206633456767661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27486648454942177942356881 20614986341206633456767661)
            ·
              refine ⟨7730619877952487546287873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20614986341206633456767661 7730619877952487546287873)
              ·
                refine ⟨5797964908464365659715905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7730619877952487546287873 5797964908464365659715905)
                ·
                  refine ⟨4348473681348274244786929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5797964908464365659715905 4348473681348274244786929)
                  ·
                    refine ⟨3261355261011205683590197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4348473681348274244786929 3261355261011205683590197)
                    ·
                      refine ⟨305752055719800532836581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3261355261011205683590197 305752055719800532836581)
                      ·
                        rfl

theorem cell23_595450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_595450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595450 prefixEnd_595450 := by exact prefixLift 595450
  have htrace : WordTrace (prefixWord ++ tailWord_595450) baseStart_595450 baseEnd_595450 := by
    simpa [prefixWord, tailWord_595450, baseEnd_595450] using wordTrace_append hprefix tailTrace_595450
  have hstable : (prefixWord ++ tailWord_595450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595450).length < 2 ^ (prefixWord ++ tailWord_595450).sum := by decide
  have hdescent : baseEnd_595450 < baseStart_595450 := by decide
  rcases family_descends (prefixWord ++ tailWord_595450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595498 : List Nat := [3, 1, 4, 1, 1, 1, 5, 1, 1, 3, 2]
def baseStart_595498 : Nat := 118140960795 + 595498 * 2 ^ 59
def prefixEnd_595498 : Nat := 4983230072969 + 3 ^ 40 * 595498 * 2
def baseEnd_595498 : Nat := 305776702791216345036361

theorem tailTrace_595498 : CollatzResearch.WordTrace tailWord_595498 prefixEnd_595498 305776702791216345036361 := by
  unfold tailWord_595498
  simp only [CollatzResearch.WordTrace]
  refine ⟨5429899099154980951630787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14479730931079949204348765 5429899099154980951630787)
  ·
    refine ⟨8144848648732471427446181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5429899099154980951630787 8144848648732471427446181)
    ·
      refine ⟨1527159121637338392646159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8144848648732471427446181 1527159121637338392646159)
      ·
        refine ⟨2290738682456007588969239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1527159121637338392646159 2290738682456007588969239)
        ·
          refine ⟨3436108023684011383453859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2290738682456007588969239 3436108023684011383453859)
          ·
            refine ⟨5154162035526017075180789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3436108023684011383453859 5154162035526017075180789)
            ·
              refine ⟨483202690830564100798199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5154162035526017075180789 483202690830564100798199)
              ·
                refine ⟨724804036245846151197299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483202690830564100798199 724804036245846151197299)
                ·
                  refine ⟨1087206054368769226795949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 724804036245846151197299 1087206054368769226795949)
                  ·
                    refine ⟨407702270388288460048481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1087206054368769226795949 407702270388288460048481)
                    ·
                      refine ⟨305776702791216345036361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 407702270388288460048481 305776702791216345036361)
                      ·
                        rfl

theorem cell23_595498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_595498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595498 prefixEnd_595498 := by exact prefixLift 595498
  have htrace : WordTrace (prefixWord ++ tailWord_595498) baseStart_595498 baseEnd_595498 := by
    simpa [prefixWord, tailWord_595498, baseEnd_595498] using wordTrace_append hprefix tailTrace_595498
  have hstable : (prefixWord ++ tailWord_595498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595498).length < 2 ^ (prefixWord ++ tailWord_595498).sum := by decide
  have hdescent : baseEnd_595498 < baseStart_595498 := by decide
  rcases family_descends (prefixWord ++ tailWord_595498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595511 : List Nat := [1, 1, 3, 1, 2, 4, 1, 4, 2, 2, 2]
def baseStart_595511 : Nat := 118140960795 + 595511 * 2 ^ 59
def prefixEnd_595511 : Nat := 4983230072969 + 3 ^ 40 * 595511 * 2
def baseEnd_595511 : Nat := 305783378039724794173801

theorem tailTrace_595511 : CollatzResearch.WordTrace tailWord_595511 prefixEnd_595511 305783378039724794173801 := by
  unfold tailWord_595511
  simp only [CollatzResearch.WordTrace]
  refine ⟨21720070545572827026746387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14480047030381884684497591 21720070545572827026746387)
  ·
    refine ⟨32580105818359240540119581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21720070545572827026746387 32580105818359240540119581)
    ·
      refine ⟨12217539681884715202544843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32580105818359240540119581 12217539681884715202544843)
      ·
        refine ⟨18326309522827072803817265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12217539681884715202544843 18326309522827072803817265)
        ·
          refine ⟨13744732142120304602862949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18326309522827072803817265 13744732142120304602862949)
          ·
            refine ⟨2577137276647557113036803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13744732142120304602862949 2577137276647557113036803)
            ·
              refine ⟨3865705914971335669555205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2577137276647557113036803 3865705914971335669555205)
              ·
                refine ⟨724819859057125438041601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3865705914971335669555205 724819859057125438041601)
                ·
                  refine ⟨543614894292844078531201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 724819859057125438041601 543614894292844078531201)
                  ·
                    refine ⟨407711170719633058898401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 543614894292844078531201 407711170719633058898401)
                    ·
                      refine ⟨305783378039724794173801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 407711170719633058898401 305783378039724794173801)
                      ·
                        rfl

theorem cell23_595511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 2, 2].length) (baseStart_595511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595511 prefixEnd_595511 := by exact prefixLift 595511
  have htrace : WordTrace (prefixWord ++ tailWord_595511) baseStart_595511 baseEnd_595511 := by
    simpa [prefixWord, tailWord_595511, baseEnd_595511] using wordTrace_append hprefix tailTrace_595511
  have hstable : (prefixWord ++ tailWord_595511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595511).length < 2 ^ (prefixWord ++ tailWord_595511).sum := by decide
  have hdescent : baseEnd_595511 < baseStart_595511 := by decide
  rcases family_descends (prefixWord ++ tailWord_595511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595520 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 8]
def baseStart_595520 : Nat := 118140960795 + 595520 * 2 ^ 59
def prefixEnd_595520 : Nat := 4983230072969 + 3 ^ 40 * 595520 * 2
def baseEnd_595520 : Nat := 305787999365615258961259

theorem tailTrace_595520 : CollatzResearch.WordTrace tailWord_595520 prefixEnd_595520 305787999365615258961259 := by
  unfold tailWord_595520
  simp only [CollatzResearch.WordTrace]
  refine ⟨10860199401270110781912007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14480265868360147709216009 10860199401270110781912007)
  ·
    refine ⟨16290299101905166172868011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10860199401270110781912007 16290299101905166172868011)
    ·
      refine ⟨24435448652857749259302017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16290299101905166172868011 24435448652857749259302017)
      ·
        refine ⟨18326586489643311944476513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24435448652857749259302017 18326586489643311944476513)
        ·
          refine ⟨13744939867232483958357385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18326586489643311944476513 13744939867232483958357385)
          ·
            refine ⟨10308704900424362968768039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13744939867232483958357385 10308704900424362968768039)
            ·
              refine ⟨15463057350636544453152059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10308704900424362968768039 15463057350636544453152059)
              ·
                refine ⟨23194586025954816679728089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15463057350636544453152059 23194586025954816679728089)
                ·
                  refine ⟨17395939519466112509796067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23194586025954816679728089 17395939519466112509796067)
                  ·
                    refine ⟨26093909279199168764694101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17395939519466112509796067 26093909279199168764694101)
                    ·
                      refine ⟨305787999365615258961259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 26093909279199168764694101 305787999365615258961259)
                      ·
                        rfl

theorem cell23_595520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_595520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595520 prefixEnd_595520 := by exact prefixLift 595520
  have htrace : WordTrace (prefixWord ++ tailWord_595520) baseStart_595520 baseEnd_595520 := by
    simpa [prefixWord, tailWord_595520, baseEnd_595520] using wordTrace_append hprefix tailTrace_595520
  have hstable : (prefixWord ++ tailWord_595520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595520).length < 2 ^ (prefixWord ++ tailWord_595520).sum := by decide
  have hdescent : baseEnd_595520 < baseStart_595520 := by decide
  rcases family_descends (prefixWord ++ tailWord_595520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595549 : List Nat := [1, 4, 4, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_595549 : Nat := 118140960795 + 595549 * 2 ^ 59
def prefixEnd_595549 : Nat := 4983230072969 + 3 ^ 40 * 595549 * 2
def baseEnd_595549 : Nat := 305802890304595645498627

theorem tailTrace_595549 : CollatzResearch.WordTrace tailWord_595549 prefixEnd_595549 305802890304595645498627 := by
  unfold tailWord_595549
  simp only [CollatzResearch.WordTrace]
  refine ⟨21721456519435159516629701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14480971012956773011086467 21721456519435159516629701)
  ·
    refine ⟨4072773097394092409368069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21721456519435159516629701 4072773097394092409368069)
    ·
      refine ⟨763644955761392326756513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4072773097394092409368069 763644955761392326756513)
      ·
        refine ⟨572733716821044245067385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 763644955761392326756513 572733716821044245067385)
        ·
          refine ⟨429550287615783183800539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 572733716821044245067385 429550287615783183800539)
          ·
            refine ⟨644325431423674775700809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429550287615783183800539 644325431423674775700809)
            ·
              refine ⟨483244073567756081775607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 644325431423674775700809 483244073567756081775607)
              ·
                refine ⟨724866110351634122663411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483244073567756081775607 724866110351634122663411)
                ·
                  refine ⟨1087299165527451183995117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 724866110351634122663411 1087299165527451183995117)
                  ·
                    refine ⟨407737187072794193998169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1087299165527451183995117 407737187072794193998169)
                    ·
                      refine ⟨305802890304595645498627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 407737187072794193998169 305802890304595645498627)
                      ·
                        rfl

theorem cell23_595549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_595549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595549 prefixEnd_595549 := by exact prefixLift 595549
  have htrace : WordTrace (prefixWord ++ tailWord_595549) baseStart_595549 baseEnd_595549 := by
    simpa [prefixWord, tailWord_595549, baseEnd_595549] using wordTrace_append hprefix tailTrace_595549
  have hstable : (prefixWord ++ tailWord_595549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595549).length < 2 ^ (prefixWord ++ tailWord_595549).sum := by decide
  have hdescent : baseEnd_595549 < baseStart_595549 := by decide
  rcases family_descends (prefixWord ++ tailWord_595549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595567 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 4]
def baseStart_595567 : Nat := 118140960795 + 595567 * 2 ^ 59
def prefixEnd_595567 : Nat := 4983230072969 + 3 ^ 40 * 595567 * 2
def baseEnd_595567 : Nat := 305812132956376575073543

theorem tailTrace_595567 : CollatzResearch.WordTrace tailWord_595567 prefixEnd_595567 305812132956376575073543 := by
  unfold tailWord_595567
  simp only [CollatzResearch.WordTrace]
  refine ⟨21722113033369948590784955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14481408688913299060523303 21722113033369948590784955)
  ·
    refine ⟨32583169550054922886177433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21722113033369948590784955 32583169550054922886177433)
    ·
      refine ⟨24437377162541192164633075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32583169550054922886177433 24437377162541192164633075)
      ·
        refine ⟨36656065743811788246949613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24437377162541192164633075 36656065743811788246949613)
        ·
          refine ⟨13746024653929420592606105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36656065743811788246949613 13746024653929420592606105)
          ·
            refine ⟨10309518490447065444454579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13746024653929420592606105 10309518490447065444454579)
            ·
              refine ⟨15464277735670598166681869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10309518490447065444454579 15464277735670598166681869)
              ·
                refine ⟨5799104150876474312505701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15464277735670598166681869 5799104150876474312505701)
                ·
                  refine ⟨1087332028289338933594819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5799104150876474312505701 1087332028289338933594819)
                  ·
                    refine ⟨1630998042434008400392229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1087332028289338933594819 1630998042434008400392229)
                    ·
                      refine ⟨305812132956376575073543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1630998042434008400392229 305812132956376575073543)
                      ·
                        rfl

theorem cell23_595567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 4].length) (baseStart_595567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595567 prefixEnd_595567 := by exact prefixLift 595567
  have htrace : WordTrace (prefixWord ++ tailWord_595567) baseStart_595567 baseEnd_595567 := by
    simpa [prefixWord, tailWord_595567, baseEnd_595567] using wordTrace_append hprefix tailTrace_595567
  have hstable : (prefixWord ++ tailWord_595567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595567).length < 2 ^ (prefixWord ++ tailWord_595567).sum := by decide
  have hdescent : baseEnd_595567 < baseStart_595567 := by decide
  rcases family_descends (prefixWord ++ tailWord_595567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595584 : List Nat := [2, 1, 1, 2, 1, 4, 1, 3, 2, 4, 2]
def baseStart_595584 : Nat := 118140960795 + 595584 * 2 ^ 59
def prefixEnd_595584 : Nat := 4983230072969 + 3 ^ 40 * 595584 * 2
def baseEnd_595584 : Nat := 305820862127503008560965

theorem tailTrace_595584 : CollatzResearch.WordTrace tailWord_595584 prefixEnd_595584 305820862127503008560965 := by
  unfold tailWord_595584
  simp only [CollatzResearch.WordTrace]
  refine ⟨10861366537154180247076903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14481822049538906996102537 10861366537154180247076903)
  ·
    refine ⟨16292049805731270370615355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10861366537154180247076903 16292049805731270370615355)
    ·
      refine ⟨24438074708596905555923033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16292049805731270370615355 24438074708596905555923033)
      ·
        refine ⟨18328556031447679166942275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24438074708596905555923033 18328556031447679166942275)
        ·
          refine ⟨27492834047171518750413413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18328556031447679166942275 27492834047171518750413413)
          ·
            refine ⟨5154906383844659765702515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27492834047171518750413413 5154906383844659765702515)
            ·
              refine ⟨7732359575766989648553773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5154906383844659765702515 7732359575766989648553773)
              ·
                refine ⟨2899634840912621118207665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7732359575766989648553773 2899634840912621118207665)
                ·
                  refine ⟨2174726130684465838655749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2899634840912621118207665 2174726130684465838655749)
                  ·
                    refine ⟨407761149503337344747953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2174726130684465838655749 407761149503337344747953)
                    ·
                      refine ⟨305820862127503008560965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 407761149503337344747953 305820862127503008560965)
                      ·
                        rfl

theorem cell23_595584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 2, 4, 2].length) (baseStart_595584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595584 prefixEnd_595584 := by exact prefixLift 595584
  have htrace : WordTrace (prefixWord ++ tailWord_595584) baseStart_595584 baseEnd_595584 := by
    simpa [prefixWord, tailWord_595584, baseEnd_595584] using wordTrace_append hprefix tailTrace_595584
  have hstable : (prefixWord ++ tailWord_595584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595584).length < 2 ^ (prefixWord ++ tailWord_595584).sum := by decide
  have hdescent : baseEnd_595584 < baseStart_595584 := by decide
  rcases family_descends (prefixWord ++ tailWord_595584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595607 : List Nat := [1, 1, 3, 3, 2, 2, 1, 2, 8]
def baseStart_595607 : Nat := 118140960795 + 595607 * 2 ^ 59
def prefixEnd_595607 : Nat := 4983230072969 + 3 ^ 40 * 595607 * 2
def baseEnd_595607 : Nat := 33981408020284046508151

theorem tailTrace_595607 : CollatzResearch.WordTrace tailWord_595607 prefixEnd_595607 33981408020284046508151 := by
  unfold tailWord_595607
  simp only [CollatzResearch.WordTrace]
  refine ⟨21723571953225035422241075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14482381302150023614827383 21723571953225035422241075)
  ·
    refine ⟨32585357929837553133361613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21723571953225035422241075 32585357929837553133361613)
    ·
      refine ⟨12219509223689082425010605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32585357929837553133361613 12219509223689082425010605)
      ·
        refine ⟨4582315958883405909378977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12219509223689082425010605 4582315958883405909378977)
        ·
          refine ⟨3436736969162554432034233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4582315958883405909378977 3436736969162554432034233)
          ·
            refine ⟨2577552726871915824025675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3436736969162554432034233 2577552726871915824025675)
            ·
              refine ⟨3866329090307873736038513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2577552726871915824025675 3866329090307873736038513)
              ·
                refine ⟨2899746817730905302028885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3866329090307873736038513 2899746817730905302028885)
                ·
                  refine ⟨33981408020284046508151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2899746817730905302028885 33981408020284046508151)
                  ·
                    rfl

theorem cell23_595607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 8].length) (baseStart_595607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595607 prefixEnd_595607 := by exact prefixLift 595607
  have htrace : WordTrace (prefixWord ++ tailWord_595607) baseStart_595607 baseEnd_595607 := by
    simpa [prefixWord, tailWord_595607, baseEnd_595607] using wordTrace_append hprefix tailTrace_595607
  have hstable : (prefixWord ++ tailWord_595607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595607).length < 2 ^ (prefixWord ++ tailWord_595607).sum := by decide
  have hdescent : baseEnd_595607 < baseStart_595607 := by decide
  rcases family_descends (prefixWord ++ tailWord_595607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595618 : List Nat := [3, 3, 1, 4, 1, 1, 1, 2, 2, 1, 4]
def baseStart_595618 : Nat := 118140960795 + 595618 * 2 ^ 59
def prefixEnd_595618 : Nat := 4983230072969 + 3 ^ 40 * 595618 * 2
def baseEnd_595618 : Nat := 305838320469755875535809

theorem tailTrace_595618 : CollatzResearch.WordTrace tailWord_595618 prefixEnd_595618 305838320469755875535809 := by
  unfold tailWord_595618
  simp only [CollatzResearch.WordTrace]
  refine ⟨5430993289046296075222877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14482648770790122867261005 5430993289046296075222877)
  ·
    refine ⟨2036622483392361028208579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5430993289046296075222877 2036622483392361028208579)
    ·
      refine ⟨3054933725088541542312869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2036622483392361028208579 3054933725088541542312869)
      ·
        refine ⟨572800073454101539183663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3054933725088541542312869 572800073454101539183663)
        ·
          refine ⟨859200110181152308775495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572800073454101539183663 859200110181152308775495)
          ·
            refine ⟨1288800165271728463163243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 859200110181152308775495 1288800165271728463163243)
            ·
              refine ⟨1933200247907592694744865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1288800165271728463163243 1933200247907592694744865)
              ·
                refine ⟨1449900185930694521058649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1933200247907592694744865 1449900185930694521058649)
                ·
                  refine ⟨1087425139448020890793987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1449900185930694521058649 1087425139448020890793987)
                  ·
                    refine ⟨1631137709172031336190981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1087425139448020890793987 1631137709172031336190981)
                    ·
                      refine ⟨305838320469755875535809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1631137709172031336190981 305838320469755875535809)
                      ·
                        rfl

theorem cell23_595618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_595618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595618 prefixEnd_595618 := by exact prefixLift 595618
  have htrace : WordTrace (prefixWord ++ tailWord_595618) baseStart_595618 baseEnd_595618 := by
    simpa [prefixWord, tailWord_595618, baseEnd_595618] using wordTrace_append hprefix tailTrace_595618
  have hstable : (prefixWord ++ tailWord_595618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595618).length < 2 ^ (prefixWord ++ tailWord_595618).sum := by decide
  have hdescent : baseEnd_595618 < baseStart_595618 := by decide
  rcases family_descends (prefixWord ++ tailWord_595618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595671 : List Nat := [1, 1, 3, 2, 1, 3, 5, 1, 1, 5]
def baseStart_595671 : Nat := 118140960795 + 595671 * 2 ^ 59
def prefixEnd_595671 : Nat := 4983230072969 + 3 ^ 40 * 595671 * 2
def baseEnd_595671 : Nat := 101955178314814722724355

theorem tailTrace_595671 : CollatzResearch.WordTrace tailWord_595671 prefixEnd_595671 101955178314814722724355 := by
  unfold tailWord_595671
  simp only [CollatzResearch.WordTrace]
  refine ⟨21725906224993174352570867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14483937483328782901713911 21725906224993174352570867)
  ·
    refine ⟨32588859337489761528856301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21725906224993174352570867 32588859337489761528856301)
    ·
      refine ⟨12220822251558660573321113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32588859337489761528856301 12220822251558660573321113)
      ·
        refine ⟨9165616688668995429990835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12220822251558660573321113 9165616688668995429990835)
        ·
          refine ⟨13748425033003493144986253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9165616688668995429990835 13748425033003493144986253)
          ·
            refine ⟨5155659387376309929369845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13748425033003493144986253 5155659387376309929369845)
            ·
              refine ⟨483343067566529055878423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5155659387376309929369845 483343067566529055878423)
              ·
                refine ⟨725014601349793583817635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483343067566529055878423 725014601349793583817635)
                ·
                  refine ⟨1087521902024690375726453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 725014601349793583817635 1087521902024690375726453)
                  ·
                    refine ⟨101955178314814722724355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1087521902024690375726453 101955178314814722724355)
                    ·
                      rfl

theorem cell23_595671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 1, 5].length) (baseStart_595671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595671 prefixEnd_595671 := by exact prefixLift 595671
  have htrace : WordTrace (prefixWord ++ tailWord_595671) baseStart_595671 baseEnd_595671 := by
    simpa [prefixWord, tailWord_595671, baseEnd_595671] using wordTrace_append hprefix tailTrace_595671
  have hstable : (prefixWord ++ tailWord_595671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595671).length < 2 ^ (prefixWord ++ tailWord_595671).sum := by decide
  have hdescent : baseEnd_595671 < baseStart_595671 := by decide
  rcases family_descends (prefixWord ++ tailWord_595671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595694 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_595694 : Nat := 118140960795 + 595694 * 2 ^ 59
def prefixEnd_595694 : Nat := 4983230072969 + 3 ^ 40 * 595694 * 2
def baseEnd_595694 : Nat := 305877344999497578185459

theorem tailTrace_595694 : CollatzResearch.WordTrace tailWord_595694 prefixEnd_595694 305877344999497578185459 := by
  unfold tailWord_595694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2715843137988731160082267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14484496735939899520438757 2715843137988731160082267)
  ·
    refine ⟨4073764706983096740123401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2715843137988731160082267 4073764706983096740123401)
    ·
      refine ⟨3055323530237322555092551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4073764706983096740123401 3055323530237322555092551)
      ·
        refine ⟨4582985295355983832638827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3055323530237322555092551 4582985295355983832638827)
        ·
          refine ⟨6874477943033975748958241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4582985295355983832638827 6874477943033975748958241)
          ·
            refine ⟨5155858457275481811718681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6874477943033975748958241 5155858457275481811718681)
            ·
              refine ⟨3866893842956611358789011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5155858457275481811718681 3866893842956611358789011)
              ·
                refine ⟨5800340764434917038183517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3866893842956611358789011 5800340764434917038183517)
                ·
                  refine ⟨2175127786663093889318819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5800340764434917038183517 2175127786663093889318819)
                  ·
                    refine ⟨3262691679994640833978229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2175127786663093889318819 3262691679994640833978229)
                    ·
                      refine ⟨305877344999497578185459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3262691679994640833978229 305877344999497578185459)
                      ·
                        rfl

theorem cell23_595694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_595694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595694 prefixEnd_595694 := by exact prefixLift 595694
  have htrace : WordTrace (prefixWord ++ tailWord_595694) baseStart_595694 baseEnd_595694 := by
    simpa [prefixWord, tailWord_595694, baseEnd_595694] using wordTrace_append hprefix tailTrace_595694
  have hstable : (prefixWord ++ tailWord_595694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595694).length < 2 ^ (prefixWord ++ tailWord_595694).sum := by decide
  have hdescent : baseEnd_595694 < baseStart_595694 := by decide
  rcases family_descends (prefixWord ++ tailWord_595694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595708 : List Nat := [2, 2, 2, 1, 3, 1, 3, 2, 3, 2, 2]
def baseStart_595708 : Nat := 118140960795 + 595708 * 2 ^ 59
def prefixEnd_595708 : Nat := 4983230072969 + 3 ^ 40 * 595708 * 2
def baseEnd_595708 : Nat := 305884533728660523410395

theorem tailTrace_595708 : CollatzResearch.WordTrace tailWord_595708 prefixEnd_595708 305884533728660523410395 := by
  unfold tailWord_595708
  simp only [CollatzResearch.WordTrace]
  refine ⟨10863627862929564835833889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14484837150572753114445185 10863627862929564835833889)
  ·
    refine ⟨8147720897197173626875417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10863627862929564835833889 8147720897197173626875417)
    ·
      refine ⟨6110790672897880220156563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8147720897197173626875417 6110790672897880220156563)
      ·
        refine ⟨9166186009346820330234845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6110790672897880220156563 9166186009346820330234845)
        ·
          refine ⟨3437319753505057623838067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9166186009346820330234845 3437319753505057623838067)
          ·
            refine ⟨5155979630257586435757101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3437319753505057623838067 5155979630257586435757101)
            ·
              refine ⟨1933492361346594913408913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5155979630257586435757101 1933492361346594913408913)
              ·
                refine ⟨1450119271009946185056685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1933492361346594913408913 1450119271009946185056685)
                ·
                  refine ⟨543794726628729819396257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1450119271009946185056685 543794726628729819396257)
                  ·
                    refine ⟨407846044971547364547193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 543794726628729819396257 407846044971547364547193)
                    ·
                      refine ⟨305884533728660523410395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 407846044971547364547193 305884533728660523410395)
                      ·
                        rfl

theorem cell23_595708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 3, 2, 2].length) (baseStart_595708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595708 prefixEnd_595708 := by exact prefixLift 595708
  have htrace : WordTrace (prefixWord ++ tailWord_595708) baseStart_595708 baseEnd_595708 := by
    simpa [prefixWord, tailWord_595708, baseEnd_595708] using wordTrace_append hprefix tailTrace_595708
  have hstable : (prefixWord ++ tailWord_595708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595708).length < 2 ^ (prefixWord ++ tailWord_595708).sum := by decide
  have hdescent : baseEnd_595708 < baseStart_595708 := by decide
  rcases family_descends (prefixWord ++ tailWord_595708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595727 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 1, 9]
def baseStart_595727 : Nat := 118140960795 + 595727 * 2 ^ 59
def prefixEnd_595727 : Nat := 4983230072969 + 3 ^ 40 * 595727 * 2
def baseEnd_595727 : Nat := 101964763287031983024269

theorem tailTrace_595727 : CollatzResearch.WordTrace tailWord_595727 prefixEnd_595727 101964763287031983024269 := by
  unfold tailWord_595727
  simp only [CollatzResearch.WordTrace]
  refine ⟨21727948712790295916609435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14485299141860197277739623 21727948712790295916609435)
  ·
    refine ⟨32591923069185443874914153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21727948712790295916609435 32591923069185443874914153)
    ·
      refine ⟨24443942301889082906185615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32591923069185443874914153 24443942301889082906185615)
      ·
        refine ⟨36665913452833624359278423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24443942301889082906185615 36665913452833624359278423)
        ·
          refine ⟨54998870179250436538917635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36665913452833624359278423 54998870179250436538917635)
          ·
            refine ⟨82498305268875654808376453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54998870179250436538917635 82498305268875654808376453)
            ·
              refine ⟨15468432237914185276570585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82498305268875654808376453 15468432237914185276570585)
              ·
                refine ⟨11601324178435638957427939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15468432237914185276570585 11601324178435638957427939)
                ·
                  refine ⟨17401986267653458436141909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11601324178435638957427939 17401986267653458436141909)
                  ·
                    refine ⟨101964763287031983024269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 17401986267653458436141909 101964763287031983024269)
                    ·
                      rfl

theorem cell23_595727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 9].length) (baseStart_595727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595727 prefixEnd_595727 := by exact prefixLift 595727
  have htrace : WordTrace (prefixWord ++ tailWord_595727) baseStart_595727 baseEnd_595727 := by
    simpa [prefixWord, tailWord_595727, baseEnd_595727] using wordTrace_append hprefix tailTrace_595727
  have hstable : (prefixWord ++ tailWord_595727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595727).length < 2 ^ (prefixWord ++ tailWord_595727).sum := by decide
  have hdescent : baseEnd_595727 < baseStart_595727 := by decide
  rcases family_descends (prefixWord ++ tailWord_595727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595768 : List Nat := [2, 1, 2, 1, 3, 3, 1, 4, 1, 3, 2]
def baseStart_595768 : Nat := 118140960795 + 595768 * 2 ^ 59
def prefixEnd_595768 : Nat := 4983230072969 + 3 ^ 40 * 595768 * 2
def baseEnd_595768 : Nat := 305915342567930288660119

theorem tailTrace_595768 : CollatzResearch.WordTrace tailWord_595768 prefixEnd_595768 305915342567930288660119 := by
  unfold tailWord_595768
  simp only [CollatzResearch.WordTrace]
  refine ⟨10864722052820879959425979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14486296070427839945901305 10864722052820879959425979)
  ·
    refine ⟨16297083079231319939138969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10864722052820879959425979 16297083079231319939138969)
    ·
      refine ⟨12222812309423489954354227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16297083079231319939138969 12222812309423489954354227)
      ·
        refine ⟨18334218464135234931531341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12222812309423489954354227 18334218464135234931531341)
        ·
          refine ⟨6875331924050713099324253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18334218464135234931531341 6875331924050713099324253)
          ·
            refine ⟨2578249471519017412246595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6875331924050713099324253 2578249471519017412246595)
            ·
              refine ⟨3867374207278526118369893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2578249471519017412246595 3867374207278526118369893)
              ·
                refine ⟨725132663864723647194355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3867374207278526118369893 725132663864723647194355)
                ·
                  refine ⟨1087698995797085470791533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 725132663864723647194355 1087698995797085470791533)
                  ·
                    refine ⟨407887123423907051546825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1087698995797085470791533 407887123423907051546825)
                    ·
                      refine ⟨305915342567930288660119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 407887123423907051546825 305915342567930288660119)
                      ·
                        rfl

theorem cell23_595768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 1, 3, 2].length) (baseStart_595768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595768 prefixEnd_595768 := by exact prefixLift 595768
  have htrace : WordTrace (prefixWord ++ tailWord_595768) baseStart_595768 baseEnd_595768 := by
    simpa [prefixWord, tailWord_595768, baseEnd_595768] using wordTrace_append hprefix tailTrace_595768
  have hstable : (prefixWord ++ tailWord_595768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595768).length < 2 ^ (prefixWord ++ tailWord_595768).sum := by decide
  have hdescent : baseEnd_595768 < baseStart_595768 := by decide
  rcases family_descends (prefixWord ++ tailWord_595768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595781 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 3, 4, 2]
def baseStart_595781 : Nat := 118140960795 + 595781 * 2 ^ 59
def prefixEnd_595781 : Nat := 4983230072969 + 3 ^ 40 * 595781 * 2
def baseEnd_595781 : Nat := 305922017816438737797559

theorem tailTrace_595781 : CollatzResearch.WordTrace tailWord_595781 prefixEnd_595781 305922017816438737797559 := by
  unfold tailWord_595781
  simp only [CollatzResearch.WordTrace]
  refine ⟨21729918254594663139075197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14486612169729775426050131 21729918254594663139075197)
  ·
    refine ⟨8148719345472998677153199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21729918254594663139075197 8148719345472998677153199)
    ·
      refine ⟨12223079018209498015729799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8148719345472998677153199 12223079018209498015729799)
      ·
        refine ⟨18334618527314247023594699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12223079018209498015729799 18334618527314247023594699)
        ·
          refine ⟨27501927790971370535392049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18334618527314247023594699 27501927790971370535392049)
          ·
            refine ⟨20626445843228527901544037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27501927790971370535392049 20626445843228527901544037)
            ·
              refine ⟨3867458595605348981539507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20626445843228527901544037 3867458595605348981539507)
              ·
                refine ⟨5801187893408023472309261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3867458595605348981539507 5801187893408023472309261)
                ·
                  refine ⟨2175445460028008802115973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5801187893408023472309261 2175445460028008802115973)
                  ·
                    refine ⟨407896023755251650396745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2175445460028008802115973 407896023755251650396745)
                    ·
                      refine ⟨305922017816438737797559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 407896023755251650396745 305922017816438737797559)
                      ·
                        rfl

theorem cell23_595781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 4, 2].length) (baseStart_595781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595781 prefixEnd_595781 := by exact prefixLift 595781
  have htrace : WordTrace (prefixWord ++ tailWord_595781) baseStart_595781 baseEnd_595781 := by
    simpa [prefixWord, tailWord_595781, baseEnd_595781] using wordTrace_append hprefix tailTrace_595781
  have hstable : (prefixWord ++ tailWord_595781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595781).length < 2 ^ (prefixWord ++ tailWord_595781).sum := by decide
  have hdescent : baseEnd_595781 < baseStart_595781 := by decide
  rcases family_descends (prefixWord ++ tailWord_595781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595784 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 1, 3, 5]
def baseStart_595784 : Nat := 118140960795 + 595784 * 2 ^ 59
def prefixEnd_595784 : Nat := 4983230072969 + 3 ^ 40 * 595784 * 2
def baseEnd_595784 : Nat := 305923558258402226060045

theorem tailTrace_595784 : CollatzResearch.WordTrace tailWord_595784 prefixEnd_595784 305923558258402226060045 := by
  unfold tailWord_595784
  simp only [CollatzResearch.WordTrace]
  refine ⟨10865013836791897325717203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14486685115722529767622937 10865013836791897325717203)
  ·
    refine ⟨16297520755187845988575805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10865013836791897325717203 16297520755187845988575805)
    ·
      refine ⟨6111570283195442245715927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16297520755187845988575805 6111570283195442245715927)
      ·
        refine ⟨9167355424793163368573891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6111570283195442245715927 9167355424793163368573891)
        ·
          refine ⟨13751033137189745052860837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9167355424793163368573891 13751033137189745052860837)
          ·
            refine ⟨2578318713223077197411407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13751033137189745052860837 2578318713223077197411407)
            ·
              refine ⟨3867478069834615796117111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2578318713223077197411407 3867478069834615796117111)
              ·
                refine ⟨5801217104751923694175667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3867478069834615796117111 5801217104751923694175667)
                ·
                  refine ⟨8701825657127885541263501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5801217104751923694175667 8701825657127885541263501)
                  ·
                    refine ⟨3263184621422957077973813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8701825657127885541263501 3263184621422957077973813)
                    ·
                      refine ⟨305923558258402226060045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3263184621422957077973813 305923558258402226060045)
                      ·
                        rfl

theorem cell23_595784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_595784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595784 prefixEnd_595784 := by exact prefixLift 595784
  have htrace : WordTrace (prefixWord ++ tailWord_595784) baseStart_595784 baseEnd_595784 := by
    simpa [prefixWord, tailWord_595784, baseEnd_595784] using wordTrace_append hprefix tailTrace_595784
  have hstable : (prefixWord ++ tailWord_595784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595784).length < 2 ^ (prefixWord ++ tailWord_595784).sum := by decide
  have hdescent : baseEnd_595784 < baseStart_595784 := by decide
  rcases family_descends (prefixWord ++ tailWord_595784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595815 : List Nat := [1, 1, 5, 1, 2, 1, 3, 3, 2, 2, 2]
def baseStart_595815 : Nat := 118140960795 + 595815 * 2 ^ 59
def prefixEnd_595815 : Nat := 4983230072969 + 3 ^ 40 * 595815 * 2
def baseEnd_595815 : Nat := 305939476158691604772403

theorem tailTrace_595815 : CollatzResearch.WordTrace tailWord_595815 prefixEnd_595815 305939476158691604772403 := by
  unfold tailWord_595815
  simp only [CollatzResearch.WordTrace]
  refine ⟨21731158336471486945812899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14487438890980991297208599 21731158336471486945812899)
  ·
    refine ⟨32596737504707230418719349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21731158336471486945812899 32596737504707230418719349)
    ·
      refine ⟨3055944141066302851754939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32596737504707230418719349 3055944141066302851754939)
      ·
        refine ⟨4583916211599454277632409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3055944141066302851754939 4583916211599454277632409)
        ·
          refine ⟨3437937158699590708224307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4583916211599454277632409 3437937158699590708224307)
          ·
            refine ⟨5156905738049386062336461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3437937158699590708224307 5156905738049386062336461)
            ·
              refine ⟨1933839651768519773376173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5156905738049386062336461 1933839651768519773376173)
              ·
                refine ⟨725189869413194915016065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1933839651768519773376173 725189869413194915016065)
                ·
                  refine ⟨543892402059896186262049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 725189869413194915016065 543892402059896186262049)
                  ·
                    refine ⟨407919301544922139696537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 543892402059896186262049 407919301544922139696537)
                    ·
                      refine ⟨305939476158691604772403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 407919301544922139696537 305939476158691604772403)
                      ·
                        rfl

theorem cell23_595815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_595815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595815 prefixEnd_595815 := by exact prefixLift 595815
  have htrace : WordTrace (prefixWord ++ tailWord_595815) baseStart_595815 baseEnd_595815 := by
    simpa [prefixWord, tailWord_595815, baseEnd_595815] using wordTrace_append hprefix tailTrace_595815
  have hstable : (prefixWord ++ tailWord_595815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595815).length < 2 ^ (prefixWord ++ tailWord_595815).sum := by decide
  have hdescent : baseEnd_595815 < baseStart_595815 := by decide
  rcases family_descends (prefixWord ++ tailWord_595815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595834 : List Nat := [3, 1, 1, 1, 1, 1, 4, 3, 1, 7]
def baseStart_595834 : Nat := 118140960795 + 595834 * 2 ^ 59
def prefixEnd_595834 : Nat := 4983230072969 + 3 ^ 40 * 595834 * 2
def baseEnd_595834 : Nat := 101983077430375676811605

theorem tailTrace_595834 : CollatzResearch.WordTrace tailWord_595834 prefixEnd_595834 101983077430375676811605 := by
  unfold tailWord_595834
  simp only [CollatzResearch.WordTrace]
  refine ⟨5432962830850663297688639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14487900882268435460503037 5432962830850663297688639)
  ·
    refine ⟨8149444246275994946532959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5432962830850663297688639 8149444246275994946532959)
    ·
      refine ⟨12224166369413992419799439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8149444246275994946532959 12224166369413992419799439)
      ·
        refine ⟨18336249554120988629699159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12224166369413992419799439 18336249554120988629699159)
        ·
          refine ⟨27504374331181482944548739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18336249554120988629699159 27504374331181482944548739)
          ·
            refine ⟨41256561496772224416823109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27504374331181482944548739 41256561496772224416823109)
            ·
              refine ⟨7735605280644792078154333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41256561496772224416823109 7735605280644792078154333)
              ·
                refine ⟨2900851980241797029307875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7735605280644792078154333 2900851980241797029307875)
                ·
                  refine ⟨4351277970362695543961813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2900851980241797029307875 4351277970362695543961813)
                  ·
                    refine ⟨101983077430375676811605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4351277970362695543961813 101983077430375676811605)
                    ·
                      rfl

theorem cell23_595834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_595834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595834 prefixEnd_595834 := by exact prefixLift 595834
  have htrace : WordTrace (prefixWord ++ tailWord_595834) baseStart_595834 baseEnd_595834 := by
    simpa [prefixWord, tailWord_595834, baseEnd_595834] using wordTrace_append hprefix tailTrace_595834
  have hstable : (prefixWord ++ tailWord_595834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595834).length < 2 ^ (prefixWord ++ tailWord_595834).sum := by decide
  have hdescent : baseEnd_595834 < baseStart_595834 := by decide
  rcases family_descends (prefixWord ++ tailWord_595834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595862 : List Nat := [5, 3, 1, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_595862 : Nat := 118140960795 + 595862 * 2 ^ 59
def prefixEnd_595862 : Nat := 4983230072969 + 3 ^ 40 * 595862 * 2
def baseEnd_595862 : Nat := 305963609749452920884687

theorem tailTrace_595862 : CollatzResearch.WordTrace tailWord_595862 prefixEnd_595862 305963609749452920884687 := by
  unfold tailWord_595862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1358304535456325873298365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14488581711534142648515893 1358304535456325873298365)
  ·
    refine ⟨509364200796122202486887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1358304535456325873298365 509364200796122202486887)
    ·
      refine ⟨764046301194183303730331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 509364200796122202486887 764046301194183303730331)
      ·
        refine ⟨1146069451791274955595497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 764046301194183303730331 1146069451791274955595497)
        ·
          refine ⟨859552088843456216696623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1146069451791274955595497 859552088843456216696623)
          ·
            refine ⟨1289328133265184325044935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 859552088843456216696623 1289328133265184325044935)
            ·
              refine ⟨1933992199897776487567403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1289328133265184325044935 1933992199897776487567403)
              ·
                refine ⟨2900988299846664731351105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1933992199897776487567403 2900988299846664731351105)
                ·
                  refine ⟨2175741224884998548513329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2900988299846664731351105 2175741224884998548513329)
                  ·
                    refine ⟨1631805918663748911384997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2175741224884998548513329 1631805918663748911384997)
                    ·
                      refine ⟨305963609749452920884687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1631805918663748911384997 305963609749452920884687)
                      ·
                        rfl

theorem cell23_595862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_595862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595862 prefixEnd_595862 := by exact prefixLift 595862
  have htrace : WordTrace (prefixWord ++ tailWord_595862) baseStart_595862 baseEnd_595862 := by
    simpa [prefixWord, tailWord_595862, baseEnd_595862] using wordTrace_append hprefix tailTrace_595862
  have hstable : (prefixWord ++ tailWord_595862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595862).length < 2 ^ (prefixWord ++ tailWord_595862).sum := by decide
  have hdescent : baseEnd_595862 < baseStart_595862 := by decide
  rcases family_descends (prefixWord ++ tailWord_595862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595884 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 6]
def baseStart_595884 : Nat := 118140960795 + 595884 * 2 ^ 59
def prefixEnd_595884 : Nat := 4983230072969 + 3 ^ 40 * 595884 * 2
def baseEnd_595884 : Nat := 305974906323851834809585

theorem tailTrace_595884 : CollatzResearch.WordTrace tailWord_595884 prefixEnd_595884 305974906323851834809585 := by
  unfold tailWord_595884
  simp only [CollatzResearch.WordTrace]
  refine ⟨10866837486610755865037353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14489116648814341153383137 10866837486610755865037353)
  ·
    refine ⟨8150128114958066898778015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10866837486610755865037353 8150128114958066898778015)
    ·
      refine ⟨12225192172437100348167023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8150128114958066898778015 12225192172437100348167023)
      ·
        refine ⟨18337788258655650522250535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12225192172437100348167023 18337788258655650522250535)
        ·
          refine ⟨27506682387983475783375803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18337788258655650522250535 27506682387983475783375803)
          ·
            refine ⟨41260023581975213675063705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27506682387983475783375803 41260023581975213675063705)
            ·
              refine ⟨30945017686481410256297779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41260023581975213675063705 30945017686481410256297779)
              ·
                refine ⟨46417526529722115384446669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30945017686481410256297779 46417526529722115384446669)
                ·
                  refine ⟨17406572448645793269167501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46417526529722115384446669 17406572448645793269167501)
                  ·
                    refine ⟨6527464668242172475937813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17406572448645793269167501 6527464668242172475937813)
                    ·
                      refine ⟨305974906323851834809585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6527464668242172475937813 305974906323851834809585)
                      ·
                        rfl

theorem cell23_595884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_595884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595884 prefixEnd_595884 := by exact prefixLift 595884
  have htrace : WordTrace (prefixWord ++ tailWord_595884) baseStart_595884 baseEnd_595884 := by
    simpa [prefixWord, tailWord_595884, baseEnd_595884] using wordTrace_append hprefix tailTrace_595884
  have hstable : (prefixWord ++ tailWord_595884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595884).length < 2 ^ (prefixWord ++ tailWord_595884).sum := by decide
  have hdescent : baseEnd_595884 < baseStart_595884 := by decide
  rcases family_descends (prefixWord ++ tailWord_595884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595891 : List Nat := [1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 3]
def baseStart_595891 : Nat := 118140960795 + 595891 * 2 ^ 59
def prefixEnd_595891 : Nat := 4983230072969 + 3 ^ 40 * 595891 * 2
def baseEnd_595891 : Nat := 305978500688433307422053

theorem tailTrace_595891 : CollatzResearch.WordTrace tailWord_595891 prefixEnd_595891 305978500688433307422053 := by
  unfold tailWord_595891
  simp only [CollatzResearch.WordTrace]
  refine ⟨21733930284196151925579527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14489286856130767950386351 21733930284196151925579527)
  ·
    refine ⟨32600895426294227888369291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21733930284196151925579527 32600895426294227888369291)
    ·
      refine ⟨48901343139441341832553937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32600895426294227888369291 48901343139441341832553937)
      ·
        refine ⟨36676007354581006374415453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48901343139441341832553937 36676007354581006374415453)
        ·
          refine ⟨13753502757967877390405795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36676007354581006374415453 13753502757967877390405795)
          ·
            refine ⟨20630254136951816085608693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13753502757967877390405795 20630254136951816085608693)
            ·
              refine ⟨1934086325339232758025815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20630254136951816085608693 1934086325339232758025815)
              ·
                refine ⟨2901129488008849137038723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1934086325339232758025815 2901129488008849137038723)
                ·
                  refine ⟨4351694232013273705558085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2901129488008849137038723 4351694232013273705558085)
                  ·
                    refine ⟨815942668502488819792141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4351694232013273705558085 815942668502488819792141)
                    ·
                      refine ⟨305978500688433307422053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 815942668502488819792141 305978500688433307422053)
                      ·
                        rfl

theorem cell23_595891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 3].length) (baseStart_595891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595891 prefixEnd_595891 := by exact prefixLift 595891
  have htrace : WordTrace (prefixWord ++ tailWord_595891) baseStart_595891 baseEnd_595891 := by
    simpa [prefixWord, tailWord_595891, baseEnd_595891] using wordTrace_append hprefix tailTrace_595891
  have hstable : (prefixWord ++ tailWord_595891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595891).length < 2 ^ (prefixWord ++ tailWord_595891).sum := by decide
  have hdescent : baseEnd_595891 < baseStart_595891 := by decide
  rcases family_descends (prefixWord ++ tailWord_595891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595901 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 2, 1, 6]
def baseStart_595901 : Nat := 118140960795 + 595901 * 2 ^ 59
def prefixEnd_595901 : Nat := 4983230072969 + 3 ^ 40 * 595901 * 2
def baseEnd_595901 : Nat := 305983635494978268297007

theorem tailTrace_595901 : CollatzResearch.WordTrace tailWord_595901 prefixEnd_595901 305983635494978268297007 := by
  unfold tailWord_595901
  simp only [CollatzResearch.WordTrace]
  refine ⟨21734295014159923633443557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14489530009439949088962371 21734295014159923633443557)
  ·
    refine ⟨4075180315154985681270667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21734295014159923633443557 4075180315154985681270667)
    ·
      refine ⟨6112770472732478521906001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4075180315154985681270667 6112770472732478521906001)
      ·
        refine ⟨4584577854549358891429501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6112770472732478521906001 4584577854549358891429501)
        ·
          refine ⟨1719216695456009584286063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4584577854549358891429501 1719216695456009584286063)
          ·
            refine ⟨2578825043184014376429095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1719216695456009584286063 2578825043184014376429095)
            ·
              refine ⟨3868237564776021564643643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2578825043184014376429095 3868237564776021564643643)
              ·
                refine ⟨5802356347164032346965465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3868237564776021564643643 5802356347164032346965465)
                ·
                  refine ⟨4351767260373024260224099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5802356347164032346965465 4351767260373024260224099)
                  ·
                    refine ⟨6527650890559536390336149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4351767260373024260224099 6527650890559536390336149)
                    ·
                      refine ⟨305983635494978268297007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6527650890559536390336149 305983635494978268297007)
                      ·
                        rfl

theorem cell23_595901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_595901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595901 prefixEnd_595901 := by exact prefixLift 595901
  have htrace : WordTrace (prefixWord ++ tailWord_595901) baseStart_595901 baseEnd_595901 := by
    simpa [prefixWord, tailWord_595901, baseEnd_595901] using wordTrace_append hprefix tailTrace_595901
  have hstable : (prefixWord ++ tailWord_595901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595901).length < 2 ^ (prefixWord ++ tailWord_595901).sum := by decide
  have hdescent : baseEnd_595901 < baseStart_595901 := by decide
  rcases family_descends (prefixWord ++ tailWord_595901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595928 : List Nat := [2, 1, 2, 2, 2, 2, 5, 1, 6]
def baseStart_595928 : Nat := 118140960795 + 595928 * 2 ^ 59
def prefixEnd_595928 : Nat := 4983230072969 + 3 ^ 40 * 595928 * 2
def baseEnd_595928 : Nat := 33999722163627740295487

theorem tailTrace_595928 : CollatzResearch.WordTrace tailWord_595928 prefixEnd_595928 33999722163627740295487 := by
  unfold tailWord_595928
  simp only [CollatzResearch.WordTrace]
  refine ⟨10867639892531053622338219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14490186523374738163117625 10867639892531053622338219)
  ·
    refine ⟨16301459838796580433507329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10867639892531053622338219 16301459838796580433507329)
    ·
      refine ⟨12226094879097435325130497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16301459838796580433507329 12226094879097435325130497)
      ·
        refine ⟨9169571159323076493847873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12226094879097435325130497 9169571159323076493847873)
        ·
          refine ⟨6877178369492307370385905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9169571159323076493847873 6877178369492307370385905)
          ·
            refine ⟨5157883777119230527789429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6877178369492307370385905 5157883777119230527789429)
            ·
              refine ⟨483551604104927861980259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5157883777119230527789429 483551604104927861980259)
              ·
                refine ⟨725327406157391792970389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483551604104927861980259 725327406157391792970389)
                ·
                  refine ⟨33999722163627740295487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 725327406157391792970389 33999722163627740295487)
                  ·
                    rfl

theorem cell23_595928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 6].length) (baseStart_595928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595928 prefixEnd_595928 := by exact prefixLift 595928
  have htrace : WordTrace (prefixWord ++ tailWord_595928) baseStart_595928 baseEnd_595928 := by
    simpa [prefixWord, tailWord_595928, baseEnd_595928] using wordTrace_append hprefix tailTrace_595928
  have hstable : (prefixWord ++ tailWord_595928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595928).length < 2 ^ (prefixWord ++ tailWord_595928).sum := by decide
  have hdescent : baseEnd_595928 < baseStart_595928 := by decide
  rcases family_descends (prefixWord ++ tailWord_595928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595948 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 6, 3, 2]
def baseStart_595948 : Nat := 118140960795 + 595948 * 2 ^ 59
def prefixEnd_595948 : Nat := 4983230072969 + 3 ^ 40 * 595948 * 2
def baseEnd_595948 : Nat := 306007769085739584409291

theorem tailTrace_595948 : CollatzResearch.WordTrace tailWord_595948 prefixEnd_595948 306007769085739584409291 := by
  unfold tailWord_595948
  simp only [CollatzResearch.WordTrace]
  refine ⟨10868004622494825330202249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14490672829993100440269665 10868004622494825330202249)
  ·
    refine ⟨8151003466871118997651687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10868004622494825330202249 8151003466871118997651687)
    ·
      refine ⟨12226505200306678496477531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8151003466871118997651687 12226505200306678496477531)
      ·
        refine ⟨18339757800460017744716297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12226505200306678496477531 18339757800460017744716297)
        ·
          refine ⟨13754818350345013308537223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18339757800460017744716297 13754818350345013308537223)
          ·
            refine ⟨20632227525517519962805835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13754818350345013308537223 20632227525517519962805835)
            ·
              refine ⟨30948341288276279944208753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20632227525517519962805835 30948341288276279944208753)
              ·
                refine ⟨23211255966207209958156565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30948341288276279944208753 23211255966207209958156565)
                ·
                  refine ⟨1088027623415962966788589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23211255966207209958156565 1088027623415962966788589)
                  ·
                    refine ⟨408010358780986112545721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1088027623415962966788589 408010358780986112545721)
                    ·
                      refine ⟨306007769085739584409291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 408010358780986112545721 306007769085739584409291)
                      ·
                        rfl

theorem cell23_595948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 3, 2].length) (baseStart_595948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_595948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_595948 prefixEnd_595948 := by exact prefixLift 595948
  have htrace : WordTrace (prefixWord ++ tailWord_595948) baseStart_595948 baseEnd_595948 := by
    simpa [prefixWord, tailWord_595948, baseEnd_595948] using wordTrace_append hprefix tailTrace_595948
  have hstable : (prefixWord ++ tailWord_595948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595948).length < 2 ^ (prefixWord ++ tailWord_595948).sum := by decide
  have hdescent : baseEnd_595948 < baseStart_595948 := by decide
  rcases family_descends (prefixWord ++ tailWord_595948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596022 : List Nat := [5, 1, 2, 1, 1, 1, 4, 2, 2, 4]
def baseStart_596022 : Nat := 118140960795 + 596022 * 2 ^ 59
def prefixEnd_596022 : Nat := 4983230072969 + 3 ^ 40 * 596022 * 2
def baseEnd_596022 : Nat := 102015255551390764961317

theorem tailTrace_596022 : CollatzResearch.WordTrace tailWord_596022 prefixEnd_596022 102015255551390764961317 := by
  unfold tailWord_596022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1358669265420097581162395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14492472164481040865732213 1358669265420097581162395)
  ·
    refine ⟨2038003898130146371743593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1358669265420097581162395 2038003898130146371743593)
    ·
      refine ⟨1528502923597609778807695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2038003898130146371743593 1528502923597609778807695)
      ·
        refine ⟨2292754385396414668211543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1528502923597609778807695 2292754385396414668211543)
        ·
          refine ⟨3439131578094622002317315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2292754385396414668211543 3439131578094622002317315)
          ·
            refine ⟨5158697367141933003475973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3439131578094622002317315 5158697367141933003475973)
            ·
              refine ⟨967255756339112438151745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5158697367141933003475973 967255756339112438151745)
              ·
                refine ⟨725441817254334328613809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 967255756339112438151745 725441817254334328613809)
                ·
                  refine ⟨544081362940750746460357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 725441817254334328613809 544081362940750746460357)
                  ·
                    refine ⟨102015255551390764961317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 544081362940750746460357 102015255551390764961317)
                    ·
                      rfl

theorem cell23_596022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_596022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596022 prefixEnd_596022 := by exact prefixLift 596022
  have htrace : WordTrace (prefixWord ++ tailWord_596022) baseStart_596022 baseEnd_596022 := by
    simpa [prefixWord, tailWord_596022, baseEnd_596022] using wordTrace_append hprefix tailTrace_596022
  have hstable : (prefixWord ++ tailWord_596022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596022).length < 2 ^ (prefixWord ++ tailWord_596022).sum := by decide
  have hdescent : baseEnd_596022 < baseStart_596022 := by decide
  rcases family_descends (prefixWord ++ tailWord_596022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596028 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 3, 3, 3]
def baseStart_596028 : Nat := 118140960795 + 596028 * 2 ^ 59
def prefixEnd_596028 : Nat := 4983230072969 + 3 ^ 40 * 596028 * 2
def baseEnd_596028 : Nat := 306048847538099271408923

theorem tailTrace_596028 : CollatzResearch.WordTrace tailWord_596028 prefixEnd_596028 306048847538099271408923 := by
  unfold tailWord_596028
  simp only [CollatzResearch.WordTrace]
  refine ⟨10869463542349912161658369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14492618056466549548877825 10869463542349912161658369)
  ·
    refine ⟨8152097656762434121243777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10869463542349912161658369 8152097656762434121243777)
    ·
      refine ⟨6114073242571825590932833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8152097656762434121243777 6114073242571825590932833)
      ·
        refine ⟨4585554931928869193199625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6114073242571825590932833 4585554931928869193199625)
        ·
          refine ⟨3439166198946651894899719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4585554931928869193199625 3439166198946651894899719)
          ·
            refine ⟨5158749298419977842349579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3439166198946651894899719 5158749298419977842349579)
            ·
              refine ⟨7738123947629966763524369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5158749298419977842349579 7738123947629966763524369)
              ·
                refine ⟨5803592960722475072643277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7738123947629966763524369 5803592960722475072643277)
                ·
                  refine ⟨2176347360270928152241229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5803592960722475072643277 2176347360270928152241229)
                  ·
                    refine ⟨816130260101598057090461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2176347360270928152241229 816130260101598057090461)
                    ·
                      refine ⟨306048847538099271408923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 816130260101598057090461 306048847538099271408923)
                      ·
                        rfl

theorem cell23_596028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_596028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596028 prefixEnd_596028 := by exact prefixLift 596028
  have htrace : WordTrace (prefixWord ++ tailWord_596028) baseStart_596028 baseEnd_596028 := by
    simpa [prefixWord, tailWord_596028, baseEnd_596028] using wordTrace_append hprefix tailTrace_596028
  have hstable : (prefixWord ++ tailWord_596028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596028).length < 2 ^ (prefixWord ++ tailWord_596028).sum := by decide
  have hdescent : baseEnd_596028 < baseStart_596028 := by decide
  rcases family_descends (prefixWord ++ tailWord_596028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596029 : List Nat := [1, 4, 1, 3, 1, 1, 3, 4, 1, 2, 2]
def baseStart_596029 : Nat := 118140960795 + 596029 * 2 ^ 59
def prefixEnd_596029 : Nat := 4983230072969 + 3 ^ 40 * 596029 * 2
def baseEnd_596029 : Nat := 306049361018753767496419

theorem tailTrace_596029 : CollatzResearch.WordTrace tailWord_596029 prefixEnd_596029 306049361018753767496419 := by
  unfold tailWord_596029
  simp only [CollatzResearch.WordTrace]
  refine ⟨21738963557696201494103141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14492642371797467662735427 21738963557696201494103141)
  ·
    refine ⟨4076055667068037780144339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21738963557696201494103141 4076055667068037780144339)
    ·
      refine ⟨6114083500602056670216509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4076055667068037780144339 6114083500602056670216509)
      ·
        refine ⟨2292781312725771251331191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6114083500602056670216509 2292781312725771251331191)
        ·
          refine ⟨3439171969088656876996787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2292781312725771251331191 3439171969088656876996787)
          ·
            refine ⟨5158757953632985315495181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3439171969088656876996787 5158757953632985315495181)
            ·
              refine ⟨1934534232612369493310693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5158757953632985315495181 1934534232612369493310693)
              ·
                refine ⟨362725168614819279995755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1934534232612369493310693 362725168614819279995755)
                ·
                  refine ⟨544087752922228919993633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 362725168614819279995755 544087752922228919993633)
                  ·
                    refine ⟨408065814691671689995225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 544087752922228919993633 408065814691671689995225)
                    ·
                      refine ⟨306049361018753767496419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 408065814691671689995225 306049361018753767496419)
                      ·
                        rfl

theorem cell23_596029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_596029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596029 prefixEnd_596029 := by exact prefixLift 596029
  have htrace : WordTrace (prefixWord ++ tailWord_596029) baseStart_596029 baseEnd_596029 := by
    simpa [prefixWord, tailWord_596029, baseEnd_596029] using wordTrace_append hprefix tailTrace_596029
  have hstable : (prefixWord ++ tailWord_596029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596029).length < 2 ^ (prefixWord ++ tailWord_596029).sum := by decide
  have hdescent : baseEnd_596029 < baseStart_596029 := by decide
  rcases family_descends (prefixWord ++ tailWord_596029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596031 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 2, 7]
def baseStart_596031 : Nat := 118140960795 + 596031 * 2 ^ 59
def prefixEnd_596031 : Nat := 4983230072969 + 3 ^ 40 * 596031 * 2
def baseEnd_596031 : Nat := 102016795993354253223803

theorem tailTrace_596031 : CollatzResearch.WordTrace tailWord_596031 prefixEnd_596031 102016795993354253223803 := by
  unfold tailWord_596031
  simp only [CollatzResearch.WordTrace]
  refine ⟨21739036503688955835675947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14492691002459303890450631 21739036503688955835675947)
  ·
    refine ⟨32608554755533433753513921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21739036503688955835675947 32608554755533433753513921)
    ·
      refine ⟨24456416066650075315135441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32608554755533433753513921 24456416066650075315135441)
      ·
        refine ⟨18342312049987556486351581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24456416066650075315135441 18342312049987556486351581)
        ·
          refine ⟨6878367018745333682381843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18342312049987556486351581 6878367018745333682381843)
          ·
            refine ⟨10317550528118000523572765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6878367018745333682381843 10317550528118000523572765)
            ·
              refine ⟨3869081448044250196339787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10317550528118000523572765 3869081448044250196339787)
              ·
                refine ⟨5803622172066375294509681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3869081448044250196339787 5803622172066375294509681)
                ·
                  refine ⟨4352716629049781470882261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5803622172066375294509681 4352716629049781470882261)
                  ·
                    refine ⟨102016795993354253223803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4352716629049781470882261 102016795993354253223803)
                    ·
                      rfl

theorem cell23_596031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 7].length) (baseStart_596031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596031 prefixEnd_596031 := by exact prefixLift 596031
  have htrace : WordTrace (prefixWord ++ tailWord_596031) baseStart_596031 baseEnd_596031 := by
    simpa [prefixWord, tailWord_596031, baseEnd_596031] using wordTrace_append hprefix tailTrace_596031
  have hstable : (prefixWord ++ tailWord_596031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596031).length < 2 ^ (prefixWord ++ tailWord_596031).sum := by decide
  have hdescent : baseEnd_596031 < baseStart_596031 := by decide
  rcases family_descends (prefixWord ++ tailWord_596031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596051 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 4]
def baseStart_596051 : Nat := 118140960795 + 596051 * 2 ^ 59
def prefixEnd_596051 : Nat := 4983230072969 + 3 ^ 40 * 596051 * 2
def baseEnd_596051 : Nat := 306060657593152681421317

theorem tailTrace_596051 : CollatzResearch.WordTrace tailWord_596051 prefixEnd_596051 306060657593152681421317 := by
  unfold tailWord_596051
  simp only [CollatzResearch.WordTrace]
  refine ⟨21739765963616499251404007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14493177309077666167602671 21739765963616499251404007)
  ·
    refine ⟨32609648945424748877106011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21739765963616499251404007 32609648945424748877106011)
    ·
      refine ⟨48914473418137123315659017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32609648945424748877106011 48914473418137123315659017)
      ·
        refine ⟨36685855063602842486744263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48914473418137123315659017 36685855063602842486744263)
        ·
          refine ⟨55028782595404263730116395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36685855063602842486744263 55028782595404263730116395)
          ·
            refine ⟨82543173893106395595174593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55028782595404263730116395 82543173893106395595174593)
            ·
              refine ⟨61907380419829796696380945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82543173893106395595174593 61907380419829796696380945)
              ·
                refine ⟨46430535314872347522285709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61907380419829796696380945 46430535314872347522285709)
                ·
                  refine ⟨17411450743077130320857141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46430535314872347522285709 17411450743077130320857141)
                  ·
                    refine ⟨1632323507163480967580357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17411450743077130320857141 1632323507163480967580357)
                    ·
                      refine ⟨306060657593152681421317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1632323507163480967580357 306060657593152681421317)
                      ·
                        rfl

theorem cell23_596051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 4].length) (baseStart_596051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596051 prefixEnd_596051 := by exact prefixLift 596051
  have htrace : WordTrace (prefixWord ++ tailWord_596051) baseStart_596051 baseEnd_596051 := by
    simpa [prefixWord, tailWord_596051, baseEnd_596051] using wordTrace_append hprefix tailTrace_596051
  have hstable : (prefixWord ++ tailWord_596051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596051).length < 2 ^ (prefixWord ++ tailWord_596051).sum := by decide
  have hdescent : baseEnd_596051 < baseStart_596051 := by decide
  rcases family_descends (prefixWord ++ tailWord_596051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596055 : List Nat := [1, 1, 3, 2, 2, 1, 4, 1, 3, 3, 2]
def baseStart_596055 : Nat := 118140960795 + 596055 * 2 ^ 59
def prefixEnd_596055 : Nat := 4983230072969 + 3 ^ 40 * 596055 * 2
def baseEnd_596055 : Nat := 306062711515770665771299

theorem tailTrace_596055 : CollatzResearch.WordTrace tailWord_596055 prefixEnd_596055 306062711515770665771299 := by
  unfold tailWord_596055
  simp only [CollatzResearch.WordTrace]
  refine ⟨21739911855602007934549619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14493274570401338623033079 21739911855602007934549619)
  ·
    refine ⟨32609867783403011901824429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21739911855602007934549619 32609867783403011901824429)
    ·
      refine ⟨12228700418776129463184161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32609867783403011901824429 12228700418776129463184161)
      ·
        refine ⟨9171525314082097097388121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12228700418776129463184161 9171525314082097097388121)
        ·
          refine ⟨6878643985561572823041091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9171525314082097097388121 6878643985561572823041091)
          ·
            refine ⟨10317965978342359234561637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6878643985561572823041091 10317965978342359234561637)
            ·
              refine ⟨1934618620939192356480307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10317965978342359234561637 1934618620939192356480307)
              ·
                refine ⟨2901927931408788534720461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1934618620939192356480307 2901927931408788534720461)
                ·
                  refine ⟨1088222974278295700520173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2901927931408788534720461 1088222974278295700520173)
                  ·
                    refine ⟨408083615354360887695065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1088222974278295700520173 408083615354360887695065)
                    ·
                      refine ⟨306062711515770665771299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 408083615354360887695065 306062711515770665771299)
                      ·
                        rfl

theorem cell23_596055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 3, 2].length) (baseStart_596055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596055 prefixEnd_596055 := by exact prefixLift 596055
  have htrace : WordTrace (prefixWord ++ tailWord_596055) baseStart_596055 baseEnd_596055 := by
    simpa [prefixWord, tailWord_596055, baseEnd_596055] using wordTrace_append hprefix tailTrace_596055
  have hstable : (prefixWord ++ tailWord_596055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596055).length < 2 ^ (prefixWord ++ tailWord_596055).sum := by decide
  have hdescent : baseEnd_596055 < baseStart_596055 := by decide
  rcases family_descends (prefixWord ++ tailWord_596055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596066 : List Nat := [3, 3, 2, 2, 2, 2, 2, 1, 1, 2, 3]
def baseStart_596066 : Nat := 118140960795 + 596066 * 2 ^ 59
def prefixEnd_596066 : Nat := 4983230072969 + 3 ^ 40 * 596066 * 2
def baseEnd_596066 : Nat := 306068359802970122733749

theorem tailTrace_596066 : CollatzResearch.WordTrace tailWord_596066 prefixEnd_596066 306068359802970122733749 := by
  unfold tailWord_596066
  simp only [CollatzResearch.WordTrace]
  refine ⟨5435078264640539203300013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14493542039041437875466701 5435078264640539203300013)
  ·
    refine ⟨2038154349240202201237505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5435078264640539203300013 2038154349240202201237505)
    ·
      refine ⟨1528615761930151650928129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2038154349240202201237505 1528615761930151650928129)
      ·
        refine ⟨1146461821447613738196097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1528615761930151650928129 1146461821447613738196097)
        ·
          refine ⟨859846366085710303647073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1146461821447613738196097 859846366085710303647073)
          ·
            refine ⟨644884774564282727735305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 859846366085710303647073 644884774564282727735305)
            ·
              refine ⟨483663580923212045801479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 644884774564282727735305 483663580923212045801479)
              ·
                refine ⟨725495371384818068702219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483663580923212045801479 725495371384818068702219)
                ·
                  refine ⟨1088243057077227103053329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 725495371384818068702219 1088243057077227103053329)
                  ·
                    refine ⟨816182292807920327289997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1088243057077227103053329 816182292807920327289997)
                    ·
                      refine ⟨306068359802970122733749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 816182292807920327289997 306068359802970122733749)
                      ·
                        rfl

theorem cell23_596066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_596066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596066 prefixEnd_596066 := by exact prefixLift 596066
  have htrace : WordTrace (prefixWord ++ tailWord_596066) baseStart_596066 baseEnd_596066 := by
    simpa [prefixWord, tailWord_596066, baseEnd_596066] using wordTrace_append hprefix tailTrace_596066
  have hstable : (prefixWord ++ tailWord_596066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596066).length < 2 ^ (prefixWord ++ tailWord_596066).sum := by decide
  have hdescent : baseEnd_596066 < baseStart_596066 := by decide
  rcases family_descends (prefixWord ++ tailWord_596066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596078 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 4, 6]
def baseStart_596078 : Nat := 118140960795 + 596078 * 2 ^ 59
def prefixEnd_596078 : Nat := 4983230072969 + 3 ^ 40 * 596078 * 2
def baseEnd_596078 : Nat := 102024840523608025261231

theorem tailTrace_596078 : CollatzResearch.WordTrace tailWord_596078 prefixEnd_596078 102024840523608025261231 := by
  unfold tailWord_596078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2717593841814835357829611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14493833823012455241757925 2717593841814835357829611)
  ·
    refine ⟨4076390762722253036744417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2717593841814835357829611 4076390762722253036744417)
    ·
      refine ⟨3057293072041689777558313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4076390762722253036744417 3057293072041689777558313)
      ·
        refine ⟨2292969804031267333168735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3057293072041689777558313 2292969804031267333168735)
        ·
          refine ⟨3439454706046900999753103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2292969804031267333168735 3439454706046900999753103)
          ·
            refine ⟨5159182059070351499629655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3439454706046900999753103 5159182059070351499629655)
            ·
              refine ⟨7738773088605527249444483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5159182059070351499629655 7738773088605527249444483)
              ·
                refine ⟨11608159632908290874166725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7738773088605527249444483 11608159632908290874166725)
                ·
                  refine ⟨2176529931170304538906261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11608159632908290874166725 2176529931170304538906261)
                  ·
                    refine ⟨102024840523608025261231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2176529931170304538906261 102024840523608025261231)
                    ·
                      rfl

theorem cell23_596078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_596078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596078 prefixEnd_596078 := by exact prefixLift 596078
  have htrace : WordTrace (prefixWord ++ tailWord_596078) baseStart_596078 baseEnd_596078 := by
    simpa [prefixWord, tailWord_596078, baseEnd_596078] using wordTrace_append hprefix tailTrace_596078
  have hstable : (prefixWord ++ tailWord_596078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596078).length < 2 ^ (prefixWord ++ tailWord_596078).sum := by decide
  have hdescent : baseEnd_596078 < baseStart_596078 := by decide
  rcases family_descends (prefixWord ++ tailWord_596078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596175 : List Nat := [1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 4]
def baseStart_596175 : Nat := 118140960795 + 596175 * 2 ^ 59
def prefixEnd_596175 : Nat := 4983230072969 + 3 ^ 40 * 596175 * 2
def baseEnd_596175 : Nat := 306124329194310196270747

theorem tailTrace_596175 : CollatzResearch.WordTrace tailWord_596175 prefixEnd_596175 306124329194310196270747 := by
  unfold tailWord_596175
  simp only [CollatzResearch.WordTrace]
  refine ⟨21744288615167268428917979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14496192410111512285945319 21744288615167268428917979)
  ·
    refine ⟨32616432922750902643376969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21744288615167268428917979 32616432922750902643376969)
    ·
      refine ⟨24462324692063176982532727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32616432922750902643376969 24462324692063176982532727)
      ·
        refine ⟨36693487038094765473799091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24462324692063176982532727 36693487038094765473799091)
        ·
          refine ⟨55040230557142148210698637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36693487038094765473799091 55040230557142148210698637)
          ·
            refine ⟨20640086458928305579011989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55040230557142148210698637 20640086458928305579011989)
            ·
              refine ⟨967504052762264324016187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20640086458928305579011989 967504052762264324016187)
              ·
                refine ⟨1451256079143396486024281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 967504052762264324016187 1451256079143396486024281)
                ·
                  refine ⟨1088442059357547364518211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1451256079143396486024281 1088442059357547364518211)
                  ·
                    refine ⟨1632663089036321046777317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1088442059357547364518211 1632663089036321046777317)
                    ·
                      refine ⟨306124329194310196270747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1632663089036321046777317 306124329194310196270747)
                      ·
                        rfl

theorem cell23_596175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 4].length) (baseStart_596175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596175 prefixEnd_596175 := by exact prefixLift 596175
  have htrace : WordTrace (prefixWord ++ tailWord_596175) baseStart_596175 baseEnd_596175 := by
    simpa [prefixWord, tailWord_596175, baseEnd_596175] using wordTrace_append hprefix tailTrace_596175
  have hstable : (prefixWord ++ tailWord_596175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596175).length < 2 ^ (prefixWord ++ tailWord_596175).sum := by decide
  have hdescent : baseEnd_596175 < baseStart_596175 := by decide
  rcases family_descends (prefixWord ++ tailWord_596175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596182 : List Nat := [5, 2, 1, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_596182 : Nat := 118140960795 + 596182 * 2 ^ 59
def prefixEnd_596182 : Nat := 4983230072969 + 3 ^ 40 * 596182 * 2
def baseEnd_596182 : Nat := 306127923558891668883215

theorem tailTrace_596182 : CollatzResearch.WordTrace tailWord_596182 prefixEnd_596182 306127923558891668883215 := by
  unfold tailWord_596182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1359033995383869289026425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14496362617427939082948533 1359033995383869289026425)
  ·
    refine ⟨1019275496537901966769819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1359033995383869289026425 1019275496537901966769819)
    ·
      refine ⟨1528913244806852950154729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1019275496537901966769819 1528913244806852950154729)
      ·
        refine ⟨1146684933605139712616047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1528913244806852950154729 1146684933605139712616047)
        ·
          refine ⟨1720027400407709568924071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1146684933605139712616047 1720027400407709568924071)
          ·
            refine ⟨2580041100611564353386107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1720027400407709568924071 2580041100611564353386107)
            ·
              refine ⟨3870061650917346530079161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2580041100611564353386107 3870061650917346530079161)
              ·
                refine ⟨2902546238188009897559371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3870061650917346530079161 2902546238188009897559371)
                ·
                  refine ⟨4353819357282014846339057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2902546238188009897559371 4353819357282014846339057)
                  ·
                    refine ⟨3265364517961511134754293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4353819357282014846339057 3265364517961511134754293)
                    ·
                      refine ⟨306127923558891668883215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3265364517961511134754293 306127923558891668883215)
                      ·
                        rfl

theorem cell23_596182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_596182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596182 prefixEnd_596182 := by exact prefixLift 596182
  have htrace : WordTrace (prefixWord ++ tailWord_596182) baseStart_596182 baseEnd_596182 := by
    simpa [prefixWord, tailWord_596182, baseEnd_596182] using wordTrace_append hprefix tailTrace_596182
  have hstable : (prefixWord ++ tailWord_596182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596182).length < 2 ^ (prefixWord ++ tailWord_596182).sum := by decide
  have hdescent : baseEnd_596182 < baseStart_596182 := by decide
  rcases family_descends (prefixWord ++ tailWord_596182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596252 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 4, 3, 2]
def baseStart_596252 : Nat := 118140960795 + 596252 * 2 ^ 59
def prefixEnd_596252 : Nat := 4983230072969 + 3 ^ 40 * 596252 * 2
def baseEnd_596252 : Nat := 306163867204706395007893

theorem tailTrace_596252 : CollatzResearch.WordTrace tailWord_596252 prefixEnd_596252 306163867204706395007893 := by
  unfold tailWord_596252
  simp only [CollatzResearch.WordTrace]
  refine ⟨10873548517944155289735505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14498064690592207052980673 10873548517944155289735505)
  ·
    refine ⟨8155161388458116467301629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10873548517944155289735505 8155161388458116467301629)
    ·
      refine ⟨3058185520671793675238111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8155161388458116467301629 3058185520671793675238111)
      ·
        refine ⟨4587278281007690512857167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3058185520671793675238111 4587278281007690512857167)
        ·
          refine ⟨6880917421511535769285751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4587278281007690512857167 6880917421511535769285751)
          ·
            refine ⟨10321376132267303653928627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6880917421511535769285751 10321376132267303653928627)
            ·
              refine ⟨15482064198400955480892941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10321376132267303653928627 15482064198400955480892941)
              ·
                refine ⟨5805774074400358305334853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15482064198400955480892941 5805774074400358305334853)
                ·
                  refine ⟨1088582638950067182250285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5805774074400358305334853 1088582638950067182250285)
                  ·
                    refine ⟨408218489606275193343857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1088582638950067182250285 408218489606275193343857)
                    ·
                      refine ⟨306163867204706395007893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 408218489606275193343857 306163867204706395007893)
                      ·
                        rfl

theorem cell23_596252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_596252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596252 prefixEnd_596252 := by exact prefixLift 596252
  have htrace : WordTrace (prefixWord ++ tailWord_596252) baseStart_596252 baseEnd_596252 := by
    simpa [prefixWord, tailWord_596252, baseEnd_596252] using wordTrace_append hprefix tailTrace_596252
  have hstable : (prefixWord ++ tailWord_596252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596252).length < 2 ^ (prefixWord ++ tailWord_596252).sum := by decide
  have hdescent : baseEnd_596252 < baseStart_596252 := by decide
  rcases family_descends (prefixWord ++ tailWord_596252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596259 : List Nat := [1, 1, 1, 4, 2, 2, 1, 6, 1, 1, 3]
def baseStart_596259 : Nat := 118140960795 + 596259 * 2 ^ 59
def prefixEnd_596259 : Nat := 4983230072969 + 3 ^ 40 * 596259 * 2
def baseEnd_596259 : Nat := 306167461569287867620361

theorem tailTrace_596259 : CollatzResearch.WordTrace tailWord_596259 prefixEnd_596259 306167461569287867620361 := by
  unfold tailWord_596259
  simp only [CollatzResearch.WordTrace]
  refine ⟨21747352346862950774975831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14498234897908633849983887 21747352346862950774975831)
  ·
    refine ⟨32621028520294426162463747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21747352346862950774975831 32621028520294426162463747)
    ·
      refine ⟨48931542780441639243695621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32621028520294426162463747 48931542780441639243695621)
      ·
        refine ⟨9174664271332807358192929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48931542780441639243695621 9174664271332807358192929)
        ·
          refine ⟨6880998203499605518644697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9174664271332807358192929 6880998203499605518644697)
          ·
            refine ⟨5160748652624704138983523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6880998203499605518644697 5160748652624704138983523)
            ·
              refine ⟨7741122978937056208475285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5160748652624704138983523 7741122978937056208475285)
              ·
                refine ⟨362865139637674509772279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7741122978937056208475285 362865139637674509772279)
                ·
                  refine ⟨544297709456511764658419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 362865139637674509772279 544297709456511764658419)
                  ·
                    refine ⟨816446564184767646987629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 544297709456511764658419 816446564184767646987629)
                    ·
                      refine ⟨306167461569287867620361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 816446564184767646987629 306167461569287867620361)
                      ·
                        rfl

theorem cell23_596259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 1, 1, 3].length) (baseStart_596259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596259 prefixEnd_596259 := by exact prefixLift 596259
  have htrace : WordTrace (prefixWord ++ tailWord_596259) baseStart_596259 baseEnd_596259 := by
    simpa [prefixWord, tailWord_596259, baseEnd_596259] using wordTrace_append hprefix tailTrace_596259
  have hstable : (prefixWord ++ tailWord_596259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596259).length < 2 ^ (prefixWord ++ tailWord_596259).sum := by decide
  have hdescent : baseEnd_596259 < baseStart_596259 := by decide
  rcases family_descends (prefixWord ++ tailWord_596259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596282 : List Nat := [3, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4]
def baseStart_596282 : Nat := 118140960795 + 596282 * 2 ^ 59
def prefixEnd_596282 : Nat := 4983230072969 + 3 ^ 40 * 596282 * 2
def baseEnd_596282 : Nat := 306179271624341277632755

theorem tailTrace_596282 : CollatzResearch.WordTrace tailWord_596282 prefixEnd_596282 306179271624341277632755 := by
  unfold tailWord_596282
  simp only [CollatzResearch.WordTrace]
  refine ⟨5437047806444906425765775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14498794150519750468708733 5437047806444906425765775)
  ·
    refine ⟨8155571709667359638648663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5437047806444906425765775 8155571709667359638648663)
    ·
      refine ⟨12233357564501039457972995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8155571709667359638648663 12233357564501039457972995)
      ·
        refine ⟨18350036346751559186959493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12233357564501039457972995 18350036346751559186959493)
        ·
          refine ⟨3440631815015917347554905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18350036346751559186959493 3440631815015917347554905)
          ·
            refine ⟨2580473861261938010666179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3440631815015917347554905 2580473861261938010666179)
            ·
              refine ⟨3870710791892907015999269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2580473861261938010666179 3870710791892907015999269)
              ·
                refine ⟨725758273479920065499863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3870710791892907015999269 725758273479920065499863)
                ·
                  refine ⟨1088637410219880098249795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 725758273479920065499863 1088637410219880098249795)
                  ·
                    refine ⟨1632956115329820147374693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1088637410219880098249795 1632956115329820147374693)
                    ·
                      refine ⟨306179271624341277632755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1632956115329820147374693 306179271624341277632755)
                      ·
                        rfl

theorem cell23_596282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4].length) (baseStart_596282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596282 prefixEnd_596282 := by exact prefixLift 596282
  have htrace : WordTrace (prefixWord ++ tailWord_596282) baseStart_596282 baseEnd_596282 := by
    simpa [prefixWord, tailWord_596282, baseEnd_596282] using wordTrace_append hprefix tailTrace_596282
  have hstable : (prefixWord ++ tailWord_596282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596282).length < 2 ^ (prefixWord ++ tailWord_596282).sum := by decide
  have hdescent : baseEnd_596282 < baseStart_596282 := by decide
  rcases family_descends (prefixWord ++ tailWord_596282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596295 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 4]
def baseStart_596295 : Nat := 118140960795 + 596295 * 2 ^ 59
def prefixEnd_596295 : Nat := 4983230072969 + 3 ^ 40 * 596295 * 2
def baseEnd_596295 : Nat := 306185946872849726770195

theorem tailTrace_596295 : CollatzResearch.WordTrace tailWord_596295 prefixEnd_596295 306185946872849726770195 := by
  unfold tailWord_596295
  simp only [CollatzResearch.WordTrace]
  refine ⟨21748665374732528923286339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14499110249821685948857559 21748665374732528923286339)
  ·
    refine ⟨32622998062098793384929509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21748665374732528923286339 32622998062098793384929509)
    ·
      refine ⟨6116812136643523759674283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32622998062098793384929509 6116812136643523759674283)
      ·
        refine ⟨9175218204965285639511425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6116812136643523759674283 9175218204965285639511425)
        ·
          refine ⟨6881413653723964229633569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9175218204965285639511425 6881413653723964229633569)
          ·
            refine ⟨5161060240292973172225177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6881413653723964229633569 5161060240292973172225177)
            ·
              refine ⟨3870795180219729879168883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5161060240292973172225177 3870795180219729879168883)
              ·
                refine ⟨5806192770329594818753325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3870795180219729879168883 5806192770329594818753325)
                ·
                  refine ⟨2177322288873598057032497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5806192770329594818753325 2177322288873598057032497)
                  ·
                    refine ⟨1632991716655198542774373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2177322288873598057032497 1632991716655198542774373)
                    ·
                      refine ⟨306185946872849726770195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1632991716655198542774373 306185946872849726770195)
                      ·
                        rfl

theorem cell23_596295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_596295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596295 prefixEnd_596295 := by exact prefixLift 596295
  have htrace : WordTrace (prefixWord ++ tailWord_596295) baseStart_596295 baseEnd_596295 := by
    simpa [prefixWord, tailWord_596295, baseEnd_596295] using wordTrace_append hprefix tailTrace_596295
  have hstable : (prefixWord ++ tailWord_596295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596295).length < 2 ^ (prefixWord ++ tailWord_596295).sum := by decide
  have hdescent : baseEnd_596295 < baseStart_596295 := by decide
  rcases family_descends (prefixWord ++ tailWord_596295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596305 : List Nat := [1, 2, 2, 1, 4, 4, 9]
def baseStart_596305 : Nat := 118140960795 + 596305 * 2 ^ 59
def prefixEnd_596305 : Nat := 4983230072969 + 3 ^ 40 * 596305 * 2
def baseEnd_596305 : Nat := 3780136810856724538829

theorem tailTrace_596305 : CollatzResearch.WordTrace tailWord_596305 prefixEnd_596305 3780136810856724538829 := by
  unfold tailWord_596305
  simp only [CollatzResearch.WordTrace]
  refine ⟨21749030104696300631150369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14499353403130867087433579 21749030104696300631150369)
  ·
    refine ⟨16311772578522225473362777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21749030104696300631150369 16311772578522225473362777)
    ·
      refine ⟨12233829433891669105022083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16311772578522225473362777 12233829433891669105022083)
      ·
        refine ⟨18350744150837503657533125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12233829433891669105022083 18350744150837503657533125)
        ·
          refine ⟨3440764528282031935787461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18350744150837503657533125 3440764528282031935787461)
          ·
            refine ⟨645143349052880987960149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3440764528282031935787461 645143349052880987960149)
            ·
              refine ⟨3780136810856724538829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 645143349052880987960149 3780136810856724538829)
              ·
                rfl

theorem cell23_596305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 9].length) (baseStart_596305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596305 prefixEnd_596305 := by exact prefixLift 596305
  have htrace : WordTrace (prefixWord ++ tailWord_596305) baseStart_596305 baseEnd_596305 := by
    simpa [prefixWord, tailWord_596305, baseEnd_596305] using wordTrace_append hprefix tailTrace_596305
  have hstable : (prefixWord ++ tailWord_596305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596305).length < 2 ^ (prefixWord ++ tailWord_596305).sum := by decide
  have hdescent : baseEnd_596305 < baseStart_596305 := by decide
  rcases family_descends (prefixWord ++ tailWord_596305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596322 : List Nat := [3, 3, 2, 1, 1, 3, 2, 8]
def baseStart_596322 : Nat := 118140960795 + 596322 * 2 ^ 59
def prefixEnd_596322 : Nat := 4983230072969 + 3 ^ 40 * 596322 * 2
def baseEnd_596322 : Nat := 11340733735204485967873

theorem tailTrace_596322 : CollatzResearch.WordTrace tailWord_596322 prefixEnd_596322 11340733735204485967873 := by
  unfold tailWord_596322
  simp only [CollatzResearch.WordTrace]
  refine ⟨5437412536408678133629805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14499766763756475023012813 5437412536408678133629805)
  ·
    refine ⟨2039029701153254300111177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5437412536408678133629805 2039029701153254300111177)
    ·
      refine ⟨1529272275864940725083383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2039029701153254300111177 1529272275864940725083383)
      ·
        refine ⟨2293908413797411087625075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1529272275864940725083383 2293908413797411087625075)
        ·
          refine ⟨3440862620696116631437613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2293908413797411087625075 3440862620696116631437613)
          ·
            refine ⟨1290323482761043736789105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3440862620696116631437613 1290323482761043736789105)
            ·
              refine ⟨967742612070782802591829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1290323482761043736789105 967742612070782802591829)
              ·
                refine ⟨11340733735204485967873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 967742612070782802591829 11340733735204485967873)
                ·
                  rfl

theorem cell23_596322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 8].length) (baseStart_596322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596322 prefixEnd_596322 := by exact prefixLift 596322
  have htrace : WordTrace (prefixWord ++ tailWord_596322) baseStart_596322 baseEnd_596322 := by
    simpa [prefixWord, tailWord_596322, baseEnd_596322] using wordTrace_append hprefix tailTrace_596322
  have hstable : (prefixWord ++ tailWord_596322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596322).length < 2 ^ (prefixWord ++ tailWord_596322).sum := by decide
  have hdescent : baseEnd_596322 < baseStart_596322 := by decide
  rcases family_descends (prefixWord ++ tailWord_596322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596366 : List Nat := [4, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3]
def baseStart_596366 : Nat := 118140960795 + 596366 * 2 ^ 59
def prefixEnd_596366 : Nat := 4983230072969 + 3 ^ 40 * 596366 * 2
def baseEnd_596366 : Nat := 306222403999318948982369

theorem tailTrace_596366 : CollatzResearch.WordTrace tailWord_596366 prefixEnd_596366 306222403999318948982369 := by
  unfold tailWord_596366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2718906869684413506140119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14500836638316872032747301 2718906869684413506140119)
  ·
    refine ⟨4078360304526620259210179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2718906869684413506140119 4078360304526620259210179)
    ·
      refine ⟨6117540456789930388815269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4078360304526620259210179 6117540456789930388815269)
      ·
        refine ⟨1147038835648111947902863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6117540456789930388815269 1147038835648111947902863)
        ·
          refine ⟨1720558253472167921854295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1147038835648111947902863 1720558253472167921854295)
          ·
            refine ⟨2580837380208251882781443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1720558253472167921854295 2580837380208251882781443)
            ·
              refine ⟨3871256070312377824172165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2580837380208251882781443 3871256070312377824172165)
              ·
                refine ⟨725860513183570842032281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3871256070312377824172165 725860513183570842032281)
                ·
                  refine ⟨544395384887678131524211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 725860513183570842032281 544395384887678131524211)
                  ·
                    refine ⟨816593077331517197286317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 544395384887678131524211 816593077331517197286317)
                    ·
                      refine ⟨306222403999318948982369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 816593077331517197286317 306222403999318948982369)
                      ·
                        rfl

theorem cell23_596366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_596366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596366 prefixEnd_596366 := by exact prefixLift 596366
  have htrace : WordTrace (prefixWord ++ tailWord_596366) baseStart_596366 baseEnd_596366 := by
    simpa [prefixWord, tailWord_596366, baseEnd_596366] using wordTrace_append hprefix tailTrace_596366
  have hstable : (prefixWord ++ tailWord_596366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596366).length < 2 ^ (prefixWord ++ tailWord_596366).sum := by decide
  have hdescent : baseEnd_596366 < baseStart_596366 := by decide
  rcases family_descends (prefixWord ++ tailWord_596366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596375 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 5]
def baseStart_596375 : Nat := 118140960795 + 596375 * 2 ^ 59
def prefixEnd_596375 : Nat := 4983230072969 + 3 ^ 40 * 596375 * 2
def baseEnd_596375 : Nat := 306227025325209413769827

theorem tailTrace_596375 : CollatzResearch.WordTrace tailWord_596375 prefixEnd_596375 306227025325209413769827 := by
  unfold tailWord_596375
  simp only [CollatzResearch.WordTrace]
  refine ⟨21751583214442702586198579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14501055476295135057465719 21751583214442702586198579)
  ·
    refine ⟨32627374821664053879297869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21751583214442702586198579 32627374821664053879297869)
    ·
      refine ⟨12235265558124020204736701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32627374821664053879297869 12235265558124020204736701)
      ·
        refine ⟨4588224584296507576776263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12235265558124020204736701 4588224584296507576776263)
        ·
          refine ⟨6882336876444761365164395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4588224584296507576776263 6882336876444761365164395)
          ·
            refine ⟨10323505314667142047746593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6882336876444761365164395 10323505314667142047746593)
            ·
              refine ⟨7742628986000356535809945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10323505314667142047746593 7742628986000356535809945)
              ·
                refine ⟨5806971739500267401857459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7742628986000356535809945 5806971739500267401857459)
                ·
                  refine ⟨8710457609250401102786189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5806971739500267401857459 8710457609250401102786189)
                  ·
                    refine ⟨3266421603468900413544821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8710457609250401102786189 3266421603468900413544821)
                    ·
                      refine ⟨306227025325209413769827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3266421603468900413544821 306227025325209413769827)
                      ·
                        rfl

theorem cell23_596375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_596375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596375 prefixEnd_596375 := by exact prefixLift 596375
  have htrace : WordTrace (prefixWord ++ tailWord_596375) baseStart_596375 baseEnd_596375 := by
    simpa [prefixWord, tailWord_596375, baseEnd_596375] using wordTrace_append hprefix tailTrace_596375
  have hstable : (prefixWord ++ tailWord_596375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596375).length < 2 ^ (prefixWord ++ tailWord_596375).sum := by decide
  have hdescent : baseEnd_596375 < baseStart_596375 := by decide
  rcases family_descends (prefixWord ++ tailWord_596375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596389 : List Nat := [1, 3, 1, 2, 1, 1, 6, 1, 1, 4, 2]
def baseStart_596389 : Nat := 118140960795 + 596389 * 2 ^ 59
def prefixEnd_596389 : Nat := 4983230072969 + 3 ^ 40 * 596389 * 2
def baseEnd_596389 : Nat := 306234214054372358994763

theorem tailTrace_596389 : CollatzResearch.WordTrace tailWord_596389 prefixEnd_596389 306234214054372358994763 := by
  unfold tailWord_596389
  simp only [CollatzResearch.WordTrace]
  refine ⟨21752093836391982977208221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14501395890927988651472147 21752093836391982977208221)
  ·
    refine ⟨8157035188646993616453083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21752093836391982977208221 8157035188646993616453083)
    ·
      refine ⟨12235552782970490424679625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8157035188646993616453083 12235552782970490424679625)
      ·
        refine ⟨9176664587227867818509719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12235552782970490424679625 9176664587227867818509719)
        ·
          refine ⟨13764996880841801727764579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9176664587227867818509719 13764996880841801727764579)
          ·
            refine ⟨20647495321262702591646869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13764996880841801727764579 20647495321262702591646869)
            ·
              refine ⟨967851343184189183983447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20647495321262702591646869 967851343184189183983447)
              ·
                refine ⟨1451777014776283775975171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 967851343184189183983447 1451777014776283775975171)
                ·
                  refine ⟨2177665522164425663962757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1451777014776283775975171 2177665522164425663962757)
                  ·
                    refine ⟨408312285405829811993017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2177665522164425663962757 408312285405829811993017)
                    ·
                      refine ⟨306234214054372358994763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 408312285405829811993017 306234214054372358994763)
                      ·
                        rfl

theorem cell23_596389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 4, 2].length) (baseStart_596389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596389 prefixEnd_596389 := by exact prefixLift 596389
  have htrace : WordTrace (prefixWord ++ tailWord_596389) baseStart_596389 baseEnd_596389 := by
    simpa [prefixWord, tailWord_596389, baseEnd_596389] using wordTrace_append hprefix tailTrace_596389
  have hstable : (prefixWord ++ tailWord_596389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596389).length < 2 ^ (prefixWord ++ tailWord_596389).sum := by decide
  have hdescent : baseEnd_596389 < baseStart_596389 := by decide
  rcases family_descends (prefixWord ++ tailWord_596389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596417 : List Nat := [1, 2, 7, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_596417 : Nat := 118140960795 + 596417 * 2 ^ 59
def prefixEnd_596417 : Nat := 4983230072969 + 3 ^ 40 * 596417 * 2
def baseEnd_596417 : Nat := 306248591512698249444635

theorem tailTrace_596417 : CollatzResearch.WordTrace tailWord_596417 prefixEnd_596417 306248591512698249444635 := by
  unfold tailWord_596417
  simp only [CollatzResearch.WordTrace]
  refine ⟨21753115080290543759227505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14502076720193695839485003 21753115080290543759227505)
  ·
    refine ⟨16314836310217907819420629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21753115080290543759227505 16314836310217907819420629)
    ·
      refine ⟨382378976020732214517671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 16314836310217907819420629 382378976020732214517671)
      ·
        refine ⟨573568464031098321776507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382378976020732214517671 573568464031098321776507)
        ·
          refine ⟨860352696046647482664761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 573568464031098321776507 860352696046647482664761)
          ·
            refine ⟨645264522034985611998571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 860352696046647482664761 645264522034985611998571)
            ·
              refine ⟨967896783052478417997857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 645264522034985611998571 967896783052478417997857)
              ·
                refine ⟨725922587289358813498393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 967896783052478417997857 725922587289358813498393)
                ·
                  refine ⟨544441940467019110123795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 725922587289358813498393 544441940467019110123795)
                  ·
                    refine ⟨816662910700528665185693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 544441940467019110123795 816662910700528665185693)
                    ·
                      refine ⟨306248591512698249444635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 816662910700528665185693 306248591512698249444635)
                      ·
                        rfl

theorem cell23_596417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_596417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596417 prefixEnd_596417 := by exact prefixLift 596417
  have htrace : WordTrace (prefixWord ++ tailWord_596417) baseStart_596417 baseEnd_596417 := by
    simpa [prefixWord, tailWord_596417, baseEnd_596417] using wordTrace_append hprefix tailTrace_596417
  have hstable : (prefixWord ++ tailWord_596417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596417).length < 2 ^ (prefixWord ++ tailWord_596417).sum := by decide
  have hdescent : baseEnd_596417 < baseStart_596417 := by decide
  rcases family_descends (prefixWord ++ tailWord_596417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596423 : List Nat := [1, 1, 4, 1, 1, 6, 1, 2, 2, 2, 2]
def baseStart_596423 : Nat := 118140960795 + 596423 * 2 ^ 59
def prefixEnd_596423 : Nat := 4983230072969 + 3 ^ 40 * 596423 * 2
def baseEnd_596423 : Nat := 306251672396625225969607

theorem tailTrace_596423 : CollatzResearch.WordTrace tailWord_596423 prefixEnd_596423 306251672396625225969607 := by
  unfold tailWord_596423
  simp only [CollatzResearch.WordTrace]
  refine ⟨21753333918268806783945923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14502222612179204522630615 21753333918268806783945923)
  ·
    refine ⟨32630000877403210175918885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21753333918268806783945923 32630000877403210175918885)
    ·
      refine ⟨6118125164513101907984791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32630000877403210175918885 6118125164513101907984791)
      ·
        refine ⟨9177187746769652861977187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6118125164513101907984791 9177187746769652861977187)
        ·
          refine ⟨13765781620154479292965781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9177187746769652861977187 13765781620154479292965781)
          ·
            refine ⟨645271013444741216857771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13765781620154479292965781 645271013444741216857771)
            ·
              refine ⟨967906520167111825286657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 645271013444741216857771 967906520167111825286657)
              ·
                refine ⟨725929890125333868964993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 967906520167111825286657 725929890125333868964993)
                ·
                  refine ⟨544447417594000401723745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 725929890125333868964993 544447417594000401723745)
                  ·
                    refine ⟨408335563195500301292809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 544447417594000401723745 408335563195500301292809)
                    ·
                      refine ⟨306251672396625225969607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 408335563195500301292809 306251672396625225969607)
                      ·
                        rfl

theorem cell23_596423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 2, 2].length) (baseStart_596423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596423 prefixEnd_596423 := by exact prefixLift 596423
  have htrace : WordTrace (prefixWord ++ tailWord_596423) baseStart_596423 baseEnd_596423 := by
    simpa [prefixWord, tailWord_596423, baseEnd_596423] using wordTrace_append hprefix tailTrace_596423
  have hstable : (prefixWord ++ tailWord_596423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596423).length < 2 ^ (prefixWord ++ tailWord_596423).sum := by decide
  have hdescent : baseEnd_596423 < baseStart_596423 := by decide
  rcases family_descends (prefixWord ++ tailWord_596423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596435 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 5]
def baseStart_596435 : Nat := 118140960795 + 596435 * 2 ^ 59
def prefixEnd_596435 : Nat := 4983230072969 + 3 ^ 40 * 596435 * 2
def baseEnd_596435 : Nat := 306257834164479179019551

theorem tailTrace_596435 : CollatzResearch.WordTrace tailWord_596435 prefixEnd_596435 306257834164479179019551 := by
  unfold tailWord_596435
  simp only [CollatzResearch.WordTrace]
  refine ⟨21753771594225332833382759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14502514396150221888921839 21753771594225332833382759)
  ·
    refine ⟨32630657391337999250074139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21753771594225332833382759 32630657391337999250074139)
    ·
      refine ⟨48945986087006998875111209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32630657391337999250074139 48945986087006998875111209)
      ·
        refine ⟨36709489565255249156333407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48945986087006998875111209 36709489565255249156333407)
        ·
          refine ⟨55064234347882873734500111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36709489565255249156333407 55064234347882873734500111)
          ·
            refine ⟨82596351521824310601750167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55064234347882873734500111 82596351521824310601750167)
            ·
              refine ⟨123894527282736465902625251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82596351521824310601750167 123894527282736465902625251)
              ·
                refine ⟨185841790924104698853937877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123894527282736465902625251 185841790924104698853937877)
                ·
                  refine ⟨4355666974783703879389169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 185841790924104698853937877 4355666974783703879389169)
                  ·
                    refine ⟨3266750231087777909541877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4355666974783703879389169 3266750231087777909541877)
                    ·
                      refine ⟨306257834164479179019551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3266750231087777909541877 306257834164479179019551)
                      ·
                        rfl

theorem cell23_596435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 5].length) (baseStart_596435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596435 prefixEnd_596435 := by exact prefixLift 596435
  have htrace : WordTrace (prefixWord ++ tailWord_596435) baseStart_596435 baseEnd_596435 := by
    simpa [prefixWord, tailWord_596435, baseEnd_596435] using wordTrace_append hprefix tailTrace_596435
  have hstable : (prefixWord ++ tailWord_596435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596435).length < 2 ^ (prefixWord ++ tailWord_596435).sum := by decide
  have hdescent : baseEnd_596435 < baseStart_596435 := by decide
  rcases family_descends (prefixWord ++ tailWord_596435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596539 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 8, 3, 2]
def baseStart_596539 : Nat := 118140960795 + 596539 * 2 ^ 59
def prefixEnd_596539 : Nat := 4983230072969 + 3 ^ 40 * 596539 * 2
def baseEnd_596539 : Nat := 306311236152546772119073

theorem tailTrace_596539 : CollatzResearch.WordTrace tailWord_596539 prefixEnd_596539 306311236152546772119073 := by
  unfold tailWord_596539
  simp only [CollatzResearch.WordTrace]
  refine ⟨21757564785848558595168671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14505043190565705730112447 21757564785848558595168671)
  ·
    refine ⟨32636347178772837892753007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21757564785848558595168671 32636347178772837892753007)
    ·
      refine ⟨48954520768159256839129511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32636347178772837892753007 48954520768159256839129511)
      ·
        refine ⟨73431781152238885258694267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48954520768159256839129511 73431781152238885258694267)
        ·
          refine ⟨110147671728358327888041401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73431781152238885258694267 110147671728358327888041401)
          ·
            refine ⟨82610753796268745916031051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110147671728358327888041401 82610753796268745916031051)
            ·
              refine ⟨123916130694403118874046577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82610753796268745916031051 123916130694403118874046577)
              ·
                refine ⟨92937098020802339155534933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123916130694403118874046577 92937098020802339155534933)
                ·
                  refine ⟨1089106617431277411978925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 92937098020802339155534933 1089106617431277411978925)
                  ·
                    refine ⟨408414981536729029492097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1089106617431277411978925 408414981536729029492097)
                    ·
                      refine ⟨306311236152546772119073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 408414981536729029492097 306311236152546772119073)
                      ·
                        rfl

theorem cell23_596539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 3, 2].length) (baseStart_596539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596539 prefixEnd_596539 := by exact prefixLift 596539
  have htrace : WordTrace (prefixWord ++ tailWord_596539) baseStart_596539 baseEnd_596539 := by
    simpa [prefixWord, tailWord_596539, baseEnd_596539] using wordTrace_append hprefix tailTrace_596539
  have hstable : (prefixWord ++ tailWord_596539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596539).length < 2 ^ (prefixWord ++ tailWord_596539).sum := by decide
  have hdescent : baseEnd_596539 < baseStart_596539 := by decide
  rcases family_descends (prefixWord ++ tailWord_596539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596540 : List Nat := [2, 2, 2, 2, 3, 3, 2, 2, 1, 4]
def baseStart_596540 : Nat := 118140960795 + 596540 * 2 ^ 59
def prefixEnd_596540 : Nat := 4983230072969 + 3 ^ 40 * 596540 * 2
def baseEnd_596540 : Nat := 102103916544400422735523

theorem tailTrace_596540 : CollatzResearch.WordTrace tailWord_596540 prefixEnd_596540 102103916544400422735523 := by
  unfold tailWord_596540
  simp only [CollatzResearch.WordTrace]
  refine ⟨10878800629422467882977537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14505067505896623843970049 10878800629422467882977537)
  ·
    refine ⟨8159100472066850912233153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10878800629422467882977537 8159100472066850912233153)
    ·
      refine ⟨6119325354050138184174865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8159100472066850912233153 6119325354050138184174865)
      ·
        refine ⟨4589494015537603638131149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6119325354050138184174865 4589494015537603638131149)
        ·
          refine ⟨1721060255826601364299181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4589494015537603638131149 1721060255826601364299181)
          ·
            refine ⟨645397595934975511612193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1721060255826601364299181 645397595934975511612193)
            ·
              refine ⟨484048196951231633709145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 645397595934975511612193 484048196951231633709145)
              ·
                refine ⟨363036147713423725281859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 484048196951231633709145 363036147713423725281859)
                ·
                  refine ⟨544554221570135587922789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 363036147713423725281859 544554221570135587922789)
                  ·
                    refine ⟨102103916544400422735523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 544554221570135587922789 102103916544400422735523)
                    ·
                      rfl

theorem cell23_596540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_596540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596540 prefixEnd_596540 := by exact prefixLift 596540
  have htrace : WordTrace (prefixWord ++ tailWord_596540) baseStart_596540 baseEnd_596540 := by
    simpa [prefixWord, tailWord_596540, baseEnd_596540] using wordTrace_append hprefix tailTrace_596540
  have hstable : (prefixWord ++ tailWord_596540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596540).length < 2 ^ (prefixWord ++ tailWord_596540).sum := by decide
  have hdescent : baseEnd_596540 < baseStart_596540 := by decide
  rcases family_descends (prefixWord ++ tailWord_596540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596574 : List Nat := [4, 4, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_596574 : Nat := 118140960795 + 596574 * 2 ^ 59
def prefixEnd_596574 : Nat := 4983230072969 + 3 ^ 40 * 596574 * 2
def baseEnd_596574 : Nat := 102109735991818045060471

theorem tailTrace_596574 : CollatzResearch.WordTrace tailWord_596574 prefixEnd_596574 102109735991818045060471 := by
  unfold tailWord_596574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2719855167590219946586597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14505894227147839715128517 2719855167590219946586597)
  ·
    refine ⟨509972843923166239984987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2719855167590219946586597 509972843923166239984987)
    ·
      refine ⟨764959265884749359977481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 509972843923166239984987 764959265884749359977481)
      ·
        refine ⟨573719449413562019983111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 764959265884749359977481 573719449413562019983111)
        ·
          refine ⟨860579174120343029974667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 573719449413562019983111 860579174120343029974667)
          ·
            refine ⟨1290868761180514544962001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 860579174120343029974667 1290868761180514544962001)
            ·
              refine ⟨968151570885385908721501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1290868761180514544962001 968151570885385908721501)
              ·
                refine ⟨363056839082019715770563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 968151570885385908721501 363056839082019715770563)
                ·
                  refine ⟨544585258623029573655845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 363056839082019715770563 544585258623029573655845)
                  ·
                    refine ⟨102109735991818045060471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 544585258623029573655845 102109735991818045060471)
                    ·
                      rfl

theorem cell23_596574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_596574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596574 prefixEnd_596574 := by exact prefixLift 596574
  have htrace : WordTrace (prefixWord ++ tailWord_596574) baseStart_596574 baseEnd_596574 := by
    simpa [prefixWord, tailWord_596574, baseEnd_596574] using wordTrace_append hprefix tailTrace_596574
  have hstable : (prefixWord ++ tailWord_596574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596574).length < 2 ^ (prefixWord ++ tailWord_596574).sum := by decide
  have hdescent : baseEnd_596574 < baseStart_596574 := by decide
  rcases family_descends (prefixWord ++ tailWord_596574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596579 : List Nat := [1, 1, 1, 5, 1, 2, 2, 2, 4, 4]
def baseStart_596579 : Nat := 118140960795 + 596579 * 2 ^ 59
def prefixEnd_596579 : Nat := 4983230072969 + 3 ^ 40 * 596579 * 2
def baseEnd_596579 : Nat := 102110591792908871872963

theorem tailTrace_596579 : CollatzResearch.WordTrace tailWord_596579 prefixEnd_596579 102110591792908871872963 := by
  unfold tailWord_596579
  simp only [CollatzResearch.WordTrace]
  refine ⟨21759023705703645426624791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14506015803802430284416527 21759023705703645426624791)
  ·
    refine ⟨32638535558555468139937187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21759023705703645426624791 32638535558555468139937187)
    ·
      refine ⟨48957803337833202209905781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32638535558555468139937187 48957803337833202209905781)
      ·
        refine ⟨4589794062921862707178667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48957803337833202209905781 4589794062921862707178667)
        ·
          refine ⟨6884691094382794060768001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4589794062921862707178667 6884691094382794060768001)
          ·
            refine ⟨5163518320787095545576001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6884691094382794060768001 5163518320787095545576001)
            ·
              refine ⟨3872638740590321659182001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5163518320787095545576001 3872638740590321659182001)
              ·
                refine ⟨2904479055442741244386501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3872638740590321659182001 2904479055442741244386501)
                ·
                  refine ⟨544589822895513983322469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2904479055442741244386501 544589822895513983322469)
                  ·
                    refine ⟨102110591792908871872963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 544589822895513983322469 102110591792908871872963)
                    ·
                      rfl

theorem cell23_596579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 4].length) (baseStart_596579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596579 prefixEnd_596579 := by exact prefixLift 596579
  have htrace : WordTrace (prefixWord ++ tailWord_596579) baseStart_596579 baseEnd_596579 := by
    simpa [prefixWord, tailWord_596579, baseEnd_596579] using wordTrace_append hprefix tailTrace_596579
  have hstable : (prefixWord ++ tailWord_596579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596579).length < 2 ^ (prefixWord ++ tailWord_596579).sum := by decide
  have hdescent : baseEnd_596579 < baseStart_596579 := by decide
  rcases family_descends (prefixWord ++ tailWord_596579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596586 : List Nat := [3, 1, 3, 2, 1, 1, 3, 3, 1, 1, 4]
def baseStart_596586 : Nat := 118140960795 + 596586 * 2 ^ 59
def prefixEnd_596586 : Nat := 4983230072969 + 3 ^ 40 * 596586 * 2
def baseEnd_596586 : Nat := 306335369743308088231357

theorem tailTrace_596586 : CollatzResearch.WordTrace tailWord_596586 prefixEnd_596586 306335369743308088231357 := by
  unfold tailWord_596586
  simp only [CollatzResearch.WordTrace]
  refine ⟨5439819754169571405532403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14506186011118857081419741 5439819754169571405532403)
  ·
    refine ⟨8159729631254357108298605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5439819754169571405532403 8159729631254357108298605)
    ·
      refine ⟨3059898611720383915611977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8159729631254357108298605 3059898611720383915611977)
      ·
        refine ⟨2294923958790287936708983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3059898611720383915611977 2294923958790287936708983)
        ·
          refine ⟨3442385938185431905063475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2294923958790287936708983 3442385938185431905063475)
          ·
            refine ⟨5163578907278147857595213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3442385938185431905063475 5163578907278147857595213)
            ·
              refine ⟨1936342090229305446598205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5163578907278147857595213 1936342090229305446598205)
              ·
                refine ⟨726128283835989542474327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1936342090229305446598205 726128283835989542474327)
                ·
                  refine ⟨1089192425753984313711491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 726128283835989542474327 1089192425753984313711491)
                  ·
                    refine ⟨1633788638630976470567237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1089192425753984313711491 1633788638630976470567237)
                    ·
                      refine ⟨306335369743308088231357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1633788638630976470567237 306335369743308088231357)
                      ·
                        rfl

theorem cell23_596586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_596586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596586 prefixEnd_596586 := by exact prefixLift 596586
  have htrace : WordTrace (prefixWord ++ tailWord_596586) baseStart_596586 baseEnd_596586 := by
    simpa [prefixWord, tailWord_596586, baseEnd_596586] using wordTrace_append hprefix tailTrace_596586
  have hstable : (prefixWord ++ tailWord_596586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596586).length < 2 ^ (prefixWord ++ tailWord_596586).sum := by decide
  have hdescent : baseEnd_596586 < baseStart_596586 := by decide
  rcases family_descends (prefixWord ++ tailWord_596586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596613 : List Nat := [1, 3, 1, 1, 4, 3, 3, 1, 2, 4]
def baseStart_596613 : Nat := 118140960795 + 596613 * 2 ^ 59
def prefixEnd_596613 : Nat := 4983230072969 + 3 ^ 40 * 596613 * 2
def baseEnd_596613 : Nat := 102116411240326494197911

theorem tailTrace_596613 : CollatzResearch.WordTrace tailWord_596613 prefixEnd_596613 102116411240326494197911 := by
  unfold tailWord_596613
  simp only [CollatzResearch.WordTrace]
  refine ⟨21760263787580469233362493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14506842525053646155574995 21760263787580469233362493)
  ·
    refine ⟨8160098920342675962510935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21760263787580469233362493 8160098920342675962510935)
    ·
      refine ⟨12240148380514013943766403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8160098920342675962510935 12240148380514013943766403)
      ·
        refine ⟨18360222570771020915649605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12240148380514013943766403 18360222570771020915649605)
        ·
          refine ⟨3442541732019566421684301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18360222570771020915649605 3442541732019566421684301)
          ·
            refine ⟨1290953149507337408131613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3442541732019566421684301 1290953149507337408131613)
            ·
              refine ⟨484107431065251528049355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1290953149507337408131613 484107431065251528049355)
              ·
                refine ⟨726161146597877292074033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 484107431065251528049355 726161146597877292074033)
                ·
                  refine ⟨544620859948407969055525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 726161146597877292074033 544620859948407969055525)
                  ·
                    refine ⟨102116411240326494197911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 544620859948407969055525 102116411240326494197911)
                    ·
                      rfl

theorem cell23_596613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 2, 4].length) (baseStart_596613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596613 prefixEnd_596613 := by exact prefixLift 596613
  have htrace : WordTrace (prefixWord ++ tailWord_596613) baseStart_596613 baseEnd_596613 := by
    simpa [prefixWord, tailWord_596613, baseEnd_596613] using wordTrace_append hprefix tailTrace_596613
  have hstable : (prefixWord ++ tailWord_596613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596613).length < 2 ^ (prefixWord ++ tailWord_596613).sum := by decide
  have hdescent : baseEnd_596613 < baseStart_596613 := by decide
  rcases family_descends (prefixWord ++ tailWord_596613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596619 : List Nat := [1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 3]
def baseStart_596619 : Nat := 118140960795 + 596619 * 2 ^ 59
def prefixEnd_596619 : Nat := 4983230072969 + 3 ^ 40 * 596619 * 2
def baseEnd_596619 : Nat := 306352314604906459118705

theorem tailTrace_596619 : CollatzResearch.WordTrace tailWord_596619 prefixEnd_596619 306352314604906459118705 := by
  unfold tailWord_596619
  simp only [CollatzResearch.WordTrace]
  refine ⟨21760482625558732258080911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14506988417039154838720607 21760482625558732258080911)
  ·
    refine ⟨32640723938338098387121367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21760482625558732258080911 32640723938338098387121367)
    ·
      refine ⟨48961085907507147580682051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32640723938338098387121367 48961085907507147580682051)
      ·
        refine ⟨73441628861260721371023077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48961085907507147580682051 73441628861260721371023077)
        ·
          refine ⟨13770305411486385257066827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73441628861260721371023077 13770305411486385257066827)
          ·
            refine ⟨20655458117229577885600241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13770305411486385257066827 20655458117229577885600241)
            ·
              refine ⟨15491593587922183414200181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20655458117229577885600241 15491593587922183414200181)
              ·
                refine ⟨1452336898867704695081267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15491593587922183414200181 1452336898867704695081267)
                ·
                  refine ⟨2178505348301557042621901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1452336898867704695081267 2178505348301557042621901)
                  ·
                    refine ⟨816939505613083890983213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2178505348301557042621901 816939505613083890983213)
                    ·
                      refine ⟨306352314604906459118705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 816939505613083890983213 306352314604906459118705)
                      ·
                        rfl

theorem cell23_596619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 3].length) (baseStart_596619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596619 prefixEnd_596619 := by exact prefixLift 596619
  have htrace : WordTrace (prefixWord ++ tailWord_596619) baseStart_596619 baseEnd_596619 := by
    simpa [prefixWord, tailWord_596619, baseEnd_596619] using wordTrace_append hprefix tailTrace_596619
  have hstable : (prefixWord ++ tailWord_596619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596619).length < 2 ^ (prefixWord ++ tailWord_596619).sum := by decide
  have hdescent : baseEnd_596619 < baseStart_596619 := by decide
  rcases family_descends (prefixWord ++ tailWord_596619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596626 : List Nat := [3, 2, 3, 1, 2, 1, 4, 7]
def baseStart_596626 : Nat := 118140960795 + 596626 * 2 ^ 59
def prefixEnd_596626 : Nat := 4983230072969 + 3 ^ 40 * 596626 * 2
def baseEnd_596626 : Nat := 11346515147018071545599

theorem tailTrace_596626 : CollatzResearch.WordTrace tailWord_596626 prefixEnd_596626 11346515147018071545599 := by
  unfold tailWord_596626
  simp only [CollatzResearch.WordTrace]
  refine ⟨5440184484133343113396433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14507158624355581635723821 5440184484133343113396433)
  ·
    refine ⟨4080138363100007335047325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5440184484133343113396433 4080138363100007335047325)
    ·
      refine ⟨1530051886162502750642747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4080138363100007335047325 1530051886162502750642747)
      ·
        refine ⟨2295077829243754125964121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1530051886162502750642747 2295077829243754125964121)
        ·
          refine ⟨1721308371932815594473091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2295077829243754125964121 1721308371932815594473091)
          ·
            refine ⟨2581962557899223391709637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1721308371932815594473091 2581962557899223391709637)
            ·
              refine ⟨484117979606104385945557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2581962557899223391709637 484117979606104385945557)
              ·
                refine ⟨11346515147018071545599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 484117979606104385945557 11346515147018071545599)
                ·
                  rfl

theorem cell23_596626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 7].length) (baseStart_596626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596626 prefixEnd_596626 := by exact prefixLift 596626
  have htrace : WordTrace (prefixWord ++ tailWord_596626) baseStart_596626 baseEnd_596626 := by
    simpa [prefixWord, tailWord_596626, baseEnd_596626] using wordTrace_append hprefix tailTrace_596626
  have hstable : (prefixWord ++ tailWord_596626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596626).length < 2 ^ (prefixWord ++ tailWord_596626).sum := by decide
  have hdescent : baseEnd_596626 < baseStart_596626 := by decide
  rcases family_descends (prefixWord ++ tailWord_596626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596653 : List Nat := [1, 5, 2, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_596653 : Nat := 118140960795 + 596653 * 2 ^ 59
def prefixEnd_596653 : Nat := 4983230072969 + 3 ^ 40 * 596653 * 2
def baseEnd_596653 : Nat := 306369772947159326093549

theorem tailTrace_596653 : CollatzResearch.WordTrace tailWord_596653 prefixEnd_596653 306369772947159326093549 := by
  unfold tailWord_596653
  simp only [CollatzResearch.WordTrace]
  refine ⟨21761722707435556064818613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14507815138290370709879075 21761722707435556064818613)
  ·
    refine ⟨2040161503822083381076745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21761722707435556064818613 2040161503822083381076745)
    ·
      refine ⟨1530121127866562535807559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2040161503822083381076745 1530121127866562535807559)
      ·
        refine ⟨2295181691799843803711339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1530121127866562535807559 2295181691799843803711339)
        ·
          refine ⟨3442772537699765705567009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2295181691799843803711339 3442772537699765705567009)
          ·
            refine ⟨2582079403274824279175257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3442772537699765705567009 2582079403274824279175257)
            ·
              refine ⟨1936559552456118209381443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2582079403274824279175257 1936559552456118209381443)
              ·
                refine ⟨2904839328684177314072165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1936559552456118209381443 2904839328684177314072165)
                ·
                  refine ⟨544657374128283246388531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2904839328684177314072165 544657374128283246388531)
                  ·
                    refine ⟨816986061192424869582797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 544657374128283246388531 816986061192424869582797)
                    ·
                      refine ⟨306369772947159326093549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 816986061192424869582797 306369772947159326093549)
                      ·
                        rfl

theorem cell23_596653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_596653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596653 prefixEnd_596653 := by exact prefixLift 596653
  have htrace : WordTrace (prefixWord ++ tailWord_596653) baseStart_596653 baseEnd_596653 := by
    simpa [prefixWord, tailWord_596653, baseEnd_596653] using wordTrace_append hprefix tailTrace_596653
  have hstable : (prefixWord ++ tailWord_596653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596653).length < 2 ^ (prefixWord ++ tailWord_596653).sum := by decide
  have hdescent : baseEnd_596653 < baseStart_596653 := by decide
  rcases family_descends (prefixWord ++ tailWord_596653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596679 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 3]
def baseStart_596679 : Nat := 118140960795 + 596679 * 2 ^ 59
def prefixEnd_596679 : Nat := 4983230072969 + 3 ^ 40 * 596679 * 2
def baseEnd_596679 : Nat := 306383123444176224368429

theorem tailTrace_596679 : CollatzResearch.WordTrace tailWord_596679 prefixEnd_596679 306383123444176224368429 := by
  unfold tailWord_596679
  simp only [CollatzResearch.WordTrace]
  refine ⟨21762671005341362505265091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14508447336894241670176727 21762671005341362505265091)
  ·
    refine ⟨32644006508012043757897637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21762671005341362505265091 32644006508012043757897637)
    ·
      refine ⟨6120751220252258204605807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32644006508012043757897637 6120751220252258204605807)
      ·
        refine ⟨9181126830378387306908711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6120751220252258204605807 9181126830378387306908711)
        ·
          refine ⟨13771690245567580960363067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9181126830378387306908711 13771690245567580960363067)
          ·
            refine ⟨20657535368351371440544601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13771690245567580960363067 20657535368351371440544601)
            ·
              refine ⟨15493151526263528580408451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20657535368351371440544601 15493151526263528580408451)
              ·
                refine ⟨23239727289395292870612677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15493151526263528580408451 23239727289395292870612677)
                ·
                  refine ⟨4357448866761617413239877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23239727289395292870612677 4357448866761617413239877)
                  ·
                    refine ⟨817021662517803264982477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4357448866761617413239877 817021662517803264982477)
                    ·
                      refine ⟨306383123444176224368429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 817021662517803264982477 306383123444176224368429)
                      ·
                        rfl

theorem cell23_596679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_596679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596679 prefixEnd_596679 := by exact prefixLift 596679
  have htrace : WordTrace (prefixWord ++ tailWord_596679) baseStart_596679 baseEnd_596679 := by
    simpa [prefixWord, tailWord_596679, baseEnd_596679] using wordTrace_append hprefix tailTrace_596679
  have hstable : (prefixWord ++ tailWord_596679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596679).length < 2 ^ (prefixWord ++ tailWord_596679).sum := by decide
  have hdescent : baseEnd_596679 < baseStart_596679 := by decide
  rcases family_descends (prefixWord ++ tailWord_596679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596680 : List Nat := [2, 1, 3, 1, 2, 5, 1, 2, 1, 3, 2]
def baseStart_596680 : Nat := 118140960795 + 596680 * 2 ^ 59
def prefixEnd_596680 : Nat := 4983230072969 + 3 ^ 40 * 596680 * 2
def baseEnd_596680 : Nat := 306383636924830720455925

theorem tailTrace_596680 : CollatzResearch.WordTrace tailWord_596680 prefixEnd_596680 306383636924830720455925 := by
  unfold tailWord_596680
  simp only [CollatzResearch.WordTrace]
  refine ⟨10881353739168869838025747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14508471652225159784034329 10881353739168869838025747)
  ·
    refine ⟨16322030608753304757038621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10881353739168869838025747 16322030608753304757038621)
    ·
      refine ⟨6120761478282489283889483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16322030608753304757038621 6120761478282489283889483)
      ·
        refine ⟨9181142217423733925834225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6120761478282489283889483 9181142217423733925834225)
        ·
          refine ⟨6885856663067800444375669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9181142217423733925834225 6885856663067800444375669)
          ·
            refine ⟨645549062162606291660219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6885856663067800444375669 645549062162606291660219)
            ·
              refine ⟨968323593243909437490329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 645549062162606291660219 968323593243909437490329)
              ·
                refine ⟨726242694932932078117747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 968323593243909437490329 726242694932932078117747)
                ·
                  refine ⟨1089364042399398117176621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 726242694932932078117747 1089364042399398117176621)
                  ·
                    refine ⟨408511515899774293941233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1089364042399398117176621 408511515899774293941233)
                    ·
                      refine ⟨306383636924830720455925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 408511515899774293941233 306383636924830720455925)
                      ·
                        rfl

theorem cell23_596680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 1, 3, 2].length) (baseStart_596680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596680 prefixEnd_596680 := by exact prefixLift 596680
  have htrace : WordTrace (prefixWord ++ tailWord_596680) baseStart_596680 baseEnd_596680 := by
    simpa [prefixWord, tailWord_596680, baseEnd_596680] using wordTrace_append hprefix tailTrace_596680
  have hstable : (prefixWord ++ tailWord_596680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596680).length < 2 ^ (prefixWord ++ tailWord_596680).sum := by decide
  have hdescent : baseEnd_596680 < baseStart_596680 := by decide
  rcases family_descends (prefixWord ++ tailWord_596680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596729 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 4, 5]
def baseStart_596729 : Nat := 118140960795 + 596729 * 2 ^ 59
def prefixEnd_596729 : Nat := 4983230072969 + 3 ^ 40 * 596729 * 2
def baseEnd_596729 : Nat := 102136265825633676247733

theorem tailTrace_596729 : CollatzResearch.WordTrace tailWord_596729 prefixEnd_596729 102136265825633676247733 := by
  unfold tailWord_596729
  simp only [CollatzResearch.WordTrace]
  refine ⟨21764494655160221044585241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14509663103440147363056827 21764494655160221044585241)
  ·
    refine ⟨16323370991370165783438931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21764494655160221044585241 16323370991370165783438931)
    ·
      refine ⟨24485056487055248675158397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16323370991370165783438931 24485056487055248675158397)
      ·
        refine ⟨9181896182645718253184399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24485056487055248675158397 9181896182645718253184399)
        ·
          refine ⟨13772844273968577379776599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9181896182645718253184399 13772844273968577379776599)
          ·
            refine ⟨20659266410952866069664899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13772844273968577379776599 20659266410952866069664899)
            ·
              refine ⟨30988899616429299104497349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20659266410952866069664899 30988899616429299104497349)
              ·
                refine ⟨5810418678080493582093253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30988899616429299104497349 5810418678080493582093253)
                ·
                  refine ⟨1089453502140092546642485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5810418678080493582093253 1089453502140092546642485)
                  ·
                    refine ⟨102136265825633676247733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1089453502140092546642485 102136265825633676247733)
                    ·
                      rfl

theorem cell23_596729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 5].length) (baseStart_596729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596729 prefixEnd_596729 := by exact prefixLift 596729
  have htrace : WordTrace (prefixWord ++ tailWord_596729) baseStart_596729 baseEnd_596729 := by
    simpa [prefixWord, tailWord_596729, baseEnd_596729] using wordTrace_append hprefix tailTrace_596729
  have hstable : (prefixWord ++ tailWord_596729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596729).length < 2 ^ (prefixWord ++ tailWord_596729).sum := by decide
  have hdescent : baseEnd_596729 < baseStart_596729 := by decide
  rcases family_descends (prefixWord ++ tailWord_596729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596779 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 4]
def baseStart_596779 : Nat := 118140960795 + 596779 * 2 ^ 59
def prefixEnd_596779 : Nat := 4983230072969 + 3 ^ 40 * 596779 * 2
def baseEnd_596779 : Nat := 306434471509625833117969

theorem tailTrace_596779 : CollatzResearch.WordTrace tailWord_596779 prefixEnd_596779 306434471509625833117969 := by
  unfold tailWord_596779
  simp only [CollatzResearch.WordTrace]
  refine ⟨21766318304979079583905391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14510878869986053055936927 21766318304979079583905391)
  ·
    refine ⟨32649477457468619375858087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21766318304979079583905391 32649477457468619375858087)
    ·
      refine ⟨48974216186202929063787131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32649477457468619375858087 48974216186202929063787131)
      ·
        refine ⟨73461324279304393595680697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48974216186202929063787131 73461324279304393595680697)
        ·
          refine ⟨55095993209478295196760523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73461324279304393595680697 55095993209478295196760523)
          ·
            refine ⟨82643989814217442795140785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55095993209478295196760523 82643989814217442795140785)
            ·
              refine ⟨61982992360663082096355589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82643989814217442795140785 61982992360663082096355589)
              ·
                refine ⟨11621811067624327893066673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61982992360663082096355589 11621811067624327893066673)
                ·
                  refine ⟨8716358300718245919800005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11621811067624327893066673 8716358300718245919800005)
                  ·
                    refine ⟨1634317181384671109962501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8716358300718245919800005 1634317181384671109962501)
                    ·
                      refine ⟨306434471509625833117969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1634317181384671109962501 306434471509625833117969)
                      ·
                        rfl

theorem cell23_596779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 4].length) (baseStart_596779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596779 prefixEnd_596779 := by exact prefixLift 596779
  have htrace : WordTrace (prefixWord ++ tailWord_596779) baseStart_596779 baseEnd_596779 := by
    simpa [prefixWord, tailWord_596779, baseEnd_596779] using wordTrace_append hprefix tailTrace_596779
  have hstable : (prefixWord ++ tailWord_596779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596779).length < 2 ^ (prefixWord ++ tailWord_596779).sum := by decide
  have hdescent : baseEnd_596779 < baseStart_596779 := by decide
  rcases family_descends (prefixWord ++ tailWord_596779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596786 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3]
def baseStart_596786 : Nat := 118140960795 + 596786 * 2 ^ 59
def prefixEnd_596786 : Nat := 4983230072969 + 3 ^ 40 * 596786 * 2
def baseEnd_596786 : Nat := 306438065874207305730437

theorem tailTrace_596786 : CollatzResearch.WordTrace tailWord_596786 prefixEnd_596786 306438065874207305730437 := by
  unfold tailWord_596786
  simp only [CollatzResearch.WordTrace]
  refine ⟨5441643403988429944852553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14511049077302479852940141 5441643403988429944852553)
  ·
    refine ⟨4081232552991322458639415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5441643403988429944852553 4081232552991322458639415)
    ·
      refine ⟨6121848829486983687959123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4081232552991322458639415 6121848829486983687959123)
      ·
        refine ⟨9182773244230475531938685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6121848829486983687959123 9182773244230475531938685)
        ·
          refine ⟨3443539966586428324477007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9182773244230475531938685 3443539966586428324477007)
          ·
            refine ⟨5165309949879642486715511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3443539966586428324477007 5165309949879642486715511)
            ·
              refine ⟨7747964924819463730073267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5165309949879642486715511 7747964924819463730073267)
              ·
                refine ⟨11621947387229195595109901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7747964924819463730073267 11621947387229195595109901)
                ·
                  refine ⟨4358230270210948348166213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11621947387229195595109901 4358230270210948348166213)
                  ·
                    refine ⟨817168175664552815281165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4358230270210948348166213 817168175664552815281165)
                    ·
                      refine ⟨306438065874207305730437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 817168175664552815281165 306438065874207305730437)
                      ·
                        rfl

theorem cell23_596786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_596786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596786 prefixEnd_596786 := by exact prefixLift 596786
  have htrace : WordTrace (prefixWord ++ tailWord_596786) baseStart_596786 baseEnd_596786 := by
    simpa [prefixWord, tailWord_596786, baseEnd_596786] using wordTrace_append hprefix tailTrace_596786
  have hstable : (prefixWord ++ tailWord_596786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596786).length < 2 ^ (prefixWord ++ tailWord_596786).sum := by decide
  have hdescent : baseEnd_596786 < baseStart_596786 := by decide
  rcases family_descends (prefixWord ++ tailWord_596786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596820 : List Nat := [2, 4, 1, 1, 4, 1, 1, 2, 2, 2, 3]
def baseStart_596820 : Nat := 118140960795 + 596820 * 2 ^ 59
def prefixEnd_596820 : Nat := 4983230072969 + 3 ^ 40 * 596820 * 2
def baseEnd_596820 : Nat := 306455524216460172705281

theorem tailTrace_596820 : CollatzResearch.WordTrace tailWord_596820 prefixEnd_596820 306455524216460172705281 := by
  unfold tailWord_596820
  simp only [CollatzResearch.WordTrace]
  refine ⟨10883906848915271793073957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14511875798553695724098609 10883906848915271793073957)
  ·
    refine ⟨2040732534171613461201367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10883906848915271793073957 2040732534171613461201367)
    ·
      refine ⟨3061098801257420191802051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2040732534171613461201367 3061098801257420191802051)
      ·
        refine ⟨4591648201886130287703077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3061098801257420191802051 4591648201886130287703077)
        ·
          refine ⟨860934037853649428944327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4591648201886130287703077 860934037853649428944327)
          ·
            refine ⟨1291401056780474143416491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 860934037853649428944327 1291401056780474143416491)
            ·
              refine ⟨1937101585170711215124737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1291401056780474143416491 1937101585170711215124737)
              ·
                refine ⟨1452826188878033411343553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1937101585170711215124737 1452826188878033411343553)
                ·
                  refine ⟨1089619641658525058507665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1452826188878033411343553 1089619641658525058507665)
                  ·
                    refine ⟨817214731243893793880749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1089619641658525058507665 817214731243893793880749)
                    ·
                      refine ⟨306455524216460172705281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 817214731243893793880749 306455524216460172705281)
                      ·
                        rfl

theorem cell23_596820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_596820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596820 prefixEnd_596820 := by exact prefixLift 596820
  have htrace : WordTrace (prefixWord ++ tailWord_596820) baseStart_596820 baseEnd_596820 := by
    simpa [prefixWord, tailWord_596820, baseEnd_596820] using wordTrace_append hprefix tailTrace_596820
  have hstable : (prefixWord ++ tailWord_596820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596820).length < 2 ^ (prefixWord ++ tailWord_596820).sum := by decide
  have hdescent : baseEnd_596820 < baseStart_596820 := by decide
  rcases family_descends (prefixWord ++ tailWord_596820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596833 : List Nat := [1, 2, 3, 1, 1, 1, 2, 5, 3, 1, 3]
def baseStart_596833 : Nat := 118140960795 + 596833 * 2 ^ 59
def prefixEnd_596833 : Nat := 4983230072969 + 3 ^ 40 * 596833 * 2
def baseEnd_596833 : Nat := 306462199464968621842721

theorem tailTrace_596833 : CollatzResearch.WordTrace tailWord_596833 prefixEnd_596833 306462199464968621842721 := by
  unfold tailWord_596833
  simp only [CollatzResearch.WordTrace]
  refine ⟨21768287846783446806371153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14512191897855631204247435 21768287846783446806371153)
  ·
    refine ⟨16326215885087585104778365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21768287846783446806371153 16326215885087585104778365)
    ·
      refine ⟨6122330956907844414291887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16326215885087585104778365 6122330956907844414291887)
      ·
        refine ⟨9183496435361766621437831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6122330956907844414291887 9183496435361766621437831)
        ·
          refine ⟨13775244653042649932156747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9183496435361766621437831 13775244653042649932156747)
          ·
            refine ⟨20662866979563974898235121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13775244653042649932156747 20662866979563974898235121)
            ·
              refine ⟨15497150234672981173676341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20662866979563974898235121 15497150234672981173676341)
              ·
                refine ⟨1452857834500591985032157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15497150234672981173676341 1452857834500591985032157)
                ·
                  refine ⟨544821687937721994387059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1452857834500591985032157 544821687937721994387059)
                  ·
                    refine ⟨817232531906582991580589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 544821687937721994387059 817232531906582991580589)
                    ·
                      refine ⟨306462199464968621842721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 817232531906582991580589 306462199464968621842721)
                      ·
                        rfl

theorem cell23_596833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_596833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596833 prefixEnd_596833 := by exact prefixLift 596833
  have htrace : WordTrace (prefixWord ++ tailWord_596833) baseStart_596833 baseEnd_596833 := by
    simpa [prefixWord, tailWord_596833, baseEnd_596833] using wordTrace_append hprefix tailTrace_596833
  have hstable : (prefixWord ++ tailWord_596833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596833).length < 2 ^ (prefixWord ++ tailWord_596833).sum := by decide
  have hdescent : baseEnd_596833 < baseStart_596833 := by decide
  rcases family_descends (prefixWord ++ tailWord_596833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596840 : List Nat := [2, 1, 4, 2, 1, 4, 2, 1, 6]
def baseStart_596840 : Nat := 118140960795 + 596840 * 2 ^ 59
def prefixEnd_596840 : Nat := 4983230072969 + 3 ^ 40 * 596840 * 2
def baseEnd_596840 : Nat := 34051754869950010495021

theorem tailTrace_596840 : CollatzResearch.WordTrace tailWord_596840 prefixEnd_596840 34051754869950010495021 := by
  unfold tailWord_596840
  simp only [CollatzResearch.WordTrace]
  refine ⟨10884271578879043500937987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14512362105172058001250649 10884271578879043500937987)
  ·
    refine ⟨16326407368318565251406981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10884271578879043500937987 16326407368318565251406981)
    ·
      refine ⟨3061201381559730984638809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16326407368318565251406981 3061201381559730984638809)
      ·
        refine ⟨2295901036169798238479107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3061201381559730984638809 2295901036169798238479107)
        ·
          refine ⟨3443851554254697357718661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2295901036169798238479107 3443851554254697357718661)
          ·
            refine ⟨645722166422755754572249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3443851554254697357718661 645722166422755754572249)
            ·
              refine ⟨484291624817066815929187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 645722166422755754572249 484291624817066815929187)
              ·
                refine ⟨726437437225600223893781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 484291624817066815929187 726437437225600223893781)
                ·
                  refine ⟨34051754869950010495021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 726437437225600223893781 34051754869950010495021)
                  ·
                    rfl

theorem cell23_596840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 6].length) (baseStart_596840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596840 prefixEnd_596840 := by exact prefixLift 596840
  have htrace : WordTrace (prefixWord ++ tailWord_596840) baseStart_596840 baseEnd_596840 := by
    simpa [prefixWord, tailWord_596840, baseEnd_596840] using wordTrace_append hprefix tailTrace_596840
  have hstable : (prefixWord ++ tailWord_596840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596840).length < 2 ^ (prefixWord ++ tailWord_596840).sum := by decide
  have hdescent : baseEnd_596840 < baseStart_596840 := by decide
  rcases family_descends (prefixWord ++ tailWord_596840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596853 : List Nat := [1, 3, 4, 1, 1, 3, 1, 1, 3, 5]
def baseStart_596853 : Nat := 118140960795 + 596853 * 2 ^ 59
def prefixEnd_596853 : Nat := 4983230072969 + 3 ^ 40 * 596853 * 2
def baseEnd_596853 : Nat := 102157489692686181197543

theorem tailTrace_596853 : CollatzResearch.WordTrace tailWord_596853 prefixEnd_596853 102157489692686181197543 := by
  unfold tailWord_596853
  simp only [CollatzResearch.WordTrace]
  refine ⟨21769017306710990222099213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14512678204473993481399475 21769017306710990222099213)
  ·
    refine ⟨8163381490016621333287205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21769017306710990222099213 8163381490016621333287205)
    ·
      refine ⟨1530634029378116499991351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8163381490016621333287205 1530634029378116499991351)
      ·
        refine ⟨2295951044067174749987027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1530634029378116499991351 2295951044067174749987027)
        ·
          refine ⟨3443926566100762124980541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2295951044067174749987027 3443926566100762124980541)
          ·
            refine ⟨1291472462287785796867703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3443926566100762124980541 1291472462287785796867703)
            ·
              refine ⟨1937208693431678695301555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1291472462287785796867703 1937208693431678695301555)
              ·
                refine ⟨2905813040147518042952333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1937208693431678695301555 2905813040147518042952333)
                ·
                  refine ⟨1089679890055319266107125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2905813040147518042952333 1089679890055319266107125)
                  ·
                    refine ⟨102157489692686181197543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1089679890055319266107125 102157489692686181197543)
                    ·
                      rfl

theorem cell23_596853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_596853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596853 prefixEnd_596853 := by exact prefixLift 596853
  have htrace : WordTrace (prefixWord ++ tailWord_596853) baseStart_596853 baseEnd_596853 := by
    simpa [prefixWord, tailWord_596853, baseEnd_596853] using wordTrace_append hprefix tailTrace_596853
  have hstable : (prefixWord ++ tailWord_596853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596853).length < 2 ^ (prefixWord ++ tailWord_596853).sum := by decide
  have hdescent : baseEnd_596853 < baseStart_596853 := by decide
  rcases family_descends (prefixWord ++ tailWord_596853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596893 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 5, 2, 3]
def baseStart_596893 : Nat := 118140960795 + 596893 * 2 ^ 59
def prefixEnd_596893 : Nat := 4983230072969 + 3 ^ 40 * 596893 * 2
def baseEnd_596893 : Nat := 306493008304238387092445

theorem tailTrace_596893 : CollatzResearch.WordTrace tailWord_596893 prefixEnd_596893 306493008304238387092445 := by
  unfold tailWord_596893
  simp only [CollatzResearch.WordTrace]
  refine ⟨21770476226566077053555333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14513650817710718035703555 21770476226566077053555333)
  ·
    refine ⟨4081964292481139447541625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21770476226566077053555333 4081964292481139447541625)
    ·
      refine ⟨3061473219360854585656219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4081964292481139447541625 3061473219360854585656219)
      ·
        refine ⟨4592209829041281878484329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3061473219360854585656219 4592209829041281878484329)
        ·
          refine ⟨3444157371780961408863247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4592209829041281878484329 3444157371780961408863247)
          ·
            refine ⟨5166236057671442113294871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3444157371780961408863247 5166236057671442113294871)
            ·
              refine ⟨7749354086507163169942307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5166236057671442113294871 7749354086507163169942307)
              ·
                refine ⟨11624031129760744754913461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7749354086507163169942307 11624031129760744754913461)
                ·
                  refine ⟨1089752918415069820773137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11624031129760744754913461 1089752918415069820773137)
                  ·
                    refine ⟨817314688811302365579853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1089752918415069820773137 817314688811302365579853)
                    ·
                      refine ⟨306493008304238387092445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 817314688811302365579853 306493008304238387092445)
                      ·
                        rfl

theorem cell23_596893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_596893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596893 prefixEnd_596893 := by exact prefixLift 596893
  have htrace : WordTrace (prefixWord ++ tailWord_596893) baseStart_596893 baseEnd_596893 := by
    simpa [prefixWord, tailWord_596893, baseEnd_596893] using wordTrace_append hprefix tailTrace_596893
  have hstable : (prefixWord ++ tailWord_596893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596893).length < 2 ^ (prefixWord ++ tailWord_596893).sum := by decide
  have hdescent : baseEnd_596893 < baseStart_596893 := by decide
  rcases family_descends (prefixWord ++ tailWord_596893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596896 : List Nat := [2, 1, 1, 4, 1, 1, 5, 8]
def baseStart_596896 : Nat := 118140960795 + 596896 * 2 ^ 59
def prefixEnd_596896 : Nat := 4983230072969 + 3 ^ 40 * 596896 * 2
def baseEnd_596896 : Nat := 11351649953563032420553

theorem tailTrace_596896 : CollatzResearch.WordTrace tailWord_596896 prefixEnd_596896 11351649953563032420553 := by
  unfold tailWord_596896
  simp only [CollatzResearch.WordTrace]
  refine ⟨10885292822777604282957271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14513723763703472377276361 10885292822777604282957271)
  ·
    refine ⟨16327939234166406424435907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10885292822777604282957271 16327939234166406424435907)
    ·
      refine ⟨24491908851249609636653861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16327939234166406424435907 24491908851249609636653861)
      ·
        refine ⟨4592232909609301806872599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24491908851249609636653861 4592232909609301806872599)
        ·
          refine ⟨6888349364413952710308899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4592232909609301806872599 6888349364413952710308899)
          ·
            refine ⟨10332524046620929065463349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6888349364413952710308899 10332524046620929065463349)
            ·
              refine ⟨968674129370712099887189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10332524046620929065463349 968674129370712099887189)
              ·
                refine ⟨11351649953563032420553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 968674129370712099887189 11351649953563032420553)
                ·
                  rfl

theorem cell23_596896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 8].length) (baseStart_596896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596896 prefixEnd_596896 := by exact prefixLift 596896
  have htrace : WordTrace (prefixWord ++ tailWord_596896) baseStart_596896 baseEnd_596896 := by
    simpa [prefixWord, tailWord_596896, baseEnd_596896] using wordTrace_append hprefix tailTrace_596896
  have hstable : (prefixWord ++ tailWord_596896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596896).length < 2 ^ (prefixWord ++ tailWord_596896).sum := by decide
  have hdescent : baseEnd_596896 < baseStart_596896 := by decide
  rcases family_descends (prefixWord ++ tailWord_596896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596940 : List Nat := [2, 2, 1, 4, 1, 1, 3, 1, 4, 1, 3]
def baseStart_596940 : Nat := 118140960795 + 596940 * 2 ^ 59
def prefixEnd_596940 : Nat := 4983230072969 + 3 ^ 40 * 596940 * 2
def baseEnd_596940 : Nat := 306517141894999703204729

theorem tailTrace_596940 : CollatzResearch.WordTrace tailWord_596940 prefixEnd_596940 306517141894999703204729 := by
  unfold tailWord_596940
  simp only [CollatzResearch.WordTrace]
  refine ⟨10886095228697902040258137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14514793638263869387010849 10886095228697902040258137)
  ·
    refine ⟨8164571421523426530193603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10886095228697902040258137 8164571421523426530193603)
    ·
      refine ⟨12246857132285139795290405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8164571421523426530193603 12246857132285139795290405)
      ·
        refine ⟨2296285712303463711616951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12246857132285139795290405 2296285712303463711616951)
        ·
          refine ⟨3444428568455195567425427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2296285712303463711616951 3444428568455195567425427)
          ·
            refine ⟨5166642852682793351138141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3444428568455195567425427 5166642852682793351138141)
            ·
              refine ⟨1937491069756047506676803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5166642852682793351138141 1937491069756047506676803)
              ·
                refine ⟨2906236604634071260015205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1937491069756047506676803 2906236604634071260015205)
                ·
                  refine ⟨544919363368888361252851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2906236604634071260015205 544919363368888361252851)
                  ·
                    refine ⟨817379045053332541879277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 544919363368888361252851 817379045053332541879277)
                    ·
                      refine ⟨306517141894999703204729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 817379045053332541879277 306517141894999703204729)
                      ·
                        rfl

theorem cell23_596940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_596940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596940 prefixEnd_596940 := by exact prefixLift 596940
  have htrace : WordTrace (prefixWord ++ tailWord_596940) baseStart_596940 baseEnd_596940 := by
    simpa [prefixWord, tailWord_596940, baseEnd_596940] using wordTrace_append hprefix tailTrace_596940
  have hstable : (prefixWord ++ tailWord_596940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596940).length < 2 ^ (prefixWord ++ tailWord_596940).sum := by decide
  have hdescent : baseEnd_596940 < baseStart_596940 := by decide
  rcases family_descends (prefixWord ++ tailWord_596940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596957 : List Nat := [1, 4, 3, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_596957 : Nat := 118140960795 + 596957 * 2 ^ 59
def prefixEnd_596957 : Nat := 4983230072969 + 3 ^ 40 * 596957 * 2
def baseEnd_596957 : Nat := 306525871066126136692151

theorem tailTrace_596957 : CollatzResearch.WordTrace tailWord_596957 prefixEnd_596957 306525871066126136692151 := by
  unfold tailWord_596957
  simp only [CollatzResearch.WordTrace]
  refine ⟨21772810498334215983885125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14515206998889477322590083 21772810498334215983885125)
  ·
    refine ⟨4082401968437665496978461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21772810498334215983885125 4082401968437665496978461)
    ·
      refine ⟨1530900738164124561366923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4082401968437665496978461 1530900738164124561366923)
      ·
        refine ⟨2296351107246186842050385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1530900738164124561366923 2296351107246186842050385)
        ·
          refine ⟨1722263330434640131537789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2296351107246186842050385 1722263330434640131537789)
          ·
            refine ⟨645848748912990049326671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1722263330434640131537789 645848748912990049326671)
            ·
              refine ⟨968773123369485073990007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 645848748912990049326671 968773123369485073990007)
              ·
                refine ⟨1453159685054227610985011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 968773123369485073990007 1453159685054227610985011)
                ·
                  refine ⟨2179739527581341416477517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1453159685054227610985011 2179739527581341416477517)
                  ·
                    refine ⟨817402322843003031179069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2179739527581341416477517 817402322843003031179069)
                    ·
                      refine ⟨306525871066126136692151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 817402322843003031179069 306525871066126136692151)
                      ·
                        rfl

theorem cell23_596957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_596957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596957 prefixEnd_596957 := by exact prefixLift 596957
  have htrace : WordTrace (prefixWord ++ tailWord_596957) baseStart_596957 baseEnd_596957 := by
    simpa [prefixWord, tailWord_596957, baseEnd_596957] using wordTrace_append hprefix tailTrace_596957
  have hstable : (prefixWord ++ tailWord_596957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596957).length < 2 ^ (prefixWord ++ tailWord_596957).sum := by decide
  have hdescent : baseEnd_596957 < baseStart_596957 := by decide
  rcases family_descends (prefixWord ++ tailWord_596957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596967 : List Nat := [1, 1, 5, 2, 2, 1, 1, 4, 1, 3, 2]
def baseStart_596967 : Nat := 118140960795 + 596967 * 2 ^ 59
def prefixEnd_596967 : Nat := 4983230072969 + 3 ^ 40 * 596967 * 2
def baseEnd_596967 : Nat := 306531005872671097567105

theorem tailTrace_596967 : CollatzResearch.WordTrace tailWord_596967 prefixEnd_596967 306531005872671097567105 := by
  unfold tailWord_596967
  simp only [CollatzResearch.WordTrace]
  refine ⟨21773175228297987691749155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14515450152198658461166103 21773175228297987691749155)
  ·
    refine ⟨32659762842446981537623733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21773175228297987691749155 32659762842446981537623733)
    ·
      refine ⟨3061852766479404519152225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32659762842446981537623733 3061852766479404519152225)
      ·
        refine ⟨2296389574859553389364169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3061852766479404519152225 2296389574859553389364169)
        ·
          refine ⟨1722292181144665042023127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2296389574859553389364169 1722292181144665042023127)
          ·
            refine ⟨2583438271716997563034691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1722292181144665042023127 2583438271716997563034691)
            ·
              refine ⟨3875157407575496344552037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2583438271716997563034691 3875157407575496344552037)
              ·
                refine ⟨726592013920405564603507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3875157407575496344552037 726592013920405564603507)
                ·
                  refine ⟨1089888020880608346905261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 726592013920405564603507 1089888020880608346905261)
                  ·
                    refine ⟨408708007830228130089473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1089888020880608346905261 408708007830228130089473)
                    ·
                      refine ⟨306531005872671097567105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 408708007830228130089473 306531005872671097567105)
                      ·
                        rfl

theorem cell23_596967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_596967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596967 prefixEnd_596967 := by exact prefixLift 596967
  have htrace : WordTrace (prefixWord ++ tailWord_596967) baseStart_596967 baseEnd_596967 := by
    simpa [prefixWord, tailWord_596967, baseEnd_596967] using wordTrace_append hprefix tailTrace_596967
  have hstable : (prefixWord ++ tailWord_596967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596967).length < 2 ^ (prefixWord ++ tailWord_596967).sum := by decide
  have hdescent : baseEnd_596967 < baseStart_596967 := by decide
  rcases family_descends (prefixWord ++ tailWord_596967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596986 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 9]
def baseStart_596986 : Nat := 118140960795 + 596986 * 2 ^ 59
def prefixEnd_596986 : Nat := 4983230072969 + 3 ^ 40 * 596986 * 2
def baseEnd_596986 : Nat := 34060084667234058136613

theorem tailTrace_596986 : CollatzResearch.WordTrace tailWord_596986 prefixEnd_596986 34060084667234058136613 := by
  unfold tailWord_596986
  simp only [CollatzResearch.WordTrace]
  refine ⟨5443467053807288484172703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14515912143486102624460541 5443467053807288484172703)
  ·
    refine ⟨8165200580710932726259055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5443467053807288484172703 8165200580710932726259055)
    ·
      refine ⟨12247800871066399089388583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8165200580710932726259055 12247800871066399089388583)
      ·
        refine ⟨18371701306599598634082875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12247800871066399089388583 18371701306599598634082875)
        ·
          refine ⟨27557551959899397951124313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18371701306599598634082875 27557551959899397951124313)
          ·
            refine ⟨20668163969924548463343235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27557551959899397951124313 20668163969924548463343235)
            ·
              refine ⟨31002245954886822695014853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20668163969924548463343235 31002245954886822695014853)
              ·
                refine ⟨5812921116541279255315285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31002245954886822695014853 5812921116541279255315285)
                ·
                  refine ⟨34060084667234058136613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5812921116541279255315285 34060084667234058136613)
                  ·
                    rfl

theorem cell23_596986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 9].length) (baseStart_596986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596986 prefixEnd_596986 := by exact prefixLift 596986
  have htrace : WordTrace (prefixWord ++ tailWord_596986) baseStart_596986 baseEnd_596986 := by
    simpa [prefixWord, tailWord_596986, baseEnd_596986] using wordTrace_append hprefix tailTrace_596986
  have hstable : (prefixWord ++ tailWord_596986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596986).length < 2 ^ (prefixWord ++ tailWord_596986).sum := by decide
  have hdescent : baseEnd_596986 < baseStart_596986 := by decide
  rcases family_descends (prefixWord ++ tailWord_596986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596997 : List Nat := [1, 3, 1, 1, 2, 3, 2, 4, 2, 2, 2]
def baseStart_596997 : Nat := 118140960795 + 596997 * 2 ^ 59
def prefixEnd_596997 : Nat := 4983230072969 + 3 ^ 40 * 596997 * 2
def baseEnd_596997 : Nat := 306546410292305980191967

theorem tailTrace_596997 : CollatzResearch.WordTrace tailWord_596997 prefixEnd_596997 306546410292305980191967 := by
  unfold tailWord_596997
  simp only [CollatzResearch.WordTrace]
  refine ⟨21774269418189302815341245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14516179612126201876894163 21774269418189302815341245)
  ·
    refine ⟨8165351031820988555752967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21774269418189302815341245 8165351031820988555752967)
    ·
      refine ⟨12248026547731482833629451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8165351031820988555752967 12248026547731482833629451)
      ·
        refine ⟨18372039821597224250444177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12248026547731482833629451 18372039821597224250444177)
        ·
          refine ⟨13779029866197918187833133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18372039821597224250444177 13779029866197918187833133)
          ·
            refine ⟨5167136199824219320437425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13779029866197918187833133 5167136199824219320437425)
            ·
              refine ⟨3875352149868164490328069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5167136199824219320437425 3875352149868164490328069)
              ·
                refine ⟨726628528100280841936513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3875352149868164490328069 726628528100280841936513)
                ·
                  refine ⟨544971396075210631452385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 726628528100280841936513 544971396075210631452385)
                  ·
                    refine ⟨408728547056407973589289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 544971396075210631452385 408728547056407973589289)
                    ·
                      refine ⟨306546410292305980191967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 408728547056407973589289 306546410292305980191967)
                      ·
                        rfl

theorem cell23_596997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 2, 2].length) (baseStart_596997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_596997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_596997 prefixEnd_596997 := by exact prefixLift 596997
  have htrace : WordTrace (prefixWord ++ tailWord_596997) baseStart_596997 baseEnd_596997 := by
    simpa [prefixWord, tailWord_596997, baseEnd_596997] using wordTrace_append hprefix tailTrace_596997
  have hstable : (prefixWord ++ tailWord_596997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596997).length < 2 ^ (prefixWord ++ tailWord_596997).sum := by decide
  have hdescent : baseEnd_596997 < baseStart_596997 := by decide
  rcases family_descends (prefixWord ++ tailWord_596997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597003 : List Nat := [1, 1, 1, 1, 6, 2, 3, 1, 7]
def baseStart_597003 : Nat := 118140960795 + 597003 * 2 ^ 59
def prefixEnd_597003 : Nat := 4983230072969 + 3 ^ 40 * 597003 * 2
def baseEnd_597003 : Nat := 34061054575136995190771

theorem tailTrace_597003 : CollatzResearch.WordTrace tailWord_597003 prefixEnd_597003 34061054575136995190771 := by
  unfold tailWord_597003
  simp only [CollatzResearch.WordTrace]
  refine ⟨21774488256167565840059663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14516325504111710560039775 21774488256167565840059663)
  ·
    refine ⟨32661732384251348760089495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21774488256167565840059663 32661732384251348760089495)
    ·
      refine ⟨48992598576377023140134243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32661732384251348760089495 48992598576377023140134243)
      ·
        refine ⟨73488897864565534710201365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48992598576377023140134243 73488897864565534710201365)
        ·
          refine ⟨3444792087401509439540689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 73488897864565534710201365 3444792087401509439540689)
          ·
            refine ⟨2583594065551132079655517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3444792087401509439540689 2583594065551132079655517)
            ·
              refine ⟨968847774581674529870819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2583594065551132079655517 968847774581674529870819)
              ·
                refine ⟨1453271661872511794806229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 968847774581674529870819 1453271661872511794806229)
                ·
                  refine ⟨34061054575136995190771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1453271661872511794806229 34061054575136995190771)
                  ·
                    rfl

theorem cell23_597003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 7].length) (baseStart_597003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597003 prefixEnd_597003 := by exact prefixLift 597003
  have htrace : WordTrace (prefixWord ++ tailWord_597003) baseStart_597003 baseEnd_597003 := by
    simpa [prefixWord, tailWord_597003, baseEnd_597003] using wordTrace_append hprefix tailTrace_597003
  have hstable : (prefixWord ++ tailWord_597003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597003).length < 2 ^ (prefixWord ++ tailWord_597003).sum := by decide
  have hdescent : baseEnd_597003 < baseStart_597003 := by decide
  rcases family_descends (prefixWord ++ tailWord_597003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597054 : List Nat := [4, 2, 1, 3, 1, 1, 4, 2, 5]
def baseStart_597054 : Nat := 118140960795 + 597054 * 2 ^ 59
def prefixEnd_597054 : Nat := 4983230072969 + 3 ^ 40 * 597054 * 2
def baseEnd_597054 : Nat := 34063964298845806353245

theorem tailTrace_597054 : CollatzResearch.WordTrace tailWord_597054 prefixEnd_597054 34063964298845806353245 := by
  unfold tailWord_597054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2722043547372850193770777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14517565585988534366777477 2722043547372850193770777)
  ·
    refine ⟨2041532660529637645328083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2722043547372850193770777 2041532660529637645328083)
    ·
      refine ⟨3062298990794456467992125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2041532660529637645328083 3062298990794456467992125)
      ·
        refine ⟨1148362121547921175497047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3062298990794456467992125 1148362121547921175497047)
        ·
          refine ⟨1722543182321881763245571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1148362121547921175497047 1722543182321881763245571)
          ·
            refine ⟨2583814773482822644868357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1722543182321881763245571 2583814773482822644868357)
            ·
              refine ⟨484465270028029245912817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2583814773482822644868357 484465270028029245912817)
              ·
                refine ⟨363348952521021934434613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 484465270028029245912817 363348952521021934434613)
                ·
                  refine ⟨34063964298845806353245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 363348952521021934434613 34063964298845806353245)
                  ·
                    rfl

theorem cell23_597054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_597054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597054 prefixEnd_597054 := by exact prefixLift 597054
  have htrace : WordTrace (prefixWord ++ tailWord_597054) baseStart_597054 baseEnd_597054 := by
    simpa [prefixWord, tailWord_597054, baseEnd_597054] using wordTrace_append hprefix tailTrace_597054
  have hstable : (prefixWord ++ tailWord_597054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597054).length < 2 ^ (prefixWord ++ tailWord_597054).sum := by decide
  have hdescent : baseEnd_597054 < baseStart_597054 := by decide
  rcases family_descends (prefixWord ++ tailWord_597054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597080 : List Nat := [2, 1, 2, 2, 1, 3, 3, 2, 3, 4]
def baseStart_597080 : Nat := 118140960795 + 597080 * 2 ^ 59
def prefixEnd_597080 : Nat := 4983230072969 + 3 ^ 40 * 597080 * 2
def baseEnd_597080 : Nat := 102196343062209718484695

theorem tailTrace_597080 : CollatzResearch.WordTrace tailWord_597080 prefixEnd_597080 102196343062209718484695 := by
  unfold tailWord_597080
  simp only [CollatzResearch.WordTrace]
  refine ⟨10888648338444303995306347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14518197784592405327075129 10888648338444303995306347)
  ·
    refine ⟨16332972507666455992959521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10888648338444303995306347 16332972507666455992959521)
    ·
      refine ⟨12249729380749841994719641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16332972507666455992959521 12249729380749841994719641)
      ·
        refine ⟨9187297035562381496039731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12249729380749841994719641 9187297035562381496039731)
        ·
          refine ⟨13780945553343572244059597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9187297035562381496039731 13780945553343572244059597)
          ·
            refine ⟨5167854582503839591522349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13780945553343572244059597 5167854582503839591522349)
            ·
              refine ⟨1937945468438939846820881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5167854582503839591522349 1937945468438939846820881)
              ·
                refine ⟨1453459101329204885115661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1937945468438939846820881 1453459101329204885115661)
                ·
                  refine ⟨545047162998451831918373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1453459101329204885115661 545047162998451831918373)
                  ·
                    refine ⟨102196343062209718484695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 545047162998451831918373 102196343062209718484695)
                    ·
                      rfl

theorem cell23_597080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 3, 4].length) (baseStart_597080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597080 prefixEnd_597080 := by exact prefixLift 597080
  have htrace : WordTrace (prefixWord ++ tailWord_597080) baseStart_597080 baseEnd_597080 := by
    simpa [prefixWord, tailWord_597080, baseEnd_597080] using wordTrace_append hprefix tailTrace_597080
  have hstable : (prefixWord ++ tailWord_597080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597080).length < 2 ^ (prefixWord ++ tailWord_597080).sum := by decide
  have hdescent : baseEnd_597080 < baseStart_597080 := by decide
  rcases family_descends (prefixWord ++ tailWord_597080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597093 : List Nat := [1, 3, 1, 3, 2, 1, 2, 2, 8]
def baseStart_597093 : Nat := 118140960795 + 597093 * 2 ^ 59
def prefixEnd_597093 : Nat := 4983230072969 + 3 ^ 40 * 597093 * 2
def baseEnd_597093 : Nat := 34066189381681956065725

theorem tailTrace_597093 : CollatzResearch.WordTrace tailWord_597093 prefixEnd_597093 34066189381681956065725 := by
  unfold tailWord_597093
  simp only [CollatzResearch.WordTrace]
  refine ⟨21777770825841511210835933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14518513883894340807223955 21777770825841511210835933)
  ·
    refine ⟨8166664059690566704063475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21777770825841511210835933 8166664059690566704063475)
    ·
      refine ⟨12249996089535850056095213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8166664059690566704063475 12249996089535850056095213)
      ·
        refine ⟨4593748533575943771035705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12249996089535850056095213 4593748533575943771035705)
        ·
          refine ⟨3445311400181957828276779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4593748533575943771035705 3445311400181957828276779)
          ·
            refine ⟨5167967100272936742415169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3445311400181957828276779 5167967100272936742415169)
            ·
              refine ⟨3875975325204702556811377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5167967100272936742415169 3875975325204702556811377)
              ·
                refine ⟨2906981493903526917608533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3875975325204702556811377 2906981493903526917608533)
                ·
                  refine ⟨34066189381681956065725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2906981493903526917608533 34066189381681956065725)
                  ·
                    rfl

theorem cell23_597093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 8].length) (baseStart_597093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597093 prefixEnd_597093 := by exact prefixLift 597093
  have htrace : WordTrace (prefixWord ++ tailWord_597093) baseStart_597093 baseEnd_597093 := by
    simpa [prefixWord, tailWord_597093, baseEnd_597093] using wordTrace_append hprefix tailTrace_597093
  have hstable : (prefixWord ++ tailWord_597093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597093).length < 2 ^ (prefixWord ++ tailWord_597093).sum := by decide
  have hdescent : baseEnd_597093 < baseStart_597093 := by decide
  rcases family_descends (prefixWord ++ tailWord_597093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597097 : List Nat := [1, 2, 1, 1, 1, 6, 1, 5, 1, 4]
def baseStart_597097 : Nat := 118140960795 + 597097 * 2 ^ 59
def prefixEnd_597097 : Nat := 4983230072969 + 3 ^ 40 * 597097 * 2
def baseEnd_597097 : Nat := 102199252785918529647169

theorem tailTrace_597097 : CollatzResearch.WordTrace tailWord_597097 prefixEnd_597097 102199252785918529647169 := by
  unfold tailWord_597097
  simp only [CollatzResearch.WordTrace]
  refine ⟨21777916717827019893981545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14518611145218013262654363 21777916717827019893981545)
  ·
    refine ⟨16333437538370264920486159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21777916717827019893981545 16333437538370264920486159)
    ·
      refine ⟨24500156307555397380729239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16333437538370264920486159 24500156307555397380729239)
      ·
        refine ⟨36750234461333096071093859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24500156307555397380729239 36750234461333096071093859)
        ·
          refine ⟨55125351691999644106640789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36750234461333096071093859 55125351691999644106640789)
          ·
            refine ⟨2584000860562483317498787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 55125351691999644106640789 2584000860562483317498787)
            ·
              refine ⟨3876001290843724976248181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2584000860562483317498787 3876001290843724976248181)
              ·
                refine ⟨363375121016599216523267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3876001290843724976248181 363375121016599216523267)
                ·
                  refine ⟨545062681524898824784901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 363375121016599216523267 545062681524898824784901)
                  ·
                    refine ⟨102199252785918529647169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 545062681524898824784901 102199252785918529647169)
                    ·
                      rfl

theorem cell23_597097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 1, 4].length) (baseStart_597097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597097 prefixEnd_597097 := by exact prefixLift 597097
  have htrace : WordTrace (prefixWord ++ tailWord_597097) baseStart_597097 baseEnd_597097 := by
    simpa [prefixWord, tailWord_597097, baseEnd_597097] using wordTrace_append hprefix tailTrace_597097
  have hstable : (prefixWord ++ tailWord_597097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597097).length < 2 ^ (prefixWord ++ tailWord_597097).sum := by decide
  have hdescent : baseEnd_597097 < baseStart_597097 := by decide
  rcases family_descends (prefixWord ++ tailWord_597097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597110 : List Nat := [5, 1, 1, 2, 1, 1, 3, 1, 8]
def baseStart_597110 : Nat := 118140960795 + 597110 * 2 ^ 59
def prefixEnd_597110 : Nat := 4983230072969 + 3 ^ 40 * 597110 * 2
def baseEnd_597110 : Nat := 34067159289584893119883

theorem tailTrace_597110 : CollatzResearch.WordTrace tailWord_597110 prefixEnd_597110 34067159289584893119883 := by
  unfold tailWord_597110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1361149429173745194637799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14518927244519948742803189 1361149429173745194637799)
  ·
    refine ⟨2041724143760617791956699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1361149429173745194637799 2041724143760617791956699)
    ·
      refine ⟨3062586215640926687935049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2041724143760617791956699 3062586215640926687935049)
      ·
        refine ⟨2296939661730695015951287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3062586215640926687935049 2296939661730695015951287)
        ·
          refine ⟨3445409492596042523926931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2296939661730695015951287 3445409492596042523926931)
          ·
            refine ⟨5168114238894063785890397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3445409492596042523926931 5168114238894063785890397)
            ·
              refine ⟨1938042839585273919708899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5168114238894063785890397 1938042839585273919708899)
              ·
                refine ⟨2907064259377910879563349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1938042839585273919708899 2907064259377910879563349)
                ·
                  refine ⟨34067159289584893119883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2907064259377910879563349 34067159289584893119883)
                  ·
                    rfl

theorem cell23_597110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_597110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597110 prefixEnd_597110 := by exact prefixLift 597110
  have htrace : WordTrace (prefixWord ++ tailWord_597110) baseStart_597110 baseEnd_597110 := by
    simpa [prefixWord, tailWord_597110, baseEnd_597110] using wordTrace_append hprefix tailTrace_597110
  have hstable : (prefixWord ++ tailWord_597110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597110).length < 2 ^ (prefixWord ++ tailWord_597110).sum := by decide
  have hdescent : baseEnd_597110 < baseStart_597110 := by decide
  rcases family_descends (prefixWord ++ tailWord_597110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597183 : List Nat := [1, 1, 2, 2, 2, 2, 3, 10]
def baseStart_597183 : Nat := 118140960795 + 597183 * 2 ^ 59
def prefixEnd_597183 : Nat := 4983230072969 + 3 ^ 40 * 597183 * 2
def baseEnd_597183 : Nat := 11357108062742305646893

theorem tailTrace_597183 : CollatzResearch.WordTrace tailWord_597183 prefixEnd_597183 11357108062742305646893 := by
  unfold tailWord_597183
  simp only [CollatzResearch.WordTrace]
  refine ⟨21781053395515456581612203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14520702263676971054408135 21781053395515456581612203)
  ·
    refine ⟨32671580093273184872418305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21781053395515456581612203 32671580093273184872418305)
    ·
      refine ⟨24503685069954888654313729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32671580093273184872418305 24503685069954888654313729)
      ·
        refine ⟨18377763802466166490735297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24503685069954888654313729 18377763802466166490735297)
        ·
          refine ⟨13783322851849624868051473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18377763802466166490735297 13783322851849624868051473)
          ·
            refine ⟨10337492138887218651038605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13783322851849624868051473 10337492138887218651038605)
            ·
              refine ⟨3876559552082706994139477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10337492138887218651038605 3876559552082706994139477)
              ·
                refine ⟨11357108062742305646893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3876559552082706994139477 11357108062742305646893)
                ·
                  rfl

theorem cell23_597183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 10].length) (baseStart_597183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597183 prefixEnd_597183 := by exact prefixLift 597183
  have htrace : WordTrace (prefixWord ++ tailWord_597183) baseStart_597183 baseEnd_597183 := by
    simpa [prefixWord, tailWord_597183, baseEnd_597183] using wordTrace_append hprefix tailTrace_597183
  have hstable : (prefixWord ++ tailWord_597183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597183).length < 2 ^ (prefixWord ++ tailWord_597183).sum := by decide
  have hdescent : baseEnd_597183 < baseStart_597183 := by decide
  rcases family_descends (prefixWord ++ tailWord_597183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597194 : List Nat := [3, 1, 2, 1, 3, 4, 1, 2, 1, 1, 4]
def baseStart_597194 : Nat := 118140960795 + 597194 * 2 ^ 59
def prefixEnd_597194 : Nat := 4983230072969 + 3 ^ 40 * 597194 * 2
def baseEnd_597194 : Nat := 306647565981241709428561

theorem tailTrace_597194 : CollatzResearch.WordTrace tailWord_597194 prefixEnd_597194 306647565981241709428561 := by
  unfold tailWord_597194
  simp only [CollatzResearch.WordTrace]
  refine ⟨5445363649618901365065659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14520969732317070306841757 5445363649618901365065659)
  ·
    refine ⟨8168045474428352047598489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5445363649618901365065659 8168045474428352047598489)
    ·
      refine ⟨6126034105821264035698867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8168045474428352047598489 6126034105821264035698867)
      ·
        refine ⟨9189051158731896053548301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6126034105821264035698867 9189051158731896053548301)
        ·
          refine ⟨3445894184524461020080613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9189051158731896053548301 3445894184524461020080613)
          ·
            refine ⟨646105159598336441265115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3445894184524461020080613 646105159598336441265115)
            ·
              refine ⟨969157739397504661897673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646105159598336441265115 969157739397504661897673)
              ·
                refine ⟨726868304548128496423255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 969157739397504661897673 726868304548128496423255)
                ·
                  refine ⟨1090302456822192744634883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 726868304548128496423255 1090302456822192744634883)
                  ·
                    refine ⟨1635453685233289116952325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1090302456822192744634883 1635453685233289116952325)
                    ·
                      refine ⟨306647565981241709428561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1635453685233289116952325 306647565981241709428561)
                      ·
                        rfl

theorem cell23_597194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_597194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597194 prefixEnd_597194 := by exact prefixLift 597194
  have htrace : WordTrace (prefixWord ++ tailWord_597194) baseStart_597194 baseEnd_597194 := by
    simpa [prefixWord, tailWord_597194, baseEnd_597194] using wordTrace_append hprefix tailTrace_597194
  have hstable : (prefixWord ++ tailWord_597194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597194).length < 2 ^ (prefixWord ++ tailWord_597194).sum := by decide
  have hdescent : baseEnd_597194 < baseStart_597194 := by decide
  rcases family_descends (prefixWord ++ tailWord_597194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597203 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 6]
def baseStart_597203 : Nat := 118140960795 + 597203 * 2 ^ 59
def prefixEnd_597203 : Nat := 4983230072969 + 3 ^ 40 * 597203 * 2
def baseEnd_597203 : Nat := 306652187307132174216019

theorem tailTrace_597203 : CollatzResearch.WordTrace tailWord_597203 prefixEnd_597203 306652187307132174216019 := by
  unfold tailWord_597203
  simp only [CollatzResearch.WordTrace]
  refine ⟨21781782855442999997340263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14521188570295333331560175 21781782855442999997340263)
  ·
    refine ⟨32672674283164499996010395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21781782855442999997340263 32672674283164499996010395)
    ·
      refine ⟨49009011424746749994015593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32672674283164499996010395 49009011424746749994015593)
      ·
        refine ⟨36756758568560062495511695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49009011424746749994015593 36756758568560062495511695)
        ·
          refine ⟨55135137852840093743267543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36756758568560062495511695 55135137852840093743267543)
          ·
            refine ⟨82702706779260140614901315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55135137852840093743267543 82702706779260140614901315)
            ·
              refine ⟨124054060168890210922351973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82702706779260140614901315 124054060168890210922351973)
              ·
                refine ⟨23260136281666914547940995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124054060168890210922351973 23260136281666914547940995)
                ·
                  refine ⟨34890204422500371821911493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23260136281666914547940995 34890204422500371821911493)
                  ·
                    refine ⟨6541913329218819716608405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34890204422500371821911493 6541913329218819716608405)
                    ·
                      refine ⟨306652187307132174216019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6541913329218819716608405 306652187307132174216019)
                      ·
                        rfl

theorem cell23_597203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_597203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597203 prefixEnd_597203 := by exact prefixLift 597203
  have htrace : WordTrace (prefixWord ++ tailWord_597203) baseStart_597203 baseEnd_597203 := by
    simpa [prefixWord, tailWord_597203, baseEnd_597203] using wordTrace_append hprefix tailTrace_597203
  have hstable : (prefixWord ++ tailWord_597203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597203).length < 2 ^ (prefixWord ++ tailWord_597203).sum := by decide
  have hdescent : baseEnd_597203 < baseStart_597203 := by decide
  rcases family_descends (prefixWord ++ tailWord_597203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597204 : List Nat := [2, 4, 1, 4, 1, 1, 1, 2, 1, 6]
def baseStart_597204 : Nat := 118140960795 + 597204 * 2 ^ 59
def prefixEnd_597204 : Nat := 4983230072969 + 3 ^ 40 * 597204 * 2
def baseEnd_597204 : Nat := 102217566929262223434505

theorem tailTrace_597204 : CollatzResearch.WordTrace tailWord_597204 prefixEnd_597204 102217566929262223434505 := by
  unfold tailWord_597204
  simp only [CollatzResearch.WordTrace]
  refine ⟨10890909664219688584063333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14521212885626251445417777 10890909664219688584063333)
  ·
    refine ⟨2042045562041191609511875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10890909664219688584063333 2042045562041191609511875)
    ·
      refine ⟨3063068343061787414267813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2042045562041191609511875 3063068343061787414267813)
      ·
        refine ⟨574325314324085140175215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3063068343061787414267813 574325314324085140175215)
        ·
          refine ⟨861487971486127710262823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 574325314324085140175215 861487971486127710262823)
          ·
            refine ⟨1292231957229191565394235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 861487971486127710262823 1292231957229191565394235)
            ·
              refine ⟨1938347935843787348091353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1292231957229191565394235 1938347935843787348091353)
              ·
                refine ⟨1453760951882840511068515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1938347935843787348091353 1453760951882840511068515)
                ·
                  refine ⟨2180641427824260766602773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1453760951882840511068515 2180641427824260766602773)
                  ·
                    refine ⟨102217566929262223434505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2180641427824260766602773 102217566929262223434505)
                    ·
                      rfl

theorem cell23_597204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_597204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597204 prefixEnd_597204 := by exact prefixLift 597204
  have htrace : WordTrace (prefixWord ++ tailWord_597204) baseStart_597204 baseEnd_597204 := by
    simpa [prefixWord, tailWord_597204, baseEnd_597204] using wordTrace_append hprefix tailTrace_597204
  have hstable : (prefixWord ++ tailWord_597204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597204).length < 2 ^ (prefixWord ++ tailWord_597204).sum := by decide
  have hdescent : baseEnd_597204 < baseStart_597204 := by decide
  rcases family_descends (prefixWord ++ tailWord_597204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597228 : List Nat := [2, 2, 1, 1, 2, 4, 4, 2, 1, 2, 2]
def baseStart_597228 : Nat := 118140960795 + 597228 * 2 ^ 59
def prefixEnd_597228 : Nat := 4983230072969 + 3 ^ 40 * 597228 * 2
def baseEnd_597228 : Nat := 306665024323494576403405

theorem tailTrace_597228 : CollatzResearch.WordTrace tailWord_597228 prefixEnd_597228 306665024323494576403405 := by
  unfold tailWord_597228
  simp only [CollatzResearch.WordTrace]
  refine ⟨10891347340176214633500169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14521796453568286178000225 10891347340176214633500169)
  ·
    refine ⟨8168510505132160975125127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10891347340176214633500169 8168510505132160975125127)
    ·
      refine ⟨12252765757698241462687691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8168510505132160975125127 12252765757698241462687691)
      ·
        refine ⟨18379148636547362194031537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12252765757698241462687691 18379148636547362194031537)
        ·
          refine ⟨13784361477410521645523653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18379148636547362194031537 13784361477410521645523653)
          ·
            refine ⟨2584567777014472808535685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13784361477410521645523653 2584567777014472808535685)
            ·
              refine ⟨484606458190213651600441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2584567777014472808535685 484606458190213651600441)
              ·
                refine ⟨363454843642660238700331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 484606458190213651600441 363454843642660238700331)
                ·
                  refine ⟨545182265463990358050497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 363454843642660238700331 545182265463990358050497)
                  ·
                    refine ⟨408886699097992768537873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 545182265463990358050497 408886699097992768537873)
                    ·
                      refine ⟨306665024323494576403405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 408886699097992768537873 306665024323494576403405)
                      ·
                        rfl

theorem cell23_597228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 1, 2, 2].length) (baseStart_597228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597228 prefixEnd_597228 := by exact prefixLift 597228
  have htrace : WordTrace (prefixWord ++ tailWord_597228) baseStart_597228 baseEnd_597228 := by
    simpa [prefixWord, tailWord_597228, baseEnd_597228] using wordTrace_append hprefix tailTrace_597228
  have hstable : (prefixWord ++ tailWord_597228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597228).length < 2 ^ (prefixWord ++ tailWord_597228).sum := by decide
  have hdescent : baseEnd_597228 < baseStart_597228 := by decide
  rcases family_descends (prefixWord ++ tailWord_597228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597230 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 2, 7]
def baseStart_597230 : Nat := 118140960795 + 597230 * 2 ^ 59
def prefixEnd_597230 : Nat := 4983230072969 + 3 ^ 40 * 597230 * 2
def baseEnd_597230 : Nat := 102222017094934522859465

theorem tailTrace_597230 : CollatzResearch.WordTrace tailWord_597230 prefixEnd_597230 102222017094934522859465 := by
  unfold tailWord_597230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2722845953293147951071643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14521845084230122405715429 2722845953293147951071643)
  ·
    refine ⟨4084268929939721926607465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2722845953293147951071643 4084268929939721926607465)
    ·
      refine ⟨3063201697454791444955599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4084268929939721926607465 3063201697454791444955599)
      ·
        refine ⟨4594802546182187167433399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3063201697454791444955599 4594802546182187167433399)
        ·
          refine ⟨6892203819273280751150099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4594802546182187167433399 6892203819273280751150099)
          ·
            refine ⟨10338305728909921126725149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6892203819273280751150099 10338305728909921126725149)
            ·
              refine ⟨3876864648341220422521931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10338305728909921126725149 3876864648341220422521931)
              ·
                refine ⟨5815296972511830633782897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3876864648341220422521931 5815296972511830633782897)
                ·
                  refine ⟨4361472729383872975337173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5815296972511830633782897 4361472729383872975337173)
                  ·
                    refine ⟨102222017094934522859465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4361472729383872975337173 102222017094934522859465)
                    ·
                      rfl

theorem cell23_597230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_597230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597230 prefixEnd_597230 := by exact prefixLift 597230
  have htrace : WordTrace (prefixWord ++ tailWord_597230) baseStart_597230 baseEnd_597230 := by
    simpa [prefixWord, tailWord_597230, baseEnd_597230] using wordTrace_append hprefix tailTrace_597230
  have hstable : (prefixWord ++ tailWord_597230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597230).length < 2 ^ (prefixWord ++ tailWord_597230).sum := by decide
  have hdescent : baseEnd_597230 < baseStart_597230 := by decide
  rcases family_descends (prefixWord ++ tailWord_597230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597234 : List Nat := [3, 2, 1, 3, 4, 1, 1, 8]
def baseStart_597234 : Nat := 118140960795 + 597234 * 2 ^ 59
def prefixEnd_597234 : Nat := 4983230072969 + 3 ^ 40 * 597234 * 2
def baseEnd_597234 : Nat := 11358077970645242701051

theorem tailTrace_597234 : CollatzResearch.WordTrace tailWord_597234 prefixEnd_597234 11358077970645242701051 := by
  unfold tailWord_597234
  simp only [CollatzResearch.WordTrace]
  refine ⟨5445728379582673072929689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14521942345553794861145837 5445728379582673072929689)
  ·
    refine ⟨4084296284687004804697267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5445728379582673072929689 4084296284687004804697267)
    ·
      refine ⟨6126444427030507207045901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4084296284687004804697267 6126444427030507207045901)
      ·
        refine ⟨2297416660136440202642213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6126444427030507207045901 2297416660136440202642213)
        ·
          refine ⟨430765623775582537995415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2297416660136440202642213 430765623775582537995415)
          ·
            refine ⟨646148435663373806993123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430765623775582537995415 646148435663373806993123)
            ·
              refine ⟨969222653495060710489685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646148435663373806993123 969222653495060710489685)
              ·
                refine ⟨11358077970645242701051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 969222653495060710489685 11358077970645242701051)
                ·
                  rfl

theorem cell23_597234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 8].length) (baseStart_597234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597234 prefixEnd_597234 := by exact prefixLift 597234
  have htrace : WordTrace (prefixWord ++ tailWord_597234) baseStart_597234 baseEnd_597234 := by
    simpa [prefixWord, tailWord_597234, baseEnd_597234] using wordTrace_append hprefix tailTrace_597234
  have hstable : (prefixWord ++ tailWord_597234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597234).length < 2 ^ (prefixWord ++ tailWord_597234).sum := by decide
  have hdescent : baseEnd_597234 < baseStart_597234 := by decide
  rcases family_descends (prefixWord ++ tailWord_597234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597244 : List Nat := [2, 2, 2, 1, 5, 1, 2, 1, 1, 3, 3]
def baseStart_597244 : Nat := 118140960795 + 597244 * 2 ^ 59
def prefixEnd_597244 : Nat := 4983230072969 + 3 ^ 40 * 597244 * 2
def baseEnd_597244 : Nat := 306673240013966513803331

theorem tailTrace_597244 : CollatzResearch.WordTrace tailWord_597244 prefixEnd_597244 306673240013966513803331 := by
  unfold tailWord_597244
  simp only [CollatzResearch.WordTrace]
  refine ⟨10891639124147231999791393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14522185498862975999721857 10891639124147231999791393)
  ·
    refine ⟨8168729343110423999843545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10891639124147231999791393 8168729343110423999843545)
    ·
      refine ⟨6126547007332817999882659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8168729343110423999843545 6126547007332817999882659)
      ·
        refine ⟨9189820510999226999823989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6126547007332817999882659 9189820510999226999823989)
        ·
          refine ⟨861545672906177531233499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9189820510999226999823989 861545672906177531233499)
          ·
            refine ⟨1292318509359266296850249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 861545672906177531233499 1292318509359266296850249)
            ·
              refine ⟨969238882019449722637687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1292318509359266296850249 969238882019449722637687)
              ·
                refine ⟨1453858323029174583956531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 969238882019449722637687 1453858323029174583956531)
                ·
                  refine ⟨2180787484543761875934797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1453858323029174583956531 2180787484543761875934797)
                  ·
                    refine ⟨817795306703910703475549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2180787484543761875934797 817795306703910703475549)
                    ·
                      refine ⟨306673240013966513803331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 817795306703910703475549 306673240013966513803331)
                      ·
                        rfl

theorem cell23_597244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_597244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597244 prefixEnd_597244 := by exact prefixLift 597244
  have htrace : WordTrace (prefixWord ++ tailWord_597244) baseStart_597244 baseEnd_597244 := by
    simpa [prefixWord, tailWord_597244, baseEnd_597244] using wordTrace_append hprefix tailTrace_597244
  have hstable : (prefixWord ++ tailWord_597244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597244).length < 2 ^ (prefixWord ++ tailWord_597244).sum := by decide
  have hdescent : baseEnd_597244 < baseStart_597244 := by decide
  rcases family_descends (prefixWord ++ tailWord_597244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597277 : List Nat := [1, 4, 2, 3, 1, 1, 1, 2, 2, 6]
def baseStart_597277 : Nat := 118140960795 + 597277 * 2 ^ 59
def prefixEnd_597277 : Nat := 4983230072969 + 3 ^ 40 * 597277 * 2
def baseEnd_597277 : Nat := 102230061625188294896893

theorem tailTrace_597277 : CollatzResearch.WordTrace tailWord_597277 prefixEnd_597277 102230061625188294896893 := by
  unfold tailWord_597277
  simp only [CollatzResearch.WordTrace]
  refine ⟨21784481857174910635534085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14522987904783273757022723 21784481857174910635534085)
  ·
    refine ⟨4084590348220295744162641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21784481857174910635534085 4084590348220295744162641)
    ·
      refine ⟨3063442761165221808121981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4084590348220295744162641 3063442761165221808121981)
      ·
        refine ⟨1148791035436958178045743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3063442761165221808121981 1148791035436958178045743)
        ·
          refine ⟨1723186553155437267068615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1148791035436958178045743 1723186553155437267068615)
          ·
            refine ⟨2584779829733155900602923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1723186553155437267068615 2584779829733155900602923)
            ·
              refine ⟨3877169744599733850904385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2584779829733155900602923 3877169744599733850904385)
              ·
                refine ⟨2907877308449800388178289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3877169744599733850904385 2907877308449800388178289)
                ·
                  refine ⟨2180907981337350291133717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2907877308449800388178289 2180907981337350291133717)
                  ·
                    refine ⟨102230061625188294896893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2180907981337350291133717 102230061625188294896893)
                    ·
                      rfl

theorem cell23_597277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_597277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597277 prefixEnd_597277 := by exact prefixLift 597277
  have htrace : WordTrace (prefixWord ++ tailWord_597277) baseStart_597277 baseEnd_597277 := by
    simpa [prefixWord, tailWord_597277, baseEnd_597277] using wordTrace_append hprefix tailTrace_597277
  have hstable : (prefixWord ++ tailWord_597277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597277).length < 2 ^ (prefixWord ++ tailWord_597277).sum := by decide
  have hdescent : baseEnd_597277 < baseStart_597277 := by decide
  rcases family_descends (prefixWord ++ tailWord_597277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597278 : List Nat := [4, 3, 2, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_597278 : Nat := 118140960795 + 597278 * 2 ^ 59
def prefixEnd_597278 : Nat := 4983230072969 + 3 ^ 40 * 597278 * 2
def baseEnd_597278 : Nat := 306690698356219380778175

theorem tailTrace_597278 : CollatzResearch.WordTrace tailWord_597278 prefixEnd_597278 306690698356219380778175 := by
  unfold tailWord_597278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2723064791271410975790061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14523012220114191870880325 2723064791271410975790061)
  ·
    refine ⟨1021149296726779115921273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2723064791271410975790061 1021149296726779115921273)
    ·
      refine ⟨765861972545084336940955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1021149296726779115921273 765861972545084336940955)
      ·
        refine ⟨1148792958817626505411433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 765861972545084336940955 1148792958817626505411433)
        ·
          refine ⟨861594719113219879058575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1148792958817626505411433 861594719113219879058575)
          ·
            refine ⟨1292392078669829818587863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 861594719113219879058575 1292392078669829818587863)
            ·
              refine ⟨1938588118004744727881795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1292392078669829818587863 1938588118004744727881795)
              ·
                refine ⟨2907882177007117091822693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1938588118004744727881795 2907882177007117091822693)
                ·
                  refine ⟨545227908188834454716755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2907882177007117091822693 545227908188834454716755)
                  ·
                    refine ⟨817841862283251682075133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 545227908188834454716755 817841862283251682075133)
                    ·
                      refine ⟨306690698356219380778175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 817841862283251682075133 306690698356219380778175)
                      ·
                        rfl

theorem cell23_597278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_597278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597278 prefixEnd_597278 := by exact prefixLift 597278
  have htrace : WordTrace (prefixWord ++ tailWord_597278) baseStart_597278 baseEnd_597278 := by
    simpa [prefixWord, tailWord_597278, baseEnd_597278] using wordTrace_append hprefix tailTrace_597278
  have hstable : (prefixWord ++ tailWord_597278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597278).length < 2 ^ (prefixWord ++ tailWord_597278).sum := by decide
  have hdescent : baseEnd_597278 < baseStart_597278 := by decide
  rcases family_descends (prefixWord ++ tailWord_597278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597297 : List Nat := [1, 2, 2, 3, 3, 1, 2, 1, 2, 2, 4]
def baseStart_597297 : Nat := 118140960795 + 597297 * 2 ^ 59
def prefixEnd_597297 : Nat := 4983230072969 + 3 ^ 40 * 597297 * 2
def baseEnd_597297 : Nat := 306700454488654806440587

theorem tailTrace_597297 : CollatzResearch.WordTrace tailWord_597297 prefixEnd_597297 306700454488654806440587 := by
  unfold tailWord_597297
  simp only [CollatzResearch.WordTrace]
  refine ⟨21785211317102454051262145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14523474211401636034174763 21785211317102454051262145)
  ·
    refine ⟨16338908487826840538446609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21785211317102454051262145 16338908487826840538446609)
    ·
      refine ⟨12254181365870130403834957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16338908487826840538446609 12254181365870130403834957)
      ·
        refine ⟨4595318012201298901438109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12254181365870130403834957 4595318012201298901438109)
        ·
          refine ⟨1723244254575487088039291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4595318012201298901438109 1723244254575487088039291)
          ·
            refine ⟨2584866381863230632058937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1723244254575487088039291 2584866381863230632058937)
            ·
              refine ⟨1938649786397422974044203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2584866381863230632058937 1938649786397422974044203)
              ·
                refine ⟨2907974679596134461066305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1938649786397422974044203 2907974679596134461066305)
                ·
                  refine ⟨2180981009697100845799729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2907974679596134461066305 2180981009697100845799729)
                  ·
                    refine ⟨1635735757272825634349797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2180981009697100845799729 1635735757272825634349797)
                    ·
                      refine ⟨306700454488654806440587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1635735757272825634349797 306700454488654806440587)
                      ·
                        rfl

theorem cell23_597297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_597297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597297 prefixEnd_597297 := by exact prefixLift 597297
  have htrace : WordTrace (prefixWord ++ tailWord_597297) baseStart_597297 baseEnd_597297 := by
    simpa [prefixWord, tailWord_597297, baseEnd_597297] using wordTrace_append hprefix tailTrace_597297
  have hstable : (prefixWord ++ tailWord_597297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597297).length < 2 ^ (prefixWord ++ tailWord_597297).sum := by decide
  have hdescent : baseEnd_597297 < baseStart_597297 := by decide
  rcases family_descends (prefixWord ++ tailWord_597297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597301 : List Nat := [1, 3, 3, 1, 2, 4, 1, 1, 1, 4, 2]
def baseStart_597301 : Nat := 118140960795 + 597301 * 2 ^ 59
def prefixEnd_597301 : Nat := 4983230072969 + 3 ^ 40 * 597301 * 2
def baseEnd_597301 : Nat := 306702508411272790790569

theorem tailTrace_597301 : CollatzResearch.WordTrace tailWord_597301 prefixEnd_597301 306702508411272790790569 := by
  unfold tailWord_597301
  simp only [CollatzResearch.WordTrace]
  refine ⟨21785357209087962734407757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14523571472725308489605171 21785357209087962734407757)
  ·
    refine ⟨8169508953407986025402909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21785357209087962734407757 8169508953407986025402909)
    ·
      refine ⟨3063565857527994759526091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8169508953407986025402909 3063565857527994759526091)
      ·
        refine ⟨4595348786291992139289137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3063565857527994759526091 4595348786291992139289137)
        ·
          refine ⟨3446511589718994104466853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4595348786291992139289137 3446511589718994104466853)
          ·
            refine ⟨646220923072311394587535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3446511589718994104466853 646220923072311394587535)
            ·
              refine ⟨969331384608467091881303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646220923072311394587535 969331384608467091881303)
              ·
                refine ⟨1453997076912700637821955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 969331384608467091881303 1453997076912700637821955)
                ·
                  refine ⟨2180995615369050956732933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1453997076912700637821955 2180995615369050956732933)
                  ·
                    refine ⟨408936677881697054387425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2180995615369050956732933 408936677881697054387425)
                    ·
                      refine ⟨306702508411272790790569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 408936677881697054387425 306702508411272790790569)
                      ·
                        rfl

theorem cell23_597301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_597301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597301 prefixEnd_597301 := by exact prefixLift 597301
  have htrace : WordTrace (prefixWord ++ tailWord_597301) baseStart_597301 baseEnd_597301 := by
    simpa [prefixWord, tailWord_597301, baseEnd_597301] using wordTrace_append hprefix tailTrace_597301
  have hstable : (prefixWord ++ tailWord_597301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597301).length < 2 ^ (prefixWord ++ tailWord_597301).sum := by decide
  have hdescent : baseEnd_597301 < baseStart_597301 := by decide
  rcases family_descends (prefixWord ++ tailWord_597301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597324 : List Nat := [2, 2, 1, 3, 2, 2, 3, 3, 5]
def baseStart_597324 : Nat := 118140960795 + 597324 * 2 ^ 59
def prefixEnd_597324 : Nat := 4983230072969 + 3 ^ 40 * 597324 * 2
def baseEnd_597324 : Nat := 34079368718480688978107

theorem tailTrace_597324 : CollatzResearch.WordTrace tailWord_597324 prefixEnd_597324 34079368718480688978107 := by
  unfold tailWord_597324
  simp only [CollatzResearch.WordTrace]
  refine ⟨10893098044002318831247513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14524130725336425108330017 10893098044002318831247513)
  ·
    refine ⟨8169823533001739123435635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10893098044002318831247513 8169823533001739123435635)
    ·
      refine ⟨12254735299502608685153453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8169823533001739123435635 12254735299502608685153453)
      ·
        refine ⟨4595525737313478256932545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12254735299502608685153453 4595525737313478256932545)
        ·
          refine ⟨3446644302985108692699409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4595525737313478256932545 3446644302985108692699409)
          ·
            refine ⟨2584983227238831519524557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3446644302985108692699409 2584983227238831519524557)
            ·
              refine ⟨969368710214561819821709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2584983227238831519524557 969368710214561819821709)
              ·
                refine ⟨363513266330460682433141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 969368710214561819821709 363513266330460682433141)
                ·
                  refine ⟨34079368718480688978107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 363513266330460682433141 34079368718480688978107)
                  ·
                    rfl

theorem cell23_597324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 5].length) (baseStart_597324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597324 prefixEnd_597324 := by exact prefixLift 597324
  have htrace : WordTrace (prefixWord ++ tailWord_597324) baseStart_597324 baseEnd_597324 := by
    simpa [prefixWord, tailWord_597324, baseEnd_597324] using wordTrace_append hprefix tailTrace_597324
  have hstable : (prefixWord ++ tailWord_597324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597324).length < 2 ^ (prefixWord ++ tailWord_597324).sum := by decide
  have hdescent : baseEnd_597324 < baseStart_597324 := by decide
  rcases family_descends (prefixWord ++ tailWord_597324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597347 : List Nat := [1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 5]
def baseStart_597347 : Nat := 118140960795 + 597347 * 2 ^ 59
def prefixEnd_597347 : Nat := 4983230072969 + 3 ^ 40 * 597347 * 2
def baseEnd_597347 : Nat := 306726128521379610815357

theorem tailTrace_597347 : CollatzResearch.WordTrace tailWord_597347 prefixEnd_597347 306726128521379610815357 := by
  unfold tailWord_597347
  simp only [CollatzResearch.WordTrace]
  refine ⟨21787034966921312590582295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14524689977947541727054863 21787034966921312590582295)
  ·
    refine ⟨32680552450381968885873443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21787034966921312590582295 32680552450381968885873443)
    ·
      refine ⟨49020828675572953328810165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32680552450381968885873443 49020828675572953328810165)
      ·
        refine ⟨4595702688334964374575953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49020828675572953328810165 4595702688334964374575953)
        ·
          refine ⟨3446777016251223280931965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4595702688334964374575953 3446777016251223280931965)
          ·
            refine ⟨1292541381094208730349487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3446777016251223280931965 1292541381094208730349487)
            ·
              refine ⟨1938812071641313095524231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1292541381094208730349487 1938812071641313095524231)
              ·
                refine ⟨2908218107461969643286347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1938812071641313095524231 2908218107461969643286347)
                ·
                  refine ⟨4362327161192954464929521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2908218107461969643286347 4362327161192954464929521)
                  ·
                    refine ⟨3271745370894715848697141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4362327161192954464929521 3271745370894715848697141)
                    ·
                      refine ⟨306726128521379610815357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3271745370894715848697141 306726128521379610815357)
                      ·
                        rfl

theorem cell23_597347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_597347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597347 prefixEnd_597347 := by exact prefixLift 597347
  have htrace : WordTrace (prefixWord ++ tailWord_597347) baseStart_597347 baseEnd_597347 := by
    simpa [prefixWord, tailWord_597347, baseEnd_597347] using wordTrace_append hprefix tailTrace_597347
  have hstable : (prefixWord ++ tailWord_597347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597347).length < 2 ^ (prefixWord ++ tailWord_597347).sum := by decide
  have hdescent : baseEnd_597347 < baseStart_597347 := by decide
  rcases family_descends (prefixWord ++ tailWord_597347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597352 : List Nat := [2, 1, 4, 2, 4, 1, 2, 1, 2, 2, 2]
def baseStart_597352 : Nat := 118140960795 + 597352 * 2 ^ 59
def prefixEnd_597352 : Nat := 4983230072969 + 3 ^ 40 * 597352 * 2
def baseEnd_597352 : Nat := 306728695924652091252835

theorem tailTrace_597352 : CollatzResearch.WordTrace tailWord_597352 prefixEnd_597352 306728695924652091252835 := by
  unfold tailWord_597352
  simp only [CollatzResearch.WordTrace]
  refine ⟨10893608665951599222257155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14524811554602132296342873 10893608665951599222257155)
  ·
    refine ⟨16340412998927398833385733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10893608665951599222257155 16340412998927398833385733)
    ·
      refine ⟨3063827437298887281259825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16340412998927398833385733 3063827437298887281259825)
      ·
        refine ⟨2297870577974165460944869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3063827437298887281259825 2297870577974165460944869)
        ·
          refine ⟨430850733370156023927163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2297870577974165460944869 430850733370156023927163)
          ·
            refine ⟨646276100055234035890745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430850733370156023927163 646276100055234035890745)
            ·
              refine ⟨484707075041425526918059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 646276100055234035890745 484707075041425526918059)
              ·
                refine ⟨727060612562138290377089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 484707075041425526918059 727060612562138290377089)
                ·
                  refine ⟨545295459421603717782817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 727060612562138290377089 545295459421603717782817)
                  ·
                    refine ⟨408971594566202788337113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 545295459421603717782817 408971594566202788337113)
                    ·
                      refine ⟨306728695924652091252835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 408971594566202788337113 306728695924652091252835)
                      ·
                        rfl

theorem cell23_597352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_597352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597352 prefixEnd_597352 := by exact prefixLift 597352
  have htrace : WordTrace (prefixWord ++ tailWord_597352) baseStart_597352 baseEnd_597352 := by
    simpa [prefixWord, tailWord_597352, baseEnd_597352] using wordTrace_append hprefix tailTrace_597352
  have hstable : (prefixWord ++ tailWord_597352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597352).length < 2 ^ (prefixWord ++ tailWord_597352).sum := by decide
  have hdescent : baseEnd_597352 < baseStart_597352 := by decide
  rcases family_descends (prefixWord ++ tailWord_597352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597367 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 5, 4]
def baseStart_597367 : Nat := 118140960795 + 597367 * 2 ^ 59
def prefixEnd_597367 : Nat := 4983230072969 + 3 ^ 40 * 597367 * 2
def baseEnd_597367 : Nat := 102245466044823177521755

theorem tailTrace_597367 : CollatzResearch.WordTrace tailWord_597367 prefixEnd_597367 102245466044823177521755 := by
  unfold tailWord_597367
  simp only [CollatzResearch.WordTrace]
  refine ⟨21787764426848856006310355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14525176284565904004206903 21787764426848856006310355)
  ·
    refine ⟨32681646640273284009465533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21787764426848856006310355 32681646640273284009465533)
    ·
      refine ⟨12255617490102481503549575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32681646640273284009465533 12255617490102481503549575)
      ·
        refine ⟨18383426235153722255324363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12255617490102481503549575 18383426235153722255324363)
        ·
          refine ⟨27575139352730583382986545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18383426235153722255324363 27575139352730583382986545)
          ·
            refine ⟨20681354514547937537239909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27575139352730583382986545 20681354514547937537239909)
            ·
              refine ⟨3877753971477738288232483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20681354514547937537239909 3877753971477738288232483)
              ·
                refine ⟨5816630957216607432348725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3877753971477738288232483 5816630957216607432348725)
                ·
                  refine ⟨545309152239056946782693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5816630957216607432348725 545309152239056946782693)
                  ·
                    refine ⟨102245466044823177521755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 545309152239056946782693 102245466044823177521755)
                    ·
                      rfl

theorem cell23_597367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 4].length) (baseStart_597367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597367 prefixEnd_597367 := by exact prefixLift 597367
  have htrace : WordTrace (prefixWord ++ tailWord_597367) baseStart_597367 baseEnd_597367 := by
    simpa [prefixWord, tailWord_597367, baseEnd_597367] using wordTrace_append hprefix tailTrace_597367
  have hstable : (prefixWord ++ tailWord_597367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597367).length < 2 ^ (prefixWord ++ tailWord_597367).sum := by decide
  have hdescent : baseEnd_597367 < baseStart_597367 := by decide
  rcases family_descends (prefixWord ++ tailWord_597367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597397 : List Nat := [1, 3, 2, 1, 1, 2, 3, 4, 6]
def baseStart_597397 : Nat := 118140960795 + 597397 * 2 ^ 59
def prefixEnd_597397 : Nat := 4983230072969 + 3 ^ 40 * 597397 * 2
def baseEnd_597397 : Nat := 34083533617122712798903

theorem tailTrace_597397 : CollatzResearch.WordTrace tailWord_597397 prefixEnd_597397 34083533617122712798903 := by
  unfold tailWord_597397
  simp only [CollatzResearch.WordTrace]
  refine ⟨21788858616740171129902445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14525905744493447419934963 21788858616740171129902445)
  ·
    refine ⟨8170821981277564173713417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21788858616740171129902445 8170821981277564173713417)
    ·
      refine ⟨6128116485958173130285063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8170821981277564173713417 6128116485958173130285063)
      ·
        refine ⟨9192174728937259695427595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6128116485958173130285063 9192174728937259695427595)
        ·
          refine ⟨13788262093405889543141393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9192174728937259695427595 13788262093405889543141393)
          ·
            refine ⟨10341196570054417157356045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13788262093405889543141393 10341196570054417157356045)
            ·
              refine ⟨3877948713770406434008517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10341196570054417157356045 3877948713770406434008517)
              ·
                refine ⟨727115383831951206376597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3877948713770406434008517 727115383831951206376597)
                ·
                  refine ⟨34083533617122712798903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 727115383831951206376597 34083533617122712798903)
                  ·
                    rfl

theorem cell23_597397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 6].length) (baseStart_597397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597397 prefixEnd_597397 := by exact prefixLift 597397
  have htrace : WordTrace (prefixWord ++ tailWord_597397) baseStart_597397 baseEnd_597397 := by
    simpa [prefixWord, tailWord_597397, baseEnd_597397] using wordTrace_append hprefix tailTrace_597397
  have hstable : (prefixWord ++ tailWord_597397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597397).length < 2 ^ (prefixWord ++ tailWord_597397).sum := by decide
  have hdescent : baseEnd_597397 < baseStart_597397 := by decide
  rcases family_descends (prefixWord ++ tailWord_597397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597401 : List Nat := [1, 2, 1, 2, 1, 6, 1, 4, 1, 4]
def baseStart_597401 : Nat := 118140960795 + 597401 * 2 ^ 59
def prefixEnd_597401 : Nat := 4983230072969 + 3 ^ 40 * 597401 * 2
def baseEnd_597401 : Nat := 102251285492240799846703

theorem tailTrace_597401 : CollatzResearch.WordTrace tailWord_597401 prefixEnd_597401 102251285492240799846703 := by
  unfold tailWord_597401
  simp only [CollatzResearch.WordTrace]
  refine ⟨21789004508725679813048057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14526003005817119875365371 21789004508725679813048057)
  ·
    refine ⟨16341753381544259859786043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21789004508725679813048057 16341753381544259859786043)
    ·
      refine ⟨24512630072316389789679065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16341753381544259859786043 24512630072316389789679065)
      ·
        refine ⟨18384472554237292342259299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24512630072316389789679065 18384472554237292342259299)
        ·
          refine ⟨27576708831355938513388949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18384472554237292342259299 27576708831355938513388949)
          ·
            refine ⟨1292658226469809617815107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27576708831355938513388949 1292658226469809617815107)
            ·
              refine ⟨1938987339704714426722661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1292658226469809617815107 1938987339704714426722661)
              ·
                refine ⟨363560126194633955010499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1938987339704714426722661 363560126194633955010499)
                ·
                  refine ⟨545340189291950932515749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 363560126194633955010499 545340189291950932515749)
                  ·
                    refine ⟨102251285492240799846703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 545340189291950932515749 102251285492240799846703)
                    ·
                      rfl

theorem cell23_597401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 1, 4].length) (baseStart_597401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597401 prefixEnd_597401 := by exact prefixLift 597401
  have htrace : WordTrace (prefixWord ++ tailWord_597401) baseStart_597401 baseEnd_597401 := by
    simpa [prefixWord, tailWord_597401, baseEnd_597401] using wordTrace_append hprefix tailTrace_597401
  have hstable : (prefixWord ++ tailWord_597401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597401).length < 2 ^ (prefixWord ++ tailWord_597401).sum := by decide
  have hdescent : baseEnd_597401 < baseStart_597401 := by decide
  rcases family_descends (prefixWord ++ tailWord_597401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597501 : List Nat := [1, 4, 1, 1, 1, 4, 2, 3, 1, 2, 3]
def baseStart_597501 : Nat := 118140960795 + 597501 * 2 ^ 59
def prefixEnd_597501 : Nat := 4983230072969 + 3 ^ 40 * 597501 * 2
def baseEnd_597501 : Nat := 306805204542172008289649

theorem tailTrace_597501 : CollatzResearch.WordTrace tailWord_597501 prefixEnd_597501 306805204542172008289649 := by
  unfold tailWord_597501
  simp only [CollatzResearch.WordTrace]
  refine ⟨21792651808363396891688357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14528434538908931261125571 21792651808363396891688357)
  ·
    refine ⟨4086122214068136917191567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21792651808363396891688357 4086122214068136917191567)
    ·
      refine ⟨6129183321102205375787351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4086122214068136917191567 6129183321102205375787351)
      ·
        refine ⟨9193774981653308063681027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6129183321102205375787351 9193774981653308063681027)
        ·
          refine ⟨13790662472479962095521541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9193774981653308063681027 13790662472479962095521541)
          ·
            refine ⟨2585749213589992892910289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13790662472479962095521541 2585749213589992892910289)
            ·
              refine ⟨1939311910192494669682717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2585749213589992892910289 1939311910192494669682717)
              ·
                refine ⟨727241966322185501131019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1939311910192494669682717 727241966322185501131019)
                ·
                  refine ⟨1090862949483278251696529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 727241966322185501131019 1090862949483278251696529)
                  ·
                    refine ⟨818147212112458688772397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1090862949483278251696529 818147212112458688772397)
                    ·
                      refine ⟨306805204542172008289649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 818147212112458688772397 306805204542172008289649)
                      ·
                        rfl

theorem cell23_597501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_597501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597501 prefixEnd_597501 := by exact prefixLift 597501
  have htrace : WordTrace (prefixWord ++ tailWord_597501) baseStart_597501 baseEnd_597501 := by
    simpa [prefixWord, tailWord_597501, baseEnd_597501] using wordTrace_append hprefix tailTrace_597501
  have hstable : (prefixWord ++ tailWord_597501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597501).length < 2 ^ (prefixWord ++ tailWord_597501).sum := by decide
  have hdescent : baseEnd_597501 < baseStart_597501 := by decide
  rcases family_descends (prefixWord ++ tailWord_597501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597515 : List Nat := [1, 1, 1, 1, 8, 2, 1, 1, 3, 2, 2]
def baseStart_597515 : Nat := 118140960795 + 597515 * 2 ^ 59
def prefixEnd_597515 : Nat := 4983230072969 + 3 ^ 40 * 597515 * 2
def baseEnd_597515 : Nat := 306812393271334953514585

theorem tailTrace_597515 : CollatzResearch.WordTrace tailWord_597515 prefixEnd_597515 306812393271334953514585 := by
  unfold tailWord_597515
  simp only [CollatzResearch.WordTrace]
  refine ⟨21793162430312677282697999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14528774953541784855131999 21793162430312677282697999)
  ·
    refine ⟨32689743645469015924046999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21793162430312677282697999 32689743645469015924046999)
    ·
      refine ⟨49034615468203523886070499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32689743645469015924046999 49034615468203523886070499)
      ·
        refine ⟨73551923202305285829105749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49034615468203523886070499 73551923202305285829105749)
        ·
          refine ⟨861936600027015068309833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 73551923202305285829105749 861936600027015068309833)
          ·
            refine ⟨646452450020261301232375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 861936600027015068309833 646452450020261301232375)
            ·
              refine ⟨969678675030391951848563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646452450020261301232375 969678675030391951848563)
              ·
                refine ⟨1454518012545587927772845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 969678675030391951848563 1454518012545587927772845)
                ·
                  refine ⟨545444254704595472914817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1454518012545587927772845 545444254704595472914817)
                  ·
                    refine ⟨409083191028446604686113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 545444254704595472914817 409083191028446604686113)
                    ·
                      refine ⟨306812393271334953514585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 409083191028446604686113 306812393271334953514585)
                      ·
                        rfl

theorem cell23_597515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 2, 2].length) (baseStart_597515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597515 prefixEnd_597515 := by exact prefixLift 597515
  have htrace : WordTrace (prefixWord ++ tailWord_597515) baseStart_597515 baseEnd_597515 := by
    simpa [prefixWord, tailWord_597515, baseEnd_597515] using wordTrace_append hprefix tailTrace_597515
  have hstable : (prefixWord ++ tailWord_597515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597515).length < 2 ^ (prefixWord ++ tailWord_597515).sum := by decide
  have hdescent : baseEnd_597515 < baseStart_597515 := by decide
  rcases family_descends (prefixWord ++ tailWord_597515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597547 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 6, 6]
def baseStart_597547 : Nat := 118140960795 + 597547 * 2 ^ 59
def prefixEnd_597547 : Nat := 4983230072969 + 3 ^ 40 * 597547 * 2
def baseEnd_597547 : Nat := 102276274884092942771479

theorem tailTrace_597547 : CollatzResearch.WordTrace tailWord_597547 prefixEnd_597547 102276274884092942771479 := by
  unfold tailWord_597547
  simp only [CollatzResearch.WordTrace]
  refine ⟨21794329566196746747862895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14529553044131164498575263 21794329566196746747862895)
  ·
    refine ⟨32691494349295120121794343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21794329566196746747862895 32691494349295120121794343)
    ·
      refine ⟨49037241523942680182691515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32691494349295120121794343 49037241523942680182691515)
      ·
        refine ⟨73555862285914020274037273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49037241523942680182691515 73555862285914020274037273)
        ·
          refine ⟨55166896714435515205527955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73555862285914020274037273 55166896714435515205527955)
          ·
            refine ⟨82750345071653272808291933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55166896714435515205527955 82750345071653272808291933)
            ·
              refine ⟨31031379401869977303109475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82750345071653272808291933 31031379401869977303109475)
              ·
                refine ⟨46547069102804965954664213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31031379401869977303109475 46547069102804965954664213)
                ·
                  refine ⟨2181893864193982779124885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46547069102804965954664213 2181893864193982779124885)
                  ·
                    refine ⟨102276274884092942771479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2181893864193982779124885 102276274884092942771479)
                    ·
                      rfl

theorem cell23_597547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 6].length) (baseStart_597547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597547 prefixEnd_597547 := by exact prefixLift 597547
  have htrace : WordTrace (prefixWord ++ tailWord_597547) baseStart_597547 baseEnd_597547 := by
    simpa [prefixWord, tailWord_597547, baseEnd_597547] using wordTrace_append hprefix tailTrace_597547
  have hstable : (prefixWord ++ tailWord_597547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597547).length < 2 ^ (prefixWord ++ tailWord_597547).sum := by decide
  have hdescent : baseEnd_597547 < baseStart_597547 := by decide
  rcases family_descends (prefixWord ++ tailWord_597547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597565 : List Nat := [1, 4, 1, 3, 3, 1, 2, 2, 2, 1, 3]
def baseStart_597565 : Nat := 118140960795 + 597565 * 2 ^ 59
def prefixEnd_597565 : Nat := 4983230072969 + 3 ^ 40 * 597565 * 2
def baseEnd_597565 : Nat := 306838067304059757889355

theorem tailTrace_597565 : CollatzResearch.WordTrace tailWord_597565 prefixEnd_597565 306838067304059757889355 := by
  unfold tailWord_597565
  simp only [CollatzResearch.WordTrace]
  refine ⟨21794986080131535822018149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14529990720087690548012099 21794986080131535822018149)
  ·
    refine ⟨4086559890024662966628403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21794986080131535822018149 4086559890024662966628403)
    ·
      refine ⟨6129839835036994449942605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4086559890024662966628403 6129839835036994449942605)
      ·
        refine ⟨2298689938138872918728477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6129839835036994449942605 2298689938138872918728477)
        ·
          refine ⟨862008726802077344523179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2298689938138872918728477 862008726802077344523179)
          ·
            refine ⟨1293013090203116016784769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 862008726802077344523179 1293013090203116016784769)
            ·
              refine ⟨969759817652337012588577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1293013090203116016784769 969759817652337012588577)
              ·
                refine ⟨727319863239252759441433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 969759817652337012588577 727319863239252759441433)
                ·
                  refine ⟨545489897429439569581075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 727319863239252759441433 545489897429439569581075)
                  ·
                    refine ⟨818234846144159354371613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 545489897429439569581075 818234846144159354371613)
                    ·
                      refine ⟨306838067304059757889355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 818234846144159354371613 306838067304059757889355)
                      ·
                        rfl

theorem cell23_597565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_597565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597565 prefixEnd_597565 := by exact prefixLift 597565
  have htrace : WordTrace (prefixWord ++ tailWord_597565) baseStart_597565 baseEnd_597565 := by
    simpa [prefixWord, tailWord_597565, baseEnd_597565] using wordTrace_append hprefix tailTrace_597565
  have hstable : (prefixWord ++ tailWord_597565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597565).length < 2 ^ (prefixWord ++ tailWord_597565).sum := by decide
  have hdescent : baseEnd_597565 < baseStart_597565 := by decide
  rcases family_descends (prefixWord ++ tailWord_597565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597577 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 11]
def baseStart_597577 : Nat := 118140960795 + 597577 * 2 ^ 59
def prefixEnd_597577 : Nat := 4983230072969 + 3 ^ 40 * 597577 * 2
def baseEnd_597577 : Nat := 34093803230212634548811

theorem tailTrace_597577 : CollatzResearch.WordTrace tailWord_597577 prefixEnd_597577 34093803230212634548811 := by
  unfold tailWord_597577
  simp only [CollatzResearch.WordTrace]
  refine ⟨21795423756088061871454985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14530282504058707914303323 21795423756088061871454985)
  ·
    refine ⟨16346567817066046403591239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21795423756088061871454985 16346567817066046403591239)
    ·
      refine ⟨24519851725599069605386859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16346567817066046403591239 24519851725599069605386859)
      ·
        refine ⟨36779777588398604408080289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24519851725599069605386859 36779777588398604408080289)
        ·
          refine ⟨27584833191298953306060217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36779777588398604408080289 27584833191298953306060217)
          ·
            refine ⟨20688624893474214979545163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27584833191298953306060217 20688624893474214979545163)
            ·
              refine ⟨31032937340211322469317745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20688624893474214979545163 31032937340211322469317745)
              ·
                refine ⟨23274703005158491851988309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31032937340211322469317745 23274703005158491851988309)
                ·
                  refine ⟨34093803230212634548811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 23274703005158491851988309 34093803230212634548811)
                  ·
                    rfl

theorem cell23_597577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 11].length) (baseStart_597577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597577 prefixEnd_597577 := by exact prefixLift 597577
  have htrace : WordTrace (prefixWord ++ tailWord_597577) baseStart_597577 baseEnd_597577 := by
    simpa [prefixWord, tailWord_597577, baseEnd_597577] using wordTrace_append hprefix tailTrace_597577
  have hstable : (prefixWord ++ tailWord_597577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597577).length < 2 ^ (prefixWord ++ tailWord_597577).sum := by decide
  have hdescent : baseEnd_597577 < baseStart_597577 := by decide
  rcases family_descends (prefixWord ++ tailWord_597577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597584 : List Nat := [2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 4]
def baseStart_597584 : Nat := 118140960795 + 597584 * 2 ^ 59
def prefixEnd_597584 : Nat := 4983230072969 + 3 ^ 40 * 597584 * 2
def baseEnd_597584 : Nat := 306847823436495183551767

theorem tailTrace_597584 : CollatzResearch.WordTrace tailWord_597584 prefixEnd_597584 306847823436495183551767 := by
  unfold tailWord_597584
  simp only [CollatzResearch.WordTrace]
  refine ⟨10897839533531351033479903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14530452711375134711306537 10897839533531351033479903)
  ·
    refine ⟨16346759300297026550219855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10897839533531351033479903 16346759300297026550219855)
    ·
      refine ⟨24520138950445539825329783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16346759300297026550219855 24520138950445539825329783)
      ·
        refine ⟨36780208425668309737994675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24520138950445539825329783 36780208425668309737994675)
        ·
          refine ⟨55170312638502464606992013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36780208425668309737994675 55170312638502464606992013)
          ·
            refine ⟨20688867239438424227622005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55170312638502464606992013 20688867239438424227622005)
            ·
              refine ⟨1939581303697352271339563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20688867239438424227622005 1939581303697352271339563)
              ·
                refine ⟨2909371955546028407009345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1939581303697352271339563 2909371955546028407009345)
                ·
                  refine ⟨2182028966659521305257009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2909371955546028407009345 2182028966659521305257009)
                  ·
                    refine ⟨1636521724994640978942757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2182028966659521305257009 1636521724994640978942757)
                    ·
                      refine ⟨306847823436495183551767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1636521724994640978942757 306847823436495183551767)
                      ·
                        rfl

theorem cell23_597584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 4].length) (baseStart_597584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597584 prefixEnd_597584 := by exact prefixLift 597584
  have htrace : WordTrace (prefixWord ++ tailWord_597584) baseStart_597584 baseEnd_597584 := by
    simpa [prefixWord, tailWord_597584, baseEnd_597584] using wordTrace_append hprefix tailTrace_597584
  have hstable : (prefixWord ++ tailWord_597584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597584).length < 2 ^ (prefixWord ++ tailWord_597584).sum := by decide
  have hdescent : baseEnd_597584 < baseStart_597584 := by decide
  rcases family_descends (prefixWord ++ tailWord_597584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597587 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 9]
def baseStart_597587 : Nat := 118140960795 + 597587 * 2 ^ 59
def prefixEnd_597587 : Nat := 4983230072969 + 3 ^ 40 * 597587 * 2
def baseEnd_597587 : Nat := 306849363878458671814253

theorem tailTrace_597587 : CollatzResearch.WordTrace tailWord_597587 prefixEnd_597587 306849363878458671814253 := by
  unfold tailWord_597587
  simp only [CollatzResearch.WordTrace]
  refine ⟨21795788486051833579319015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14530525657367889052879343 21795788486051833579319015)
  ·
    refine ⟨32693682729077750368978523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21795788486051833579319015 32693682729077750368978523)
    ·
      refine ⟨49040524093616625553467785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32693682729077750368978523 49040524093616625553467785)
      ·
        refine ⟨36780393070212469165100839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49040524093616625553467785 36780393070212469165100839)
        ·
          refine ⟨55170589605318703747651259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36780393070212469165100839 55170589605318703747651259)
          ·
            refine ⟨82755884407978055621476889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55170589605318703747651259 82755884407978055621476889)
            ·
              refine ⟨62066913305983541716107667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82755884407978055621476889 62066913305983541716107667)
              ·
                refine ⟨93100369958975312574161501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62066913305983541716107667 93100369958975312574161501)
                ·
                  refine ⟨34912638734615742215310563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93100369958975312574161501 34912638734615742215310563)
                  ·
                    refine ⟨52368958101923613322965845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34912638734615742215310563 52368958101923613322965845)
                    ·
                      refine ⟨306849363878458671814253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 52368958101923613322965845 306849363878458671814253)
                      ·
                        rfl

theorem cell23_597587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_597587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597587 prefixEnd_597587 := by exact prefixLift 597587
  have htrace : WordTrace (prefixWord ++ tailWord_597587) baseStart_597587 baseEnd_597587 := by
    simpa [prefixWord, tailWord_597587, baseEnd_597587] using wordTrace_append hprefix tailTrace_597587
  have hstable : (prefixWord ++ tailWord_597587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597587).length < 2 ^ (prefixWord ++ tailWord_597587).sum := by decide
  have hdescent : baseEnd_597587 < baseStart_597587 := by decide
  rcases family_descends (prefixWord ++ tailWord_597587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597588 : List Nat := [2, 4, 1, 1, 1, 2, 4, 1, 1, 4, 2]
def baseStart_597588 : Nat := 118140960795 + 597588 * 2 ^ 59
def prefixEnd_597588 : Nat := 4983230072969 + 3 ^ 40 * 597588 * 2
def baseEnd_597588 : Nat := 306849877359113167901749

theorem tailTrace_597588 : CollatzResearch.WordTrace tailWord_597588 prefixEnd_597588 306849877359113167901749 := by
  unfold tailWord_597588
  simp only [CollatzResearch.WordTrace]
  refine ⟨10897912479524105375052709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14530549972698807166736945 10897912479524105375052709)
  ·
    refine ⟨2043358589910769757822383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10897912479524105375052709 2043358589910769757822383)
    ·
      refine ⟨3065037884866154636733575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2043358589910769757822383 3065037884866154636733575)
      ·
        refine ⟨4597556827299231955100363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3065037884866154636733575 4597556827299231955100363)
        ·
          refine ⟨6896335240948847932650545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4597556827299231955100363 6896335240948847932650545)
          ·
            refine ⟨5172251430711635949487909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6896335240948847932650545 5172251430711635949487909)
            ·
              refine ⟨969797143258431740528983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5172251430711635949487909 969797143258431740528983)
              ·
                refine ⟨1454695714887647610793475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 969797143258431740528983 1454695714887647610793475)
                ·
                  refine ⟨2182043572331471416190213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1454695714887647610793475 2182043572331471416190213)
                  ·
                    refine ⟨409133169812150890535665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2182043572331471416190213 409133169812150890535665)
                    ·
                      refine ⟨306849877359113167901749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 409133169812150890535665 306849877359113167901749)
                      ·
                        rfl

theorem cell23_597588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_597588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597588 prefixEnd_597588 := by exact prefixLift 597588
  have htrace : WordTrace (prefixWord ++ tailWord_597588) baseStart_597588 baseEnd_597588 := by
    simpa [prefixWord, tailWord_597588, baseEnd_597588] using wordTrace_append hprefix tailTrace_597588
  have hstable : (prefixWord ++ tailWord_597588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597588).length < 2 ^ (prefixWord ++ tailWord_597588).sum := by decide
  have hdescent : baseEnd_597588 < baseStart_597588 := by decide
  rcases family_descends (prefixWord ++ tailWord_597588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597622 : List Nat := [5, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2]
def baseStart_597622 : Nat := 118140960795 + 597622 * 2 ^ 59
def prefixEnd_597622 : Nat := 4983230072969 + 3 ^ 40 * 597622 * 2
def baseEnd_597622 : Nat := 306867335701366034876593

theorem tailTrace_597622 : CollatzResearch.WordTrace tailWord_597622 prefixEnd_597622 306867335701366034876593 := by
  unfold tailWord_597622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1362316565057814659802695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14531376693950023037895413 1362316565057814659802695)
  ·
    refine ⟨2043474847586721989704043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1362316565057814659802695 2043474847586721989704043)
    ·
      refine ⟨3065212271380082984556065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2043474847586721989704043 3065212271380082984556065)
      ·
        refine ⟨2298909203535062238417049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3065212271380082984556065 2298909203535062238417049)
        ·
          refine ⟨1724181902651296678812787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2298909203535062238417049 1724181902651296678812787)
          ·
            refine ⟨2586272853976945018219181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1724181902651296678812787 2586272853976945018219181)
            ·
              refine ⟨969852320241354381832193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2586272853976945018219181 969852320241354381832193)
              ·
                refine ⟨727389240181015786374145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 969852320241354381832193 727389240181015786374145)
                ·
                  refine ⟨545541930135761839780609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 727389240181015786374145 545541930135761839780609)
                  ·
                    refine ⟨409156447601821379835457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 545541930135761839780609 409156447601821379835457)
                    ·
                      refine ⟨306867335701366034876593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 409156447601821379835457 306867335701366034876593)
                      ·
                        rfl

theorem cell23_597622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_597622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597622 prefixEnd_597622 := by exact prefixLift 597622
  have htrace : WordTrace (prefixWord ++ tailWord_597622) baseStart_597622 baseEnd_597622 := by
    simpa [prefixWord, tailWord_597622, baseEnd_597622] using wordTrace_append hprefix tailTrace_597622
  have hstable : (prefixWord ++ tailWord_597622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597622).length < 2 ^ (prefixWord ++ tailWord_597622).sum := by decide
  have hdescent : baseEnd_597622 < baseStart_597622 := by decide
  rcases family_descends (prefixWord ++ tailWord_597622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597644 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 3, 3, 4]
def baseStart_597644 : Nat := 118140960795 + 597644 * 2 ^ 59
def prefixEnd_597644 : Nat := 4983230072969 + 3 ^ 40 * 597644 * 2
def baseEnd_597644 : Nat := 306878632275764948801491

theorem tailTrace_597644 : CollatzResearch.WordTrace tailWord_597644 prefixEnd_597644 306878632275764948801491 := by
  unfold tailWord_597644
  simp only [CollatzResearch.WordTrace]
  refine ⟨10898933723422666157071993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14531911631230221542762657 10898933723422666157071993)
  ·
    refine ⟨8174200292566999617803995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10898933723422666157071993 8174200292566999617803995)
    ·
      refine ⟨12261300438850499426705993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8174200292566999617803995 12261300438850499426705993)
      ·
        refine ⟨9195975329137874570029495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12261300438850499426705993 9195975329137874570029495)
        ·
          refine ⟨13793962993706811855044243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9195975329137874570029495 13793962993706811855044243)
          ·
            refine ⟨20690944490560217782566365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13793962993706811855044243 20690944490560217782566365)
            ·
              refine ⟨7759104183960081668462387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20690944490560217782566365 7759104183960081668462387)
              ·
                refine ⟨11638656275940122502693581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7759104183960081668462387 11638656275940122502693581)
                ·
                  refine ⟨4364496103477545938510093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11638656275940122502693581 4364496103477545938510093)
                  ·
                    refine ⟨1636686038804079726941285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4364496103477545938510093 1636686038804079726941285)
                    ·
                      refine ⟨306878632275764948801491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1636686038804079726941285 306878632275764948801491)
                      ·
                        rfl

theorem cell23_597644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_597644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597644 prefixEnd_597644 := by exact prefixLift 597644
  have htrace : WordTrace (prefixWord ++ tailWord_597644) baseStart_597644 baseEnd_597644 := by
    simpa [prefixWord, tailWord_597644, baseEnd_597644] using wordTrace_append hprefix tailTrace_597644
  have hstable : (prefixWord ++ tailWord_597644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597644).length < 2 ^ (prefixWord ++ tailWord_597644).sum := by decide
  have hdescent : baseEnd_597644 < baseStart_597644 := by decide
  rcases family_descends (prefixWord ++ tailWord_597644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597661 : List Nat := [1, 4, 2, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_597661 : Nat := 118140960795 + 597661 * 2 ^ 59
def prefixEnd_597661 : Nat := 4983230072969 + 3 ^ 40 * 597661 * 2
def baseEnd_597661 : Nat := 306887361446891382288913

theorem tailTrace_597661 : CollatzResearch.WordTrace tailWord_597661 prefixEnd_597661 306887361446891382288913 := by
  unfold tailWord_597661
  simp only [CollatzResearch.WordTrace]
  refine ⟨21798487487783744217512837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14532324991855829478341891 21798487487783744217512837)
  ·
    refine ⟨4087216403959452040783657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21798487487783744217512837 4087216403959452040783657)
    ·
      refine ⟨3065412302969589030587743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4087216403959452040783657 3065412302969589030587743)
      ·
        refine ⟨4598118454454383545881615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3065412302969589030587743 4598118454454383545881615)
        ·
          refine ⟨6897177681681575318822423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4598118454454383545881615 6897177681681575318822423)
          ·
            refine ⟨10345766522522362978233635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6897177681681575318822423 10345766522522362978233635)
            ·
              refine ⟨15518649783783544467350453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10345766522522362978233635 15518649783783544467350453)
              ·
                refine ⟨1454873417229707293814105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15518649783783544467350453 1454873417229707293814105)
                ·
                  refine ⟨1091155062922280470360579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1454873417229707293814105 1091155062922280470360579)
                  ·
                    refine ⟨1636732594383420705540869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1091155062922280470360579 1636732594383420705540869)
                    ·
                      refine ⟨306887361446891382288913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1636732594383420705540869 306887361446891382288913)
                      ·
                        rfl

theorem cell23_597661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_597661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597661 prefixEnd_597661 := by exact prefixLift 597661
  have htrace : WordTrace (prefixWord ++ tailWord_597661) baseStart_597661 baseEnd_597661 := by
    simpa [prefixWord, tailWord_597661, baseEnd_597661] using wordTrace_append hprefix tailTrace_597661
  have hstable : (prefixWord ++ tailWord_597661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597661).length < 2 ^ (prefixWord ++ tailWord_597661).sum := by decide
  have hdescent : baseEnd_597661 < baseStart_597661 := by decide
  rcases family_descends (prefixWord ++ tailWord_597661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597688 : List Nat := [2, 1, 2, 1, 2, 1, 1, 8, 1, 4]
def baseStart_597688 : Nat := 118140960795 + 597688 * 2 ^ 59
def prefixEnd_597688 : Nat := 4983230072969 + 3 ^ 40 * 597688 * 2
def baseEnd_597688 : Nat := 102300408474854258883763

theorem tailTrace_597688 : CollatzResearch.WordTrace tailWord_597688 prefixEnd_597688 102300408474854258883763 := by
  unfold tailWord_597688
  simp only [CollatzResearch.WordTrace]
  refine ⟨10899736129342963914372859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14532981505790618552497145 10899736129342963914372859)
  ·
    refine ⟨16349604194014445871559289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10899736129342963914372859 16349604194014445871559289)
    ·
      refine ⟨12262203145510834403669467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16349604194014445871559289 12262203145510834403669467)
      ·
        refine ⟨18393304718266251605504201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12262203145510834403669467 18393304718266251605504201)
        ·
          refine ⟨13794978538699688704128151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18393304718266251605504201 13794978538699688704128151)
          ·
            refine ⟨20692467808049533056192227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13794978538699688704128151 20692467808049533056192227)
            ·
              refine ⟨31038701712074299584288341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20692467808049533056192227 31038701712074299584288341)
              ·
                refine ⟨363734785688370698253379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 31038701712074299584288341 363734785688370698253379)
                ·
                  refine ⟨545602178532556047380069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 363734785688370698253379 545602178532556047380069)
                  ·
                    refine ⟨102300408474854258883763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 545602178532556047380069 102300408474854258883763)
                    ·
                      rfl

theorem cell23_597688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 1, 4].length) (baseStart_597688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597688 prefixEnd_597688 := by exact prefixLift 597688
  have htrace : WordTrace (prefixWord ++ tailWord_597688) baseStart_597688 baseEnd_597688 := by
    simpa [prefixWord, tailWord_597688, baseEnd_597688] using wordTrace_append hprefix tailTrace_597688
  have hstable : (prefixWord ++ tailWord_597688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597688).length < 2 ^ (prefixWord ++ tailWord_597688).sum := by decide
  have hdescent : baseEnd_597688 < baseStart_597688 := by decide
  rcases family_descends (prefixWord ++ tailWord_597688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597735 : List Nat := [1, 1, 5, 4, 1, 1, 2, 2, 6]
def baseStart_597735 : Nat := 118140960795 + 597735 * 2 ^ 59
def prefixEnd_597735 : Nat := 4983230072969 + 3 ^ 40 * 597735 * 2
def baseEnd_597735 : Nat := 34102817668369343640397

theorem tailTrace_597735 : CollatzResearch.WordTrace tailWord_597735 prefixEnd_597735 34102817668369343640397 := by
  unfold tailWord_597735
  simp only [CollatzResearch.WordTrace]
  refine ⟨21801186489515654855706659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14534124326343769903804439 21801186489515654855706659)
  ·
    refine ⟨32701779734273482283559989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21801186489515654855706659 32701779734273482283559989)
    ·
      refine ⟨3065791850088138964083749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32701779734273482283559989 3065791850088138964083749)
      ·
        refine ⟨574835971891526055765703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3065791850088138964083749 574835971891526055765703)
        ·
          refine ⟨862253957837289083648555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 574835971891526055765703 862253957837289083648555)
          ·
            refine ⟨1293380936755933625472833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 862253957837289083648555 1293380936755933625472833)
            ·
              refine ⟨970035702566950219104625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1293380936755933625472833 970035702566950219104625)
              ·
                refine ⟨727526776925212664328469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 970035702566950219104625 727526776925212664328469)
                ·
                  refine ⟨34102817668369343640397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 727526776925212664328469 34102817668369343640397)
                  ·
                    rfl

theorem cell23_597735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 6].length) (baseStart_597735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597735 prefixEnd_597735 := by exact prefixLift 597735
  have htrace : WordTrace (prefixWord ++ tailWord_597735) baseStart_597735 baseEnd_597735 := by
    simpa [prefixWord, tailWord_597735, baseEnd_597735] using wordTrace_append hprefix tailTrace_597735
  have hstable : (prefixWord ++ tailWord_597735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597735).length < 2 ^ (prefixWord ++ tailWord_597735).sum := by decide
  have hdescent : baseEnd_597735 < baseStart_597735 := by decide
  rcases family_descends (prefixWord ++ tailWord_597735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597751 : List Nat := [1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 4]
def baseStart_597751 : Nat := 118140960795 + 597751 * 2 ^ 59
def prefixEnd_597751 : Nat := 4983230072969 + 3 ^ 40 * 597751 * 2
def baseEnd_597751 : Nat := 306933574705796030163499

theorem tailTrace_597751 : CollatzResearch.WordTrace tailWord_597751 prefixEnd_597751 306933574705796030163499 := by
  unfold tailWord_597751
  simp only [CollatzResearch.WordTrace]
  refine ⟨21801770057457689588289107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14534513371638459725526071 21801770057457689588289107)
  ·
    refine ⟨32702655086186534382433661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21801770057457689588289107 32702655086186534382433661)
    ·
      refine ⟨12263495657319950393412623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32702655086186534382433661 12263495657319950393412623)
      ·
        refine ⟨18395243485979925590118935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12263495657319950393412623 18395243485979925590118935)
        ·
          refine ⟨27592865228969888385178403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18395243485979925590118935 27592865228969888385178403)
          ·
            refine ⟨41389297843454832577767605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27592865228969888385178403 41389297843454832577767605)
            ·
              refine ⟨3880246672823890554165713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41389297843454832577767605 3880246672823890554165713)
              ·
                refine ⟨2910185004617917915624285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3880246672823890554165713 2910185004617917915624285)
                ·
                  refine ⟨1091319376731719218359107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2910185004617917915624285 1091319376731719218359107)
                  ·
                    refine ⟨1636979065097578827538661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1091319376731719218359107 1636979065097578827538661)
                    ·
                      refine ⟨306933574705796030163499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1636979065097578827538661 306933574705796030163499)
                      ·
                        rfl

theorem cell23_597751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_597751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597751 prefixEnd_597751 := by exact prefixLift 597751
  have htrace : WordTrace (prefixWord ++ tailWord_597751) baseStart_597751 baseEnd_597751 := by
    simpa [prefixWord, tailWord_597751, baseEnd_597751] using wordTrace_append hprefix tailTrace_597751
  have hstable : (prefixWord ++ tailWord_597751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597751).length < 2 ^ (prefixWord ++ tailWord_597751).sum := by decide
  have hdescent : baseEnd_597751 < baseStart_597751 := by decide
  rcases family_descends (prefixWord ++ tailWord_597751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597761 : List Nat := [1, 2, 4, 1, 1, 1, 3, 3, 1, 6]
def baseStart_597761 : Nat := 118140960795 + 597761 * 2 ^ 59
def prefixEnd_597761 : Nat := 4983230072969 + 3 ^ 40 * 597761 * 2
def baseEnd_597761 : Nat := 102312903170780330346151

theorem tailTrace_597761 : CollatzResearch.WordTrace tailWord_597761 prefixEnd_597761 102312903170780330346151 := by
  unfold tailWord_597761
  simp only [CollatzResearch.WordTrace]
  refine ⟨21802134787421461296153137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14534756524947640864102091 21802134787421461296153137)
  ·
    refine ⟨16351601090566095972114853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21802134787421461296153137 16351601090566095972114853)
    ·
      refine ⟨3065925204481142994771535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16351601090566095972114853 3065925204481142994771535)
      ·
        refine ⟨4598887806721714492157303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3065925204481142994771535 4598887806721714492157303)
        ·
          refine ⟨6898331710082571738235955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4598887806721714492157303 6898331710082571738235955)
          ·
            refine ⟨10347497565123857607353933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6898331710082571738235955 10347497565123857607353933)
            ·
              refine ⟨3880311586921446602757725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10347497565123857607353933 3880311586921446602757725)
              ·
                refine ⟨1455116845095542476034147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3880311586921446602757725 1455116845095542476034147)
                ·
                  refine ⟨2182675267643313714051221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1455116845095542476034147 2182675267643313714051221)
                  ·
                    refine ⟨102312903170780330346151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2182675267643313714051221 102312903170780330346151)
                    ·
                      rfl

theorem cell23_597761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_597761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597761 prefixEnd_597761 := by exact prefixLift 597761
  have htrace : WordTrace (prefixWord ++ tailWord_597761) baseStart_597761 baseEnd_597761 := by
    simpa [prefixWord, tailWord_597761, baseEnd_597761] using wordTrace_append hprefix tailTrace_597761
  have hstable : (prefixWord ++ tailWord_597761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597761).length < 2 ^ (prefixWord ++ tailWord_597761).sum := by decide
  have hdescent : baseEnd_597761 < baseStart_597761 := by decide
  rcases family_descends (prefixWord ++ tailWord_597761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597766 : List Nat := [6, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_597766 : Nat := 118140960795 + 597766 * 2 ^ 59
def prefixEnd_597766 : Nat := 4983230072969 + 3 ^ 40 * 597766 * 2
def baseEnd_597766 : Nat := 306941276915613471475931

theorem tailTrace_597766 : CollatzResearch.WordTrace tailWord_597766 prefixEnd_597766 306941276915613471475931 := by
  unfold tailWord_597766
  simp only [CollatzResearch.WordTrace]
  refine ⟨681322411012604598440161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14534878101602231433390101 681322411012604598440161)
  ·
    refine ⟨510991808259453448830121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 681322411012604598440161 510991808259453448830121)
    ·
      refine ⟨383243856194590086622591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 510991808259453448830121 383243856194590086622591)
      ·
        refine ⟨574865784291885129933887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383243856194590086622591 574865784291885129933887)
        ·
          refine ⟨862298676437827694900831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 574865784291885129933887 862298676437827694900831)
          ·
            refine ⟨1293448014656741542351247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 862298676437827694900831 1293448014656741542351247)
            ·
              refine ⟨1940172021985112313526871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1293448014656741542351247 1940172021985112313526871)
              ·
                refine ⟨2910258032977668470290307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1940172021985112313526871 2910258032977668470290307)
                ·
                  refine ⟨4365387049466502705435461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2910258032977668470290307 4365387049466502705435461)
                  ·
                    refine ⟨818510071774969257269149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4365387049466502705435461 818510071774969257269149)
                    ·
                      refine ⟨306941276915613471475931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 818510071774969257269149 306941276915613471475931)
                      ·
                        rfl

theorem cell23_597766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_597766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597766 prefixEnd_597766 := by exact prefixLift 597766
  have htrace : WordTrace (prefixWord ++ tailWord_597766) baseStart_597766 baseEnd_597766 := by
    simpa [prefixWord, tailWord_597766, baseEnd_597766] using wordTrace_append hprefix tailTrace_597766
  have hstable : (prefixWord ++ tailWord_597766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597766).length < 2 ^ (prefixWord ++ tailWord_597766).sum := by decide
  have hdescent : baseEnd_597766 < baseStart_597766 := by decide
  rcases family_descends (prefixWord ++ tailWord_597766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597768 : List Nat := [2, 1, 3, 2, 2, 1, 2, 4, 1, 1, 4]
def baseStart_597768 : Nat := 118140960795 + 597768 * 2 ^ 59
def prefixEnd_597768 : Nat := 4983230072969 + 3 ^ 40 * 597768 * 2
def baseEnd_597768 : Nat := 306942303876922463650921

theorem tailTrace_597768 : CollatzResearch.WordTrace tailWord_597768 prefixEnd_597768 306942303876922463650921 := by
  unfold tailWord_597768
  simp only [CollatzResearch.WordTrace]
  refine ⟨10901195049198050745828979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14534926732264067661105305 10901195049198050745828979)
  ·
    refine ⟨16351792573797076118743469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10901195049198050745828979 16351792573797076118743469)
    ·
      refine ⟨6131922215173903544528801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16351792573797076118743469 6131922215173903544528801)
      ·
        refine ⟨4598941661380427658396601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6131922215173903544528801 4598941661380427658396601)
        ·
          refine ⟨3449206246035320743797451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4598941661380427658396601 3449206246035320743797451)
          ·
            refine ⟨5173809369052981115696177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3449206246035320743797451 5173809369052981115696177)
            ·
              refine ⟨3880357026789735836772133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5173809369052981115696177 3880357026789735836772133)
              ·
                refine ⟨727566942523075469394775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3880357026789735836772133 727566942523075469394775)
                ·
                  refine ⟨1091350413784613204092163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 727566942523075469394775 1091350413784613204092163)
                  ·
                    refine ⟨1637025620676919806138245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1091350413784613204092163 1637025620676919806138245)
                    ·
                      refine ⟨306942303876922463650921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1637025620676919806138245 306942303876922463650921)
                      ·
                        rfl

theorem cell23_597768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_597768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597768 prefixEnd_597768 := by exact prefixLift 597768
  have htrace : WordTrace (prefixWord ++ tailWord_597768) baseStart_597768 baseEnd_597768 := by
    simpa [prefixWord, tailWord_597768, baseEnd_597768] using wordTrace_append hprefix tailTrace_597768
  have hstable : (prefixWord ++ tailWord_597768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597768).length < 2 ^ (prefixWord ++ tailWord_597768).sum := by decide
  have hdescent : baseEnd_597768 < baseStart_597768 := by decide
  rcases family_descends (prefixWord ++ tailWord_597768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597773 : List Nat := [1, 7, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_597773 : Nat := 118140960795 + 597773 * 2 ^ 59
def prefixEnd_597773 : Nat := 4983230072969 + 3 ^ 40 * 597773 * 2
def baseEnd_597773 : Nat := 102314957093398314696133

theorem tailTrace_597773 : CollatzResearch.WordTrace tailWord_597773 prefixEnd_597773 102314957093398314696133 := by
  unfold tailWord_597773
  simp only [CollatzResearch.WordTrace]
  refine ⟨21802572463377987345589973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14535048308918658230393315 21802572463377987345589973)
  ·
    refine ⟨510997792110421578412265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 21802572463377987345589973 510997792110421578412265)
    ·
      refine ⟨383248344082816183809199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 510997792110421578412265 383248344082816183809199)
      ·
        refine ⟨574872516124224275713799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383248344082816183809199 574872516124224275713799)
        ·
          refine ⟨862308774186336413570699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 574872516124224275713799 862308774186336413570699)
          ·
            refine ⟨1293463161279504620356049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 862308774186336413570699 1293463161279504620356049)
            ·
              refine ⟨970097370959628465267037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1293463161279504620356049 970097370959628465267037)
              ·
                refine ⟨363786514109860674475139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 970097370959628465267037 363786514109860674475139)
                ·
                  refine ⟨545679771164791011712709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 363786514109860674475139 545679771164791011712709)
                  ·
                    refine ⟨102314957093398314696133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 545679771164791011712709 102314957093398314696133)
                    ·
                      rfl

theorem cell23_597773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_597773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597773 prefixEnd_597773 := by exact prefixLift 597773
  have htrace : WordTrace (prefixWord ++ tailWord_597773) baseStart_597773 baseEnd_597773 := by
    simpa [prefixWord, tailWord_597773, baseEnd_597773] using wordTrace_append hprefix tailTrace_597773
  have hstable : (prefixWord ++ tailWord_597773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597773).length < 2 ^ (prefixWord ++ tailWord_597773).sum := by decide
  have hdescent : baseEnd_597773 < baseStart_597773 := by decide
  rcases family_descends (prefixWord ++ tailWord_597773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
