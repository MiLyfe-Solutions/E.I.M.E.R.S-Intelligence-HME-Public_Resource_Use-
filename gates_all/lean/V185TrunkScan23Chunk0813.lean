import V185TrunkScan23Chunk0812

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4809445 : List Nat := [1, 3, 1, 4, 1, 2, 1, 4, 1, 5]
def baseStart_4809445 : Nat := 118140960795 + 4809445 * 2 ^ 59
def prefixEnd_4809445 : Nat := 4983230072969 + 3 ^ 40 * 4809445 * 2
def baseEnd_4809445 : Nat := 823185655454346919339757

theorem tailTrace_4809445 : CollatzResearch.WordTrace tailWord_4809445 prefixEnd_4809445 823185655454346919339757 := by
  unfold tailWord_4809445
  simp only [CollatzResearch.WordTrace]
  refine ⟨175414870061209627657085789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116943246707473085104723859 175414870061209627657085789)
  ·
    refine ⟨65780576272953610371407171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175414870061209627657085789 65780576272953610371407171)
    ·
      refine ⟨98670864409430415557110757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65780576272953610371407171 98670864409430415557110757)
      ·
        refine ⟨18500787076768202916958267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98670864409430415557110757 18500787076768202916958267)
        ·
          refine ⟨27751180615152304375437401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18500787076768202916958267 27751180615152304375437401)
          ·
            refine ⟨20813385461364228281578051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27751180615152304375437401 20813385461364228281578051)
            ·
              refine ⟨31220078192046342422367077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20813385461364228281578051 31220078192046342422367077)
              ·
                refine ⟨5853764661008689204193827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31220078192046342422367077 5853764661008689204193827)
                ·
                  refine ⟨8780646991513033806290741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5853764661008689204193827 8780646991513033806290741)
                  ·
                    refine ⟨823185655454346919339757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8780646991513033806290741 823185655454346919339757)
                    ·
                      rfl

theorem cell23_4809445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 5].length) (baseStart_4809445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809445 prefixEnd_4809445 := by exact prefixLift 4809445
  have htrace : WordTrace (prefixWord ++ tailWord_4809445) baseStart_4809445 baseEnd_4809445 := by
    simpa [prefixWord, tailWord_4809445, baseEnd_4809445] using wordTrace_append hprefix tailTrace_4809445
  have hstable : (prefixWord ++ tailWord_4809445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809445).length < 2 ^ (prefixWord ++ tailWord_4809445).sum := by decide
  have hdescent : baseEnd_4809445 < baseStart_4809445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809475 : List Nat := [1, 1, 1, 3, 2, 2, 1, 6, 2, 4]
def baseStart_4809475 : Nat := 118140960795 + 4809475 * 2 ^ 59
def prefixEnd_4809475 : Nat := 4983230072969 + 3 ^ 40 * 4809475 * 2
def baseEnd_4809475 : Nat := 823190790260891880214711

theorem tailTrace_4809475 : CollatzResearch.WordTrace tailWord_4809475 prefixEnd_4809475 823190790260891880214711 := by
  unfold tailWord_4809475
  simp only [CollatzResearch.WordTrace]
  refine ⟨175415964251100942780677879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116943976167400628520451919 175415964251100942780677879)
  ·
    refine ⟨263123946376651414171016819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175415964251100942780677879 263123946376651414171016819)
    ·
      refine ⟨394685919564977121256525229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263123946376651414171016819 394685919564977121256525229)
      ·
        refine ⟨148007219836866420471196961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 394685919564977121256525229 148007219836866420471196961)
        ·
          refine ⟨111005414877649815353397721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148007219836866420471196961 111005414877649815353397721)
          ·
            refine ⟨83254061158237361515048291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111005414877649815353397721 83254061158237361515048291)
            ·
              refine ⟨124881091737356042272572437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83254061158237361515048291 124881091737356042272572437)
              ·
                refine ⟨5853801175188564481526833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 124881091737356042272572437 5853801175188564481526833)
                ·
                  refine ⟨4390350881391423361145125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5853801175188564481526833 4390350881391423361145125)
                  ·
                    refine ⟨823190790260891880214711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4390350881391423361145125 823190790260891880214711)
                    ·
                      rfl

theorem cell23_4809475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 4].length) (baseStart_4809475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809475 prefixEnd_4809475 := by exact prefixLift 4809475
  have htrace : WordTrace (prefixWord ++ tailWord_4809475) baseStart_4809475 baseEnd_4809475 := by
    simpa [prefixWord, tailWord_4809475, baseEnd_4809475] using wordTrace_append hprefix tailTrace_4809475
  have hstable : (prefixWord ++ tailWord_4809475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809475).length < 2 ^ (prefixWord ++ tailWord_4809475).sum := by decide
  have hdescent : baseEnd_4809475 < baseStart_4809475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809476 : List Nat := [2, 3, 2, 2, 1, 1, 5, 2, 1, 1, 3]
def baseStart_4809476 : Nat := 118140960795 + 4809476 * 2 ^ 59
def prefixEnd_4809476 : Nat := 4983230072969 + 3 ^ 40 * 4809476 * 2
def baseEnd_4809476 : Nat := 2469572884263330136731629

theorem tailTrace_4809476 : CollatzResearch.WordTrace tailWord_4809476 prefixEnd_4809476 2469572884263330136731629 := by
  unfold tailWord_4809476
  simp only [CollatzResearch.WordTrace]
  refine ⟨87708000362048659975732141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116944000482731546634309521 87708000362048659975732141)
  ·
    refine ⟨32890500135768247490899553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87708000362048659975732141 32890500135768247490899553)
    ·
      refine ⟨24667875101826185618174665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32890500135768247490899553 24667875101826185618174665)
      ·
        refine ⟨18500906326369639213630999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24667875101826185618174665 18500906326369639213630999)
        ·
          refine ⟨27751359489554458820446499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18500906326369639213630999 27751359489554458820446499)
          ·
            refine ⟨41627039234331688230669749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27751359489554458820446499 41627039234331688230669749)
            ·
              refine ⟨3902534928218595771625289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41627039234331688230669749 3902534928218595771625289)
              ·
                refine ⟨2926901196163946828718967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3902534928218595771625289 2926901196163946828718967)
                ·
                  refine ⟨4390351794245920243078451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2926901196163946828718967 4390351794245920243078451)
                  ·
                    refine ⟨6585527691368880364617677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4390351794245920243078451 6585527691368880364617677)
                    ·
                      refine ⟨2469572884263330136731629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6585527691368880364617677 2469572884263330136731629)
                      ·
                        rfl

theorem cell23_4809476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_4809476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809476 prefixEnd_4809476 := by exact prefixLift 4809476
  have htrace : WordTrace (prefixWord ++ tailWord_4809476) baseStart_4809476 baseEnd_4809476 := by
    simpa [prefixWord, tailWord_4809476, baseEnd_4809476] using wordTrace_append hprefix tailTrace_4809476
  have hstable : (prefixWord ++ tailWord_4809476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809476).length < 2 ^ (prefixWord ++ tailWord_4809476).sum := by decide
  have hdescent : baseEnd_4809476 < baseStart_4809476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809526 : List Nat := [5, 1, 2, 2, 2, 1, 2, 2, 2, 4]
def baseStart_4809526 : Nat := 118140960795 + 4809526 * 2 ^ 59
def prefixEnd_4809526 : Nat := 4983230072969 + 3 ^ 40 * 4809526 * 2
def baseEnd_4809526 : Nat := 823199519432018313702133

theorem tailTrace_4809526 : CollatzResearch.WordTrace tailWord_4809526 prefixEnd_4809526 823199519432018313702133 := by
  unfold tailWord_4809526
  simp only [CollatzResearch.WordTrace]
  refine ⟨10963614023369761155674027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116945216249277452327189621 10963614023369761155674027)
  ·
    refine ⟨16445421035054641733511041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10963614023369761155674027 16445421035054641733511041)
    ·
      refine ⟨12334065776290981300133281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16445421035054641733511041 12334065776290981300133281)
      ·
        refine ⟨9250549332218235975099961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12334065776290981300133281 9250549332218235975099961)
        ·
          refine ⟨6937911999163676981324971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9250549332218235975099961 6937911999163676981324971)
          ·
            refine ⟨10406867998745515471987457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6937911999163676981324971 10406867998745515471987457)
            ·
              refine ⟨7805150999059136603990593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10406867998745515471987457 7805150999059136603990593)
              ·
                refine ⟨5853863249294352452992945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7805150999059136603990593 5853863249294352452992945)
                ·
                  refine ⟨4390397436970764339744709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5853863249294352452992945 4390397436970764339744709)
                  ·
                    refine ⟨823199519432018313702133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4390397436970764339744709 823199519432018313702133)
                    ·
                      rfl

theorem cell23_4809526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_4809526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809526 prefixEnd_4809526 := by exact prefixLift 4809526
  have htrace : WordTrace (prefixWord ++ tailWord_4809526) baseStart_4809526 baseEnd_4809526 := by
    simpa [prefixWord, tailWord_4809526, baseEnd_4809526] using wordTrace_append hprefix tailTrace_4809526
  have hstable : (prefixWord ++ tailWord_4809526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809526).length < 2 ^ (prefixWord ++ tailWord_4809526).sum := by decide
  have hdescent : baseEnd_4809526 < baseStart_4809526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809533 : List Nat := [1, 4, 1, 4, 2, 1, 1, 4, 1, 2, 2]
def baseStart_4809533 : Nat := 118140960795 + 4809533 * 2 ^ 59
def prefixEnd_4809533 : Nat := 4983230072969 + 3 ^ 40 * 4809533 * 2
def baseEnd_4809533 : Nat := 2469602152660636413718867

theorem tailTrace_4809533 : CollatzResearch.WordTrace tailWord_4809533 prefixEnd_4809533 2469602152660636413718867 := by
  unfold tailWord_4809533
  simp only [CollatzResearch.WordTrace]
  refine ⟨175418079684890818686289253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116945386456593879124192835 175418079684890818686289253)
  ·
    refine ⟨32890889940917028503679235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175418079684890818686289253 32890889940917028503679235)
    ·
      refine ⟨49336334911375542755518853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32890889940917028503679235 49336334911375542755518853)
      ·
        refine ⟨9250562795882914266659785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49336334911375542755518853 9250562795882914266659785)
        ·
          refine ⟨6937922096912185699994839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9250562795882914266659785 6937922096912185699994839)
          ·
            refine ⟨10406883145368278549992259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6937922096912185699994839 10406883145368278549992259)
            ·
              refine ⟨15610324718052417824988389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10406883145368278549992259 15610324718052417824988389)
              ·
                refine ⟨2926935884634828342185323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15610324718052417824988389 2926935884634828342185323)
                ·
                  refine ⟨4390403826952242513277985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2926935884634828342185323 4390403826952242513277985)
                  ·
                    refine ⟨3292802870214181884958489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4390403826952242513277985 3292802870214181884958489)
                    ·
                      refine ⟨2469602152660636413718867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3292802870214181884958489 2469602152660636413718867)
                      ·
                        rfl

theorem cell23_4809533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_4809533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809533 prefixEnd_4809533 := by exact prefixLift 4809533
  have htrace : WordTrace (prefixWord ++ tailWord_4809533) baseStart_4809533 baseEnd_4809533 := by
    simpa [prefixWord, tailWord_4809533, baseEnd_4809533] using wordTrace_append hprefix tailTrace_4809533
  have hstable : (prefixWord ++ tailWord_4809533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809533).length < 2 ^ (prefixWord ++ tailWord_4809533).sum := by decide
  have hdescent : baseEnd_4809533 < baseStart_4809533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809576 : List Nat := [2, 1, 4, 2, 1, 2, 4, 1, 1, 3, 2]
def baseStart_4809576 : Nat := 118140960795 + 4809576 * 2 ^ 59
def prefixEnd_4809576 : Nat := 4983230072969 + 3 ^ 40 * 4809576 * 2
def baseEnd_4809576 : Nat := 2469624232328779745481169

theorem tailTrace_4809576 : CollatzResearch.WordTrace tailWord_4809576 prefixEnd_4809576 2469624232328779745481169 := by
  unfold tailWord_4809576
  simp only [CollatzResearch.WordTrace]
  refine ⟨87709824011867518515052291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116946432015823358020069721 87709824011867518515052291)
  ·
    refine ⟨131564736017801277772578437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87709824011867518515052291 131564736017801277772578437)
    ·
      refine ⟨24668388003337739582358457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131564736017801277772578437 24668388003337739582358457)
      ·
        refine ⟨18501291002503304686768843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24668388003337739582358457 18501291002503304686768843)
        ·
          refine ⟨27751936503754957030153265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18501291002503304686768843 27751936503754957030153265)
          ·
            refine ⟨20813952377816217772614949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27751936503754957030153265 20813952377816217772614949)
            ·
              refine ⟨3902616070840540832365303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20813952377816217772614949 3902616070840540832365303)
              ·
                refine ⟨5853924106260811248547955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3902616070840540832365303 5853924106260811248547955)
                ·
                  refine ⟨8780886159391216872821933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5853924106260811248547955 8780886159391216872821933)
                  ·
                    refine ⟨3292832309771706327308225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8780886159391216872821933 3292832309771706327308225)
                    ·
                      refine ⟨2469624232328779745481169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3292832309771706327308225 2469624232328779745481169)
                      ·
                        rfl

theorem cell23_4809576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_4809576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809576 prefixEnd_4809576 := by exact prefixLift 4809576
  have htrace : WordTrace (prefixWord ++ tailWord_4809576) baseStart_4809576 baseEnd_4809576 := by
    simpa [prefixWord, tailWord_4809576, baseEnd_4809576] using wordTrace_append hprefix tailTrace_4809576
  have hstable : (prefixWord ++ tailWord_4809576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809576).length < 2 ^ (prefixWord ++ tailWord_4809576).sum := by decide
  have hdescent : baseEnd_4809576 < baseStart_4809576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809585 : List Nat := [1, 2, 2, 2, 1, 4, 1, 2, 2, 2, 4]
def baseStart_4809585 : Nat := 118140960795 + 4809585 * 2 ^ 59
def prefixEnd_4809585 : Nat := 4983230072969 + 3 ^ 40 * 4809585 * 2
def baseEnd_4809585 : Nat := 2469628853654670210268627

theorem tailTrace_4809585 : CollatzResearch.WordTrace tailWord_4809585 prefixEnd_4809585 2469628853654670210268627 := by
  unfold tailWord_4809585
  simp only [CollatzResearch.WordTrace]
  refine ⟨175419976280702431567182209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116946650853801621044788139 175419976280702431567182209)
  ·
    refine ⟨131564982210526823675386657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175419976280702431567182209 131564982210526823675386657)
    ·
      refine ⟨98673736657895117756539993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131564982210526823675386657 98673736657895117756539993)
      ·
        refine ⟨74005302493421338317404995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98673736657895117756539993 74005302493421338317404995)
        ·
          refine ⟨111007953740132007476107493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74005302493421338317404995 111007953740132007476107493)
          ·
            refine ⟨20813991326274751401770155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111007953740132007476107493 20813991326274751401770155)
            ·
              refine ⟨31220986989412127102655233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20813991326274751401770155 31220986989412127102655233)
              ·
                refine ⟨23415740242059095326991425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31220986989412127102655233 23415740242059095326991425)
                ·
                  refine ⟨17561805181544321495243569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23415740242059095326991425 17561805181544321495243569)
                  ·
                    refine ⟨13171353886158241121432677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17561805181544321495243569 13171353886158241121432677)
                    ·
                      refine ⟨2469628853654670210268627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13171353886158241121432677 2469628853654670210268627)
                      ·
                        rfl

theorem cell23_4809585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_4809585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809585 prefixEnd_4809585 := by exact prefixLift 4809585
  have htrace : WordTrace (prefixWord ++ tailWord_4809585) baseStart_4809585 baseEnd_4809585 := by
    simpa [prefixWord, tailWord_4809585, baseEnd_4809585] using wordTrace_append hprefix tailTrace_4809585
  have hstable : (prefixWord ++ tailWord_4809585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809585).length < 2 ^ (prefixWord ++ tailWord_4809585).sum := by decide
  have hdescent : baseEnd_4809585 < baseStart_4809585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809625 : List Nat := [1, 2, 1, 2, 1, 3, 1, 5, 2, 5]
def baseStart_4809625 : Nat := 118140960795 + 4809625 * 2 ^ 59
def prefixEnd_4809625 : Nat := 4983230072969 + 3 ^ 40 * 4809625 * 2
def baseEnd_4809625 : Nat := 823216464293616684589481

theorem tailTrace_4809625 : CollatzResearch.WordTrace tailWord_4809625 prefixEnd_4809625 823216464293616684589481 := by
  unfold tailWord_4809625
  simp only [CollatzResearch.WordTrace]
  refine ⟨175421435200557518398638329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116947623467038345599092219 175421435200557518398638329)
  ·
    refine ⟨131566076400418138798978747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175421435200557518398638329 131566076400418138798978747)
    ·
      refine ⟨197349114600627208198468121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131566076400418138798978747 197349114600627208198468121)
      ·
        refine ⟨148011835950470406148851091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197349114600627208198468121 148011835950470406148851091)
        ·
          refine ⟨222017753925705609223276637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148011835950470406148851091 222017753925705609223276637)
          ·
            refine ⟨83256657722139603458728739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222017753925705609223276637 83256657722139603458728739)
            ·
              refine ⟨124884986583209405188093109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83256657722139603458728739 124884986583209405188093109)
              ·
                refine ⟨11707967492175881736383729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 124884986583209405188093109 11707967492175881736383729)
                ·
                  refine ⟨8780975619131911302287797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11707967492175881736383729 8780975619131911302287797)
                  ·
                    refine ⟨823216464293616684589481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8780975619131911302287797 823216464293616684589481)
                    ·
                      rfl

theorem cell23_4809625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 5].length) (baseStart_4809625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809625 prefixEnd_4809625 := by exact prefixLift 4809625
  have htrace : WordTrace (prefixWord ++ tailWord_4809625) baseStart_4809625 baseEnd_4809625 := by
    simpa [prefixWord, tailWord_4809625, baseEnd_4809625] using wordTrace_append hprefix tailTrace_4809625
  have hstable : (prefixWord ++ tailWord_4809625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809625).length < 2 ^ (prefixWord ++ tailWord_4809625).sum := by decide
  have hdescent : baseEnd_4809625 < baseStart_4809625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809662 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_4809662 : Nat := 118140960795 + 4809662 * 2 ^ 59
def prefixEnd_4809662 : Nat := 4983230072969 + 3 ^ 40 * 4809662 * 2
def baseEnd_4809662 : Nat := 2469668391665066409005773

theorem tailTrace_4809662 : CollatzResearch.WordTrace tailWord_4809662 prefixEnd_4809662 2469668391665066409005773 := by
  unfold tailWord_4809662
  simp only [CollatzResearch.WordTrace]
  refine ⟨21927848087677934214716905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116948523134282315811823493 21927848087677934214716905)
  ·
    refine ⟨16445886065758450661037679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21927848087677934214716905 16445886065758450661037679)
    ·
      refine ⟨24668829098637675991556519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16445886065758450661037679 24668829098637675991556519)
      ·
        refine ⟨37003243647956513987334779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24668829098637675991556519 37003243647956513987334779)
        ·
          refine ⟨55504865471934770981002169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37003243647956513987334779 55504865471934770981002169)
          ·
            refine ⟨41628649103951078235751627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55504865471934770981002169 41628649103951078235751627)
            ·
              refine ⟨62442973655926617353627441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41628649103951078235751627 62442973655926617353627441)
              ·
                refine ⟨46832230241944963015220581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62442973655926617353627441 46832230241944963015220581)
                ·
                  refine ⟨8781043170364680565353859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46832230241944963015220581 8781043170364680565353859)
                  ·
                    refine ⟨13171564755547020848030789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8781043170364680565353859 13171564755547020848030789)
                    ·
                      refine ⟨2469668391665066409005773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13171564755547020848030789 2469668391665066409005773)
                      ·
                        rfl

theorem cell23_4809662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_4809662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809662 prefixEnd_4809662 := by exact prefixLift 4809662
  have htrace : WordTrace (prefixWord ++ tailWord_4809662) baseStart_4809662 baseEnd_4809662 := by
    simpa [prefixWord, tailWord_4809662, baseEnd_4809662] using wordTrace_append hprefix tailTrace_4809662
  have hstable : (prefixWord ++ tailWord_4809662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809662).length < 2 ^ (prefixWord ++ tailWord_4809662).sum := by decide
  have hdescent : baseEnd_4809662 < baseStart_4809662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809706 : List Nat := [3, 1, 3, 1, 2, 3, 1, 4, 1, 4]
def baseStart_4809706 : Nat := 118140960795 + 4809706 * 2 ^ 59
def prefixEnd_4809706 : Nat := 4983230072969 + 3 ^ 40 * 4809706 * 2
def baseEnd_4809706 : Nat := 823230328271288078951857

theorem tailTrace_4809706 : CollatzResearch.WordTrace tailWord_4809706 prefixEnd_4809706 823230328271288078951857 := by
  unfold tailWord_4809706
  simp only [CollatzResearch.WordTrace]
  refine ⟨43856097378316017308084243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116949593008842712821557981 43856097378316017308084243)
  ·
    refine ⟨65784146067474025962126365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43856097378316017308084243 65784146067474025962126365)
    ·
      refine ⟨24669054775302759735797387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65784146067474025962126365 24669054775302759735797387)
      ·
        refine ⟨37003582162954139603696081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24669054775302759735797387 37003582162954139603696081)
        ·
          refine ⟨27752686622215604702772061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37003582162954139603696081 27752686622215604702772061)
          ·
            refine ⟨10407257483330851763539523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27752686622215604702772061 10407257483330851763539523)
            ·
              refine ⟨15610886224996277645309285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10407257483330851763539523 15610886224996277645309285)
              ·
                refine ⟨2927041167186802058495491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15610886224996277645309285 2927041167186802058495491)
                ·
                  refine ⟨4390561750780203087743237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2927041167186802058495491 4390561750780203087743237)
                  ·
                    refine ⟨823230328271288078951857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4390561750780203087743237 823230328271288078951857)
                    ·
                      rfl

theorem cell23_4809706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_4809706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809706 prefixEnd_4809706 := by exact prefixLift 4809706
  have htrace : WordTrace (prefixWord ++ tailWord_4809706) baseStart_4809706 baseEnd_4809706 := by
    simpa [prefixWord, tailWord_4809706, baseEnd_4809706] using wordTrace_append hprefix tailTrace_4809706
  have hstable : (prefixWord ++ tailWord_4809706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809706).length < 2 ^ (prefixWord ++ tailWord_4809706).sum := by decide
  have hdescent : baseEnd_4809706 < baseStart_4809706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809725 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 1, 3, 7]
def baseStart_4809725 : Nat := 118140960795 + 4809725 * 2 ^ 59
def prefixEnd_4809725 : Nat := 4983230072969 + 3 ^ 40 * 4809725 * 2
def baseEnd_4809725 : Nat := 2469700740946299662517983

theorem tailTrace_4809725 : CollatzResearch.WordTrace tailWord_4809725 prefixEnd_4809725 2469700740946299662517983 := by
  unfold tailWord_4809725
  simp only [CollatzResearch.WordTrace]
  refine ⟨175425082500195235477278629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116950055000130156984852419 175425082500195235477278629)
  ·
    refine ⟨32892202968786606651989743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175425082500195235477278629 32892202968786606651989743)
    ·
      refine ⟨49338304453179909977984615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32892202968786606651989743 49338304453179909977984615)
      ·
        refine ⟨74007456679769864966976923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49338304453179909977984615 74007456679769864966976923)
        ·
          refine ⟨111011185019654797450465385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74007456679769864966976923 111011185019654797450465385)
          ·
            refine ⟨83258388764741098087849039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111011185019654797450465385 83258388764741098087849039)
            ·
              refine ⟨124887583147111647131773559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83258388764741098087849039 124887583147111647131773559)
              ·
                refine ⟨187331374720667470697660339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124887583147111647131773559 187331374720667470697660339)
                ·
                  refine ⟨280997062081001206046490509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187331374720667470697660339 280997062081001206046490509)
                  ·
                    refine ⟨105373898280375452267433941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 280997062081001206046490509 105373898280375452267433941)
                    ·
                      refine ⟨2469700740946299662517983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 105373898280375452267433941 2469700740946299662517983)
                      ·
                        rfl

theorem cell23_4809725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_4809725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809725 prefixEnd_4809725 := by exact prefixLift 4809725
  have htrace : WordTrace (prefixWord ++ tailWord_4809725) baseStart_4809725 baseEnd_4809725 := by
    simpa [prefixWord, tailWord_4809725, baseEnd_4809725] using wordTrace_append hprefix tailTrace_4809725
  have hstable : (prefixWord ++ tailWord_4809725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809725).length < 2 ^ (prefixWord ++ tailWord_4809725).sum := by decide
  have hdescent : baseEnd_4809725 < baseStart_4809725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809729 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 5, 1, 3]
def baseStart_4809729 : Nat := 118140960795 + 4809729 * 2 ^ 59
def prefixEnd_4809729 : Nat := 4983230072969 + 3 ^ 40 * 4809729 * 2
def baseEnd_4809729 : Nat := 2469702794868917646867965

theorem tailTrace_4809729 : CollatzResearch.WordTrace tailWord_4809729 prefixEnd_4809729 2469702794868917646867965 := by
  unfold tailWord_4809729
  simp only [CollatzResearch.WordTrace]
  refine ⟨175425228392180744160424241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116950152261453829440282827 175425228392180744160424241)
  ·
    refine ⟨131568921294135558120318181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175425228392180744160424241 131568921294135558120318181)
    ·
      refine ⟨24669172742650417147559659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131568921294135558120318181 24669172742650417147559659)
      ·
        refine ⟨37003759113975625721339489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24669172742650417147559659 37003759113975625721339489)
        ·
          refine ⟨27752819335481719291004617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37003759113975625721339489 27752819335481719291004617)
          ·
            refine ⟨20814614501611289468253463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27752819335481719291004617 20814614501611289468253463)
            ·
              refine ⟨31221921752416934202380195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20814614501611289468253463 31221921752416934202380195)
              ·
                refine ⟨46832882628625401303570293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31221921752416934202380195 46832882628625401303570293)
                ·
                  refine ⟨4390582746433631372209715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46832882628625401303570293 4390582746433631372209715)
                  ·
                    refine ⟨6585874119650447058314573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4390582746433631372209715 6585874119650447058314573)
                    ·
                      refine ⟨2469702794868917646867965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6585874119650447058314573 2469702794868917646867965)
                      ·
                        rfl

theorem cell23_4809729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_4809729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809729 prefixEnd_4809729 := by exact prefixLift 4809729
  have htrace : WordTrace (prefixWord ++ tailWord_4809729) baseStart_4809729 baseEnd_4809729 := by
    simpa [prefixWord, tailWord_4809729, baseEnd_4809729] using wordTrace_append hprefix tailTrace_4809729
  have hstable : (prefixWord ++ tailWord_4809729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809729).length < 2 ^ (prefixWord ++ tailWord_4809729).sum := by decide
  have hdescent : baseEnd_4809729 < baseStart_4809729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809730 : List Nat := [3, 4, 1, 3, 2, 1, 1, 1, 2, 1, 4]
def baseStart_4809730 : Nat := 118140960795 + 4809730 * 2 ^ 59
def prefixEnd_4809730 : Nat := 4983230072969 + 3 ^ 40 * 4809730 * 2
def baseEnd_4809730 : Nat := 2469703308349572142955461

theorem tailTrace_4809730 : CollatzResearch.WordTrace tailWord_4809730 prefixEnd_4809730 2469703308349572142955461 := by
  unfold tailWord_4809730
  simp only [CollatzResearch.WordTrace]
  refine ⟨43856316216294280332802661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116950176576784747554140429 43856316216294280332802661)
  ·
    refine ⟨8223059290555177562400499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43856316216294280332802661 8223059290555177562400499)
    ·
      refine ⟨12334588935832766343600749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8223059290555177562400499 12334588935832766343600749)
      ·
        refine ⟨4625470850937287378850281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12334588935832766343600749 4625470850937287378850281)
        ·
          refine ⟨3469103138202965534137711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4625470850937287378850281 3469103138202965534137711)
          ·
            refine ⟨5203654707304448301206567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3469103138202965534137711 5203654707304448301206567)
            ·
              refine ⟨7805482060956672451809851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5203654707304448301206567 7805482060956672451809851)
              ·
                refine ⟨11708223091435008677714777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7805482060956672451809851 11708223091435008677714777)
                ·
                  refine ⟨8781167318576256508286083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11708223091435008677714777 8781167318576256508286083)
                  ·
                    refine ⟨13171750977864384762429125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8781167318576256508286083 13171750977864384762429125)
                    ·
                      refine ⟨2469703308349572142955461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13171750977864384762429125 2469703308349572142955461)
                      ·
                        rfl

theorem cell23_4809730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_4809730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809730 prefixEnd_4809730 := by exact prefixLift 4809730
  have htrace : WordTrace (prefixWord ++ tailWord_4809730) baseStart_4809730 baseEnd_4809730 := by
    simpa [prefixWord, tailWord_4809730, baseEnd_4809730] using wordTrace_append hprefix tailTrace_4809730
  have hstable : (prefixWord ++ tailWord_4809730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809730).length < 2 ^ (prefixWord ++ tailWord_4809730).sum := by decide
  have hdescent : baseEnd_4809730 < baseStart_4809730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809739 : List Nat := [1, 1, 1, 1, 6, 3, 1, 1, 1, 5, 2]
def baseStart_4809739 : Nat := 118140960795 + 4809739 * 2 ^ 59
def prefixEnd_4809739 : Nat := 4983230072969 + 3 ^ 40 * 4809739 * 2
def baseEnd_4809739 : Nat := 2469707929675462607742919

theorem tailTrace_4809739 : CollatzResearch.WordTrace tailWord_4809739 prefixEnd_4809739 2469707929675462607742919 := by
  unfold tailWord_4809739
  simp only [CollatzResearch.WordTrace]
  refine ⟨175425593122144515868288271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116950395414763010578858847 175425593122144515868288271)
  ·
    refine ⟨263138389683216773802432407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175425593122144515868288271 263138389683216773802432407)
    ·
      refine ⟨394707584524825160703648611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263138389683216773802432407 394707584524825160703648611)
      ·
        refine ⟨592061376787237741055472917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394707584524825160703648611 592061376787237741055472917)
        ·
          refine ⟨27752877036901769111975293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 592061376787237741055472917 27752877036901769111975293)
          ·
            refine ⟨10407328888838163416990735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27752877036901769111975293 10407328888838163416990735)
            ·
              refine ⟨15610993333257245125486103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10407328888838163416990735 15610993333257245125486103)
              ·
                refine ⟨23416489999885867688229155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15610993333257245125486103 23416489999885867688229155)
                ·
                  refine ⟨35124734999828801532343733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23416489999885867688229155 35124734999828801532343733)
                  ·
                    refine ⟨3292943906233950143657225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35124734999828801532343733 3292943906233950143657225)
                    ·
                      refine ⟨2469707929675462607742919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3292943906233950143657225 2469707929675462607742919)
                      ·
                        rfl

theorem cell23_4809739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 5, 2].length) (baseStart_4809739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809739 prefixEnd_4809739 := by exact prefixLift 4809739
  have htrace : WordTrace (prefixWord ++ tailWord_4809739) baseStart_4809739 baseEnd_4809739 := by
    simpa [prefixWord, tailWord_4809739, baseEnd_4809739] using wordTrace_append hprefix tailTrace_4809739
  have hstable : (prefixWord ++ tailWord_4809739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809739).length < 2 ^ (prefixWord ++ tailWord_4809739).sum := by decide
  have hdescent : baseEnd_4809739 < baseStart_4809739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809749 : List Nat := [1, 3, 2, 1, 4, 2, 1, 3, 1, 5]
def baseStart_4809749 : Nat := 118140960795 + 4809749 * 2 ^ 59
def prefixEnd_4809749 : Nat := 4983230072969 + 3 ^ 40 * 4809749 * 2
def baseEnd_4809749 : Nat := 823237688160669189539291

theorem tailTrace_4809749 : CollatzResearch.WordTrace tailWord_4809749 prefixEnd_4809749 823237688160669189539291 := by
  unfold tailWord_4809749
  simp only [CollatzResearch.WordTrace]
  refine ⟨175425957852108287576152301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116950638568072191717434867 175425957852108287576152301)
  ·
    refine ⟨65784734194540607841057113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175425957852108287576152301 65784734194540607841057113)
    ·
      refine ⟨49338550645905455880792835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65784734194540607841057113 49338550645905455880792835)
      ·
        refine ⟨74007825968858183821189253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49338550645905455880792835 74007825968858183821189253)
        ·
          refine ⟨13876467369160909466472985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74007825968858183821189253 13876467369160909466472985)
          ·
            refine ⟨10407350526870682099854739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13876467369160909466472985 10407350526870682099854739)
            ·
              refine ⟨15611025790306023149782109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10407350526870682099854739 15611025790306023149782109)
              ·
                refine ⟨5854134671364758681168291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15611025790306023149782109 5854134671364758681168291)
                ·
                  refine ⟨8781202007047138021752437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5854134671364758681168291 8781202007047138021752437)
                  ·
                    refine ⟨823237688160669189539291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8781202007047138021752437 823237688160669189539291)
                    ·
                      rfl

theorem cell23_4809749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_4809749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809749 prefixEnd_4809749 := by exact prefixLift 4809749
  have htrace : WordTrace (prefixWord ++ tailWord_4809749) baseStart_4809749 baseEnd_4809749 := by
    simpa [prefixWord, tailWord_4809749, baseEnd_4809749] using wordTrace_append hprefix tailTrace_4809749
  have hstable : (prefixWord ++ tailWord_4809749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809749).length < 2 ^ (prefixWord ++ tailWord_4809749).sum := by decide
  have hdescent : baseEnd_4809749 < baseStart_4809749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809772 : List Nat := [2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 5]
def baseStart_4809772 : Nat := 118140960795 + 4809772 * 2 ^ 59
def prefixEnd_4809772 : Nat := 4983230072969 + 3 ^ 40 * 4809772 * 2
def baseEnd_4809772 : Nat := 2469724874537060978630267

theorem tailTrace_4809772 : CollatzResearch.WordTrace tailWord_4809772 prefixEnd_4809772 2469724874537060978630267 := by
  unfold tailWord_4809772
  simp only [CollatzResearch.WordTrace]
  refine ⟨87713398365512481252119785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116951197820683308336159713 87713398365512481252119785)
  ·
    refine ⟨65785048774134360939089839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87713398365512481252119785 65785048774134360939089839)
    ·
      refine ⟨98677573161201541408634759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65785048774134360939089839 98677573161201541408634759)
      ·
        refine ⟨148016359741802312112952139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98677573161201541408634759 148016359741802312112952139)
        ·
          refine ⟨222024539612703468169428209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148016359741802312112952139 222024539612703468169428209)
          ·
            refine ⟨166518404709527601127071157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222024539612703468169428209 166518404709527601127071157)
            ·
              refine ⟨15611100441518212605662921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 166518404709527601127071157 15611100441518212605662921)
              ·
                refine ⟨11708325331138659454247191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15611100441518212605662921 11708325331138659454247191)
                ·
                  refine ⟨17562487996707989181370787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11708325331138659454247191 17562487996707989181370787)
                  ·
                    refine ⟨26343731995061983772056181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17562487996707989181370787 26343731995061983772056181)
                    ·
                      refine ⟨2469724874537060978630267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26343731995061983772056181 2469724874537060978630267)
                      ·
                        rfl

theorem cell23_4809772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_4809772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809772 prefixEnd_4809772 := by exact prefixLift 4809772
  have htrace : WordTrace (prefixWord ++ tailWord_4809772) baseStart_4809772 baseEnd_4809772 := by
    simpa [prefixWord, tailWord_4809772, baseEnd_4809772] using wordTrace_append hprefix tailTrace_4809772
  have hstable : (prefixWord ++ tailWord_4809772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809772).length < 2 ^ (prefixWord ++ tailWord_4809772).sum := by decide
  have hdescent : baseEnd_4809772 < baseStart_4809772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809786 : List Nat := [3, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2]
def baseStart_4809786 : Nat := 118140960795 + 4809786 * 2 ^ 59
def prefixEnd_4809786 : Nat := 4983230072969 + 3 ^ 40 * 4809786 * 2
def baseEnd_4809786 : Nat := 2469732063266223923855203

theorem tailTrace_4809786 : CollatzResearch.WordTrace tailWord_4809786 prefixEnd_4809786 2469732063266223923855203 := by
  unfold tailWord_4809786
  simp only [CollatzResearch.WordTrace]
  refine ⟨43856826838243560723812303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116951538235316161930166141 43856826838243560723812303)
  ·
    refine ⟨65785240257365341085718455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43856826838243560723812303 65785240257365341085718455)
    ·
      refine ⟨98677860386048011628577683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65785240257365341085718455 98677860386048011628577683)
      ·
        refine ⟨148016790579072017442866525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98677860386048011628577683 148016790579072017442866525)
        ·
          refine ⟨55506296467152006541074947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148016790579072017442866525 55506296467152006541074947)
          ·
            refine ⟨83259444700728009811612421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55506296467152006541074947 83259444700728009811612421)
            ·
              refine ⟨15611145881386501839677329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83259444700728009811612421 15611145881386501839677329)
              ·
                refine ⟨11708359411039876379757997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15611145881386501839677329 11708359411039876379757997)
                ·
                  refine ⟨4390634779139953642409249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11708359411039876379757997 4390634779139953642409249)
                  ·
                    refine ⟨3292976084354965231806937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4390634779139953642409249 3292976084354965231806937)
                    ·
                      refine ⟨2469732063266223923855203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3292976084354965231806937 2469732063266223923855203)
                      ·
                        rfl

theorem cell23_4809786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2].length) (baseStart_4809786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809786 prefixEnd_4809786 := by exact prefixLift 4809786
  have htrace : WordTrace (prefixWord ++ tailWord_4809786) baseStart_4809786 baseEnd_4809786 := by
    simpa [prefixWord, tailWord_4809786, baseEnd_4809786] using wordTrace_append hprefix tailTrace_4809786
  have hstable : (prefixWord ++ tailWord_4809786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809786).length < 2 ^ (prefixWord ++ tailWord_4809786).sum := by decide
  have hdescent : baseEnd_4809786 < baseStart_4809786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809814 : List Nat := [5, 2, 2, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_4809814 : Nat := 118140960795 + 4809814 * 2 ^ 59
def prefixEnd_4809814 : Nat := 4983230072969 + 3 ^ 40 * 4809814 * 2
def baseEnd_4809814 : Nat := 2469746440724549814305075

theorem tailTrace_4809814 : CollatzResearch.WordTrace tailWord_4809814 prefixEnd_4809814 2469746440724549814305075 := by
  unfold tailWord_4809814
  simp only [CollatzResearch.WordTrace]
  refine ⟨10964270537304550229829281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116952219064581869118178997 10964270537304550229829281)
  ·
    refine ⟨8223202902978412672371961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10964270537304550229829281 8223202902978412672371961)
    ·
      refine ⟨6167402177233809504278971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8223202902978412672371961 6167402177233809504278971)
      ·
        refine ⟨9251103265850714256418457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6167402177233809504278971 9251103265850714256418457)
        ·
          refine ⟨6938327449388035692313843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9251103265850714256418457 6938327449388035692313843)
          ·
            refine ⟨10407491174082053538470765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6938327449388035692313843 10407491174082053538470765)
            ·
              refine ⟨3902809190280770076926537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10407491174082053538470765 3902809190280770076926537)
              ·
                refine ⟨2927106892710577557694903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3902809190280770076926537 2927106892710577557694903)
                ·
                  refine ⟨4390660339065866336542355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2927106892710577557694903 4390660339065866336542355)
                  ·
                    refine ⟨6585990508598799504813533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4390660339065866336542355 6585990508598799504813533)
                    ·
                      refine ⟨2469746440724549814305075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6585990508598799504813533 2469746440724549814305075)
                      ·
                        rfl

theorem cell23_4809814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_4809814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809814 prefixEnd_4809814 := by exact prefixLift 4809814
  have htrace : WordTrace (prefixWord ++ tailWord_4809814) baseStart_4809814 baseEnd_4809814 := by
    simpa [prefixWord, tailWord_4809814, baseEnd_4809814] using wordTrace_append hprefix tailTrace_4809814
  have hstable : (prefixWord ++ tailWord_4809814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809814).length < 2 ^ (prefixWord ++ tailWord_4809814).sum := by decide
  have hdescent : baseEnd_4809814 < baseStart_4809814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809836 : List Nat := [2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 3]
def baseStart_4809836 : Nat := 118140960795 + 4809836 * 2 ^ 59
def prefixEnd_4809836 : Nat := 4983230072969 + 3 ^ 40 * 4809836 * 2
def baseEnd_4809836 : Nat := 2469757737298948728229973

theorem tailTrace_4809836 : CollatzResearch.WordTrace tailWord_4809836 prefixEnd_4809836 2469757737298948728229973 := by
  unfold tailWord_4809836
  simp only [CollatzResearch.WordTrace]
  refine ⟨87714565501396550717284681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116952754001862067623046241 87714565501396550717284681)
  ·
    refine ⟨65785924126047413037963511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87714565501396550717284681 65785924126047413037963511)
    ·
      refine ⟨98678886189071119556945267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65785924126047413037963511 98678886189071119556945267)
      ·
        refine ⟨148018329283606679335417901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98678886189071119556945267 148018329283606679335417901)
        ·
          refine ⟨55506873481352504750781713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148018329283606679335417901 55506873481352504750781713)
          ·
            refine ⟨41630155111014378563086285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55506873481352504750781713 41630155111014378563086285)
            ·
              refine ⟨15611308166630391961157357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41630155111014378563086285 15611308166630391961157357)
              ·
                refine ⟨5854240562486396985434009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15611308166630391961157357 5854240562486396985434009)
                ·
                  refine ⟨4390680421864797739075507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5854240562486396985434009 4390680421864797739075507)
                  ·
                    refine ⟨6586020632797196608613261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4390680421864797739075507 6586020632797196608613261)
                    ·
                      refine ⟨2469757737298948728229973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6586020632797196608613261 2469757737298948728229973)
                      ·
                        rfl

theorem cell23_4809836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 3].length) (baseStart_4809836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809836 prefixEnd_4809836 := by exact prefixLift 4809836
  have htrace : WordTrace (prefixWord ++ tailWord_4809836) baseStart_4809836 baseEnd_4809836 := by
    simpa [prefixWord, tailWord_4809836, baseEnd_4809836] using wordTrace_append hprefix tailTrace_4809836
  have hstable : (prefixWord ++ tailWord_4809836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809836).length < 2 ^ (prefixWord ++ tailWord_4809836).sum := by decide
  have hdescent : baseEnd_4809836 < baseStart_4809836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809879 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 3]
def baseStart_4809879 : Nat := 118140960795 + 4809879 * 2 ^ 59
def prefixEnd_4809879 : Nat := 4983230072969 + 3 ^ 40 * 4809879 * 2
def baseEnd_4809879 : Nat := 2469779816967092059992275

theorem tailTrace_4809879 : CollatzResearch.WordTrace tailWord_4809879 prefixEnd_4809879 2469779816967092059992275 := by
  unfold tailWord_4809879
  simp only [CollatzResearch.WordTrace]
  refine ⟨175430699341637319778384691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116953799561091546518923127 175430699341637319778384691)
  ·
    refine ⟨263146049012455979667577037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175430699341637319778384691 263146049012455979667577037)
    ·
      refine ⟨98679768379670992375341389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263146049012455979667577037 98679768379670992375341389)
      ·
        refine ⟨37004913142376622140753021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98679768379670992375341389 37004913142376622140753021)
        ·
          refine ⟨13876842428391233302782383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37004913142376622140753021 13876842428391233302782383)
          ·
            refine ⟨20815263642586849954173575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13876842428391233302782383 20815263642586849954173575)
            ·
              refine ⟨31222895463880274931260363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20815263642586849954173575 31222895463880274931260363)
              ·
                refine ⟨46834343195820412396890545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31222895463880274931260363 46834343195820412396890545)
                ·
                  refine ⟨35125757396865309297667909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46834343195820412396890545 35125757396865309297667909)
                  ·
                    refine ⟨6586079511912245493312733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35125757396865309297667909 6586079511912245493312733)
                    ·
                      refine ⟨2469779816967092059992275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6586079511912245493312733 2469779816967092059992275)
                      ·
                        rfl

theorem cell23_4809879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_4809879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809879 prefixEnd_4809879 := by exact prefixLift 4809879
  have htrace : WordTrace (prefixWord ++ tailWord_4809879) baseStart_4809879 baseEnd_4809879 := by
    simpa [prefixWord, tailWord_4809879, baseEnd_4809879] using wordTrace_append hprefix tailTrace_4809879
  have hstable : (prefixWord ++ tailWord_4809879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809879).length < 2 ^ (prefixWord ++ tailWord_4809879).sum := by decide
  have hdescent : baseEnd_4809879 < baseStart_4809879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809886 : List Nat := [4, 3, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_4809886 : Nat := 118140960795 + 4809886 * 2 ^ 59
def prefixEnd_4809886 : Nat := 4983230072969 + 3 ^ 40 * 4809886 * 2
def baseEnd_4809886 : Nat := 823261137110557844201581

theorem tailTrace_4809886 : CollatzResearch.WordTrace tailWord_4809886 prefixEnd_4809886 823261137110557844201581 := by
  unfold tailWord_4809886
  simp only [CollatzResearch.WordTrace]
  refine ⟨21928869331576494996736189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116953969768407973315926341 21928869331576494996736189)
  ·
    refine ⟨8223325999341185623776071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21928869331576494996736189 8223325999341185623776071)
    ·
      refine ⟨12334988999011778435664107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8223325999341185623776071 12334988999011778435664107)
      ·
        refine ⟨18502483498517667653496161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12334988999011778435664107 18502483498517667653496161)
        ·
          refine ⟨13876862623888250740122121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18502483498517667653496161 13876862623888250740122121)
          ·
            refine ⟨10407646967916188055091591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13876862623888250740122121 10407646967916188055091591)
            ·
              refine ⟨15611470451874282082637387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10407646967916188055091591 15611470451874282082637387)
              ·
                refine ⟨23417205677811423123956081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15611470451874282082637387 23417205677811423123956081)
                ·
                  refine ⟨17562904258358567342967061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23417205677811423123956081 17562904258358567342967061)
                  ·
                    refine ⟨823261137110557844201581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17562904258358567342967061 823261137110557844201581)
                    ·
                      rfl

theorem cell23_4809886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_4809886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809886 prefixEnd_4809886 := by exact prefixLift 4809886
  have htrace : WordTrace (prefixWord ++ tailWord_4809886) baseStart_4809886 baseEnd_4809886 := by
    simpa [prefixWord, tailWord_4809886, baseEnd_4809886] using wordTrace_append hprefix tailTrace_4809886
  have hstable : (prefixWord ++ tailWord_4809886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809886).length < 2 ^ (prefixWord ++ tailWord_4809886).sum := by decide
  have hdescent : baseEnd_4809886 < baseStart_4809886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809889 : List Nat := [1, 2, 3, 3, 1, 1, 3, 1, 2, 2, 4]
def baseStart_4809889 : Nat := 118140960795 + 4809889 * 2 ^ 59
def prefixEnd_4809889 : Nat := 4983230072969 + 3 ^ 40 * 4809889 * 2
def baseEnd_4809889 : Nat := 2469784951773637020867229

theorem tailTrace_4809889 : CollatzResearch.WordTrace tailWord_4809889 prefixEnd_4809889 2469784951773637020867229 := by
  unfold tailWord_4809889
  simp only [CollatzResearch.WordTrace]
  refine ⟨175431064071601091486248721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116954042714400727657499147 175431064071601091486248721)
  ·
    refine ⟨131573298053700818614686541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175431064071601091486248721 131573298053700818614686541)
    ·
      refine ⟨49339986770137806980507453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131573298053700818614686541 49339986770137806980507453)
      ·
        refine ⟨18502495038801677617690295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49339986770137806980507453 18502495038801677617690295)
        ·
          refine ⟨27753742558202516426535443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18502495038801677617690295 27753742558202516426535443)
          ·
            refine ⟨41630613837303774639803165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27753742558202516426535443 41630613837303774639803165)
            ·
              refine ⟨15611480188988915489926187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41630613837303774639803165 15611480188988915489926187)
              ·
                refine ⟨23417220283483373234889281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15611480188988915489926187 23417220283483373234889281)
                ·
                  refine ⟨17562915212612529926166961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23417220283483373234889281 17562915212612529926166961)
                  ·
                    refine ⟨13172186409459397444625221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17562915212612529926166961 13172186409459397444625221)
                    ·
                      refine ⟨2469784951773637020867229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13172186409459397444625221 2469784951773637020867229)
                      ·
                        rfl

theorem cell23_4809889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_4809889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809889 prefixEnd_4809889 := by exact prefixLift 4809889
  have htrace : WordTrace (prefixWord ++ tailWord_4809889) baseStart_4809889 baseEnd_4809889 := by
    simpa [prefixWord, tailWord_4809889, baseEnd_4809889] using wordTrace_append hprefix tailTrace_4809889
  have hstable : (prefixWord ++ tailWord_4809889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809889).length < 2 ^ (prefixWord ++ tailWord_4809889).sum := by decide
  have hdescent : baseEnd_4809889 < baseStart_4809889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809893 : List Nat := [1, 3, 1, 2, 1, 4, 2, 3, 2, 2, 2]
def baseStart_4809893 : Nat := 118140960795 + 4809893 * 2 ^ 59
def prefixEnd_4809893 : Nat := 4983230072969 + 3 ^ 40 * 4809893 * 2
def baseEnd_4809893 : Nat := 2469787005696255005217211

theorem tailTrace_4809893 : CollatzResearch.WordTrace tailWord_4809893 prefixEnd_4809893 2469787005696255005217211 := by
  unfold tailWord_4809893
  simp only [CollatzResearch.WordTrace]
  refine ⟨175431209963586600169394333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116954139975724400112929555 175431209963586600169394333)
  ·
    refine ⟨65786703736344975063522875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175431209963586600169394333 65786703736344975063522875)
    ·
      refine ⟨98680055604517462595284313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65786703736344975063522875 98680055604517462595284313)
      ·
        refine ⟨74010041703388096946463235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98680055604517462595284313 74010041703388096946463235)
        ·
          refine ⟨111015062555082145419694853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74010041703388096946463235 111015062555082145419694853)
          ·
            refine ⟨20815324229077902266192785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111015062555082145419694853 20815324229077902266192785)
            ·
              refine ⟨15611493171808426699644589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20815324229077902266192785 15611493171808426699644589)
              ·
                refine ⟨5854309939428160012366721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15611493171808426699644589 5854309939428160012366721)
                ·
                  refine ⟨4390732454571120009275041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5854309939428160012366721 4390732454571120009275041)
                  ·
                    refine ⟨3293049340928340006956281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4390732454571120009275041 3293049340928340006956281)
                    ·
                      refine ⟨2469787005696255005217211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3293049340928340006956281 2469787005696255005217211)
                      ·
                        rfl

theorem cell23_4809893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 2, 2].length) (baseStart_4809893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809893 prefixEnd_4809893 := by exact prefixLift 4809893
  have htrace : WordTrace (prefixWord ++ tailWord_4809893) baseStart_4809893 baseEnd_4809893 := by
    simpa [prefixWord, tailWord_4809893, baseEnd_4809893] using wordTrace_append hprefix tailTrace_4809893
  have hstable : (prefixWord ++ tailWord_4809893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809893).length < 2 ^ (prefixWord ++ tailWord_4809893).sum := by decide
  have hdescent : baseEnd_4809893 < baseStart_4809893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809916 : List Nat := [2, 2, 2, 3, 2, 1, 1, 5, 5]
def baseStart_4809916 : Nat := 118140960795 + 4809916 * 2 ^ 59
def prefixEnd_4809916 : Nat := 4983230072969 + 3 ^ 40 * 4809916 * 2
def baseEnd_4809916 : Nat := 274422090639034268358845

theorem tailTrace_4809916 : CollatzResearch.WordTrace tailWord_4809916 prefixEnd_4809916 274422090639034268358845 := by
  unfold tailWord_4809916
  simp only [CollatzResearch.WordTrace]
  refine ⟨87716024421251637548740801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116954699228335516731654401 87716024421251637548740801)
  ·
    refine ⟨65787018315938728161555601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87716024421251637548740801 65787018315938728161555601)
    ·
      refine ⟨49340263736954046121166701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65787018315938728161555601 49340263736954046121166701)
      ·
        refine ⟨18502598901357767295437513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49340263736954046121166701 18502598901357767295437513)
        ·
          refine ⟨13876949176018325471578135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18502598901357767295437513 13876949176018325471578135)
          ·
            refine ⟨20815423764027488207367203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13876949176018325471578135 20815423764027488207367203)
            ·
              refine ⟨31223135646041232311050805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20815423764027488207367203 31223135646041232311050805)
              ·
                refine ⟨2927168966816365529161013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31223135646041232311050805 2927168966816365529161013)
                ·
                  refine ⟨274422090639034268358845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2927168966816365529161013 274422090639034268358845)
                  ·
                    rfl

theorem cell23_4809916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 5].length) (baseStart_4809916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809916 prefixEnd_4809916 := by exact prefixLift 4809916
  have htrace : WordTrace (prefixWord ++ tailWord_4809916) baseStart_4809916 baseEnd_4809916 := by
    simpa [prefixWord, tailWord_4809916, baseEnd_4809916] using wordTrace_append hprefix tailTrace_4809916
  have hstable : (prefixWord ++ tailWord_4809916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809916).length < 2 ^ (prefixWord ++ tailWord_4809916).sum := by decide
  have hdescent : baseEnd_4809916 < baseStart_4809916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809966 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 1, 6, 2]
def baseStart_4809966 : Nat := 118140960795 + 4809966 * 2 ^ 59
def prefixEnd_4809966 : Nat := 4983230072969 + 3 ^ 40 * 4809966 * 2
def baseEnd_4809966 : Nat := 2469824489784033219604375

theorem tailTrace_4809966 : CollatzResearch.WordTrace tailWord_4809966 prefixEnd_4809966 2469824489784033219604375 := by
  unfold tailWord_4809966
  simp only [CollatzResearch.WordTrace]
  refine ⟨21929234061540266704600219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116955914994881422424534501 21929234061540266704600219)
  ·
    refine ⟨32893851092310400056900329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21929234061540266704600219 32893851092310400056900329)
    ·
      refine ⟨24670388319232800042675247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32893851092310400056900329 24670388319232800042675247)
      ·
        refine ⟨37005582478849200064012871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24670388319232800042675247 37005582478849200064012871)
        ·
          refine ⟨55508373718273800096019307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37005582478849200064012871 55508373718273800096019307)
          ·
            refine ⟨83262560577410700144028961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55508373718273800096019307 83262560577410700144028961)
            ·
              refine ⟨62446920433058025108021721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83262560577410700144028961 62446920433058025108021721)
              ·
                refine ⟨46835190324793518831016291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62446920433058025108021721 46835190324793518831016291)
                ·
                  refine ⟨70252785487190278246524437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46835190324793518831016291 70252785487190278246524437)
                  ·
                    refine ⟨3293099319712044292805833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70252785487190278246524437 3293099319712044292805833)
                    ·
                      refine ⟨2469824489784033219604375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3293099319712044292805833 2469824489784033219604375)
                      ·
                        rfl

theorem cell23_4809966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_4809966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809966 prefixEnd_4809966 := by exact prefixLift 4809966
  have htrace : WordTrace (prefixWord ++ tailWord_4809966) baseStart_4809966 baseEnd_4809966 := by
    simpa [prefixWord, tailWord_4809966, baseEnd_4809966] using wordTrace_append hprefix tailTrace_4809966
  have hstable : (prefixWord ++ tailWord_4809966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809966).length < 2 ^ (prefixWord ++ tailWord_4809966).sum := by decide
  have hdescent : baseEnd_4809966 < baseStart_4809966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4809989 : List Nat := [1, 3, 1, 1, 2, 1, 4, 4, 6]
def baseStart_4809989 : Nat := 118140960795 + 4809989 * 2 ^ 59
def prefixEnd_4809989 : Nat := 4983230072969 + 3 ^ 40 * 4809989 * 2
def baseEnd_4809989 : Nat := 274426255537676292179641

theorem tailTrace_4809989 : CollatzResearch.WordTrace tailWord_4809989 prefixEnd_4809989 274426255537676292179641 := by
  unfold tailWord_4809989
  simp only [CollatzResearch.WordTrace]
  refine ⟨175434711371238808564889021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116956474247492539043259347 175434711371238808564889021)
  ·
    refine ⟨65788016764214553211833383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175434711371238808564889021 65788016764214553211833383)
    ·
      refine ⟨98682025146321829817750075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65788016764214553211833383 98682025146321829817750075)
      ·
        refine ⟨148023037719482744726625113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98682025146321829817750075 148023037719482744726625113)
        ·
          refine ⟨111017278289612058544968835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148023037719482744726625113 111017278289612058544968835)
          ·
            refine ⟨166525917434418087817453253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111017278289612058544968835 166525917434418087817453253)
            ·
              refine ⟨31223609518953391465772485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 166525917434418087817453253 31223609518953391465772485)
              ·
                refine ⟨5854426784803760899832341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31223609518953391465772485 5854426784803760899832341)
                ·
                  refine ⟨274426255537676292179641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5854426784803760899832341 274426255537676292179641)
                  ·
                    rfl

theorem cell23_4809989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 6].length) (baseStart_4809989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4809989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4809989 prefixEnd_4809989 := by exact prefixLift 4809989
  have htrace : WordTrace (prefixWord ++ tailWord_4809989) baseStart_4809989 baseEnd_4809989 := by
    simpa [prefixWord, tailWord_4809989, baseEnd_4809989] using wordTrace_append hprefix tailTrace_4809989
  have hstable : (prefixWord ++ tailWord_4809989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4809989).length < 2 ^ (prefixWord ++ tailWord_4809989).sum := by decide
  have hdescent : baseEnd_4809989 < baseStart_4809989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4809989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810056 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 2, 6, 2]
def baseStart_4810056 : Nat := 118140960795 + 4810056 * 2 ^ 59
def prefixEnd_4810056 : Nat := 4983230072969 + 3 ^ 40 * 4810056 * 2
def baseEnd_4810056 : Nat := 2469870703042937867478961

theorem tailTrace_4810056 : CollatzResearch.WordTrace tailWord_4810056 prefixEnd_4810056 2469870703042937867478961 := by
  unfold tailWord_4810056
  simp only [CollatzResearch.WordTrace]
  refine ⟨87718577530998039503789011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116958103374664052671718681 87718577530998039503789011)
  ·
    refine ⟨131577866296497059255683517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87718577530998039503789011 131577866296497059255683517)
    ·
      refine ⟨49341699861186397220881319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131577866296497059255683517 49341699861186397220881319)
      ·
        refine ⟨74012549791779595831321979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49341699861186397220881319 74012549791779595831321979)
        ·
          refine ⟨111018824687669393746982969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74012549791779595831321979 111018824687669393746982969)
          ·
            refine ⟨83264118515752045310237227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111018824687669393746982969 83264118515752045310237227)
            ·
              refine ⟨124896177773628067965355841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83264118515752045310237227 124896177773628067965355841)
              ·
                refine ⟨93672133330221050974016881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124896177773628067965355841 93672133330221050974016881)
                ·
                  refine ⟨70254099997665788230512661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93672133330221050974016881 70254099997665788230512661)
                  ·
                    refine ⟨3293160937390583823305281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70254099997665788230512661 3293160937390583823305281)
                    ·
                      refine ⟨2469870703042937867478961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3293160937390583823305281 2469870703042937867478961)
                      ·
                        rfl

theorem cell23_4810056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 2, 6, 2].length) (baseStart_4810056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810056 prefixEnd_4810056 := by exact prefixLift 4810056
  have htrace : WordTrace (prefixWord ++ tailWord_4810056) baseStart_4810056 baseEnd_4810056 := by
    simpa [prefixWord, tailWord_4810056, baseEnd_4810056] using wordTrace_append hprefix tailTrace_4810056
  have hstable : (prefixWord ++ tailWord_4810056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810056).length < 2 ^ (prefixWord ++ tailWord_4810056).sum := by decide
  have hdescent : baseEnd_4810056 < baseStart_4810056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810066 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 6, 4]
def baseStart_4810066 : Nat := 118140960795 + 4810066 * 2 ^ 59
def prefixEnd_4810066 : Nat := 4983230072969 + 3 ^ 40 * 4810066 * 2
def baseEnd_4810066 : Nat := 823291945949827609451305

theorem tailTrace_4810066 : CollatzResearch.WordTrace tailWord_4810066 prefixEnd_4810066 823291945949827609451305 := by
  unfold tailWord_4810066
  simp only [CollatzResearch.WordTrace]
  refine ⟨43859379947989962678860513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116958346527973233810294701 43859379947989962678860513)
  ·
    refine ⟨32894534960992472009145385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43859379947989962678860513 32894534960992472009145385)
    ·
      refine ⟨24670901220744354006859039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32894534960992472009145385 24670901220744354006859039)
      ·
        refine ⟨37006351831116531010288559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24670901220744354006859039 37006351831116531010288559)
        ·
          refine ⟨55509527746674796515432839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37006351831116531010288559 55509527746674796515432839)
          ·
            refine ⟨83264291620012194773149259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55509527746674796515432839 83264291620012194773149259)
            ·
              refine ⟨124896437430018292159723889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83264291620012194773149259 124896437430018292159723889)
              ·
                refine ⟨93672328072513719119792917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124896437430018292159723889 93672328072513719119792917)
                ·
                  refine ⟨4390890378399080583740293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 93672328072513719119792917 4390890378399080583740293)
                  ·
                    refine ⟨823291945949827609451305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4390890378399080583740293 823291945949827609451305)
                    ·
                      rfl

theorem cell23_4810066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_4810066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810066 prefixEnd_4810066 := by exact prefixLift 4810066
  have htrace : WordTrace (prefixWord ++ tailWord_4810066) baseStart_4810066 baseEnd_4810066 := by
    simpa [prefixWord, tailWord_4810066, baseEnd_4810066] using wordTrace_append hprefix tailTrace_4810066
  have hstable : (prefixWord ++ tailWord_4810066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810066).length < 2 ^ (prefixWord ++ tailWord_4810066).sum := by decide
  have hdescent : baseEnd_4810066 < baseStart_4810066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810073 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 5, 2, 2]
def baseStart_4810073 : Nat := 118140960795 + 4810073 * 2 ^ 59
def prefixEnd_4810073 : Nat := 4983230072969 + 3 ^ 40 * 4810073 * 2
def baseEnd_4810073 : Nat := 2469879432214064300966383

theorem tailTrace_4810073 : CollatzResearch.WordTrace tailWord_4810073 prefixEnd_4810073 2469879432214064300966383 := by
  unfold tailWord_4810073
  simp only [CollatzResearch.WordTrace]
  refine ⟨175437775102934490910946873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116958516735289660607297915 175437775102934490910946873)
  ·
    refine ⟨131578331327200868183210155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175437775102934490910946873 131578331327200868183210155)
    ·
      refine ⟨197367496990801302274815233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131578331327200868183210155 197367496990801302274815233)
      ·
        refine ⟨148025622743100976706111425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197367496990801302274815233 148025622743100976706111425)
        ·
          refine ⟨111019217057325732529583569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148025622743100976706111425 111019217057325732529583569)
          ·
            refine ⟨83264412792994299397187677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111019217057325732529583569 83264412792994299397187677)
            ·
              refine ⟨31224154797372862273945379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83264412792994299397187677 31224154797372862273945379)
              ·
                refine ⟨46836232196059293410918069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31224154797372862273945379 46836232196059293410918069)
                ·
                  refine ⟨4390896768380558757273569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46836232196059293410918069 4390896768380558757273569)
                  ·
                    refine ⟨3293172576285419067955177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4390896768380558757273569 3293172576285419067955177)
                    ·
                      refine ⟨2469879432214064300966383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3293172576285419067955177 2469879432214064300966383)
                      ·
                        rfl

theorem cell23_4810073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 2, 2].length) (baseStart_4810073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810073 prefixEnd_4810073 := by exact prefixLift 4810073
  have htrace : WordTrace (prefixWord ++ tailWord_4810073) baseStart_4810073 baseEnd_4810073 := by
    simpa [prefixWord, tailWord_4810073, baseEnd_4810073] using wordTrace_append hprefix tailTrace_4810073
  have hstable : (prefixWord ++ tailWord_4810073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810073).length < 2 ^ (prefixWord ++ tailWord_4810073).sum := by decide
  have hdescent : baseEnd_4810073 < baseStart_4810073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810087 : List Nat := [1, 1, 5, 1, 5, 1, 2, 1, 1, 5]
def baseStart_4810087 : Nat := 118140960795 + 4810087 * 2 ^ 59
def prefixEnd_4810087 : Nat := 4983230072969 + 3 ^ 40 * 4810087 * 2
def baseEnd_4810087 : Nat := 823295540314409082063773

theorem tailTrace_4810087 : CollatzResearch.WordTrace tailWord_4810087 prefixEnd_4810087 823295540314409082063773 := by
  unfold tailWord_4810087
  simp only [CollatzResearch.WordTrace]
  refine ⟨175438285724883771301956515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116958857149922514201304343 175438285724883771301956515)
  ·
    refine ⟨263157428587325656952934773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175438285724883771301956515 263157428587325656952934773)
    ·
      refine ⟨24671008930061780339337635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 263157428587325656952934773 24671008930061780339337635)
      ·
        refine ⟨37006513395092670509006453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24671008930061780339337635 37006513395092670509006453)
        ·
          refine ⟨3469360630789937860219355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37006513395092670509006453 3469360630789937860219355)
          ·
            refine ⟨5204040946184906790329033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3469360630789937860219355 5204040946184906790329033)
            ·
              refine ⟨3903030709638680092746775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5204040946184906790329033 3903030709638680092746775)
              ·
                refine ⟨5854546064458020139120163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3903030709638680092746775 5854546064458020139120163)
                ·
                  refine ⟨8781819096687030208680245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5854546064458020139120163 8781819096687030208680245)
                  ·
                    refine ⟨823295540314409082063773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8781819096687030208680245 823295540314409082063773)
                    ·
                      rfl

theorem cell23_4810087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_4810087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810087 prefixEnd_4810087 := by exact prefixLift 4810087
  have htrace : WordTrace (prefixWord ++ tailWord_4810087) baseStart_4810087 baseEnd_4810087 := by
    simpa [prefixWord, tailWord_4810087, baseEnd_4810087] using wordTrace_append hprefix tailTrace_4810087
  have hstable : (prefixWord ++ tailWord_4810087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810087).length < 2 ^ (prefixWord ++ tailWord_4810087).sum := by decide
  have hdescent : baseEnd_4810087 < baseStart_4810087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810090 : List Nat := [3, 1, 3, 3, 2, 1, 1, 3, 1, 1, 4]
def baseStart_4810090 : Nat := 118140960795 + 4810090 * 2 ^ 59
def prefixEnd_4810090 : Nat := 4983230072969 + 3 ^ 40 * 4810090 * 2
def baseEnd_4810090 : Nat := 2469888161385190734453805

theorem tailTrace_4810090 : CollatzResearch.WordTrace tailWord_4810090 prefixEnd_4810090 2469888161385190734453805 := by
  unfold tailWord_4810090
  simp only [CollatzResearch.WordTrace]
  refine ⟨43859598785968225703578931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116958930095915268542877149 43859598785968225703578931)
  ·
    refine ⟨65789398178952338555368397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43859598785968225703578931 65789398178952338555368397)
    ·
      refine ⟨24671024317107126958263149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65789398178952338555368397 24671024317107126958263149)
      ·
        refine ⟨9251634118915172609348681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24671024317107126958263149 9251634118915172609348681)
        ·
          refine ⟨6938725589186379457011511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9251634118915172609348681 6938725589186379457011511)
          ·
            refine ⟨10408088383779569185517267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6938725589186379457011511 10408088383779569185517267)
            ·
              refine ⟨15612132575669353778275901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10408088383779569185517267 15612132575669353778275901)
              ·
                refine ⟨5854549715876007666853463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15612132575669353778275901 5854549715876007666853463)
                ·
                  refine ⟨8781824573814011500280195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5854549715876007666853463 8781824573814011500280195)
                  ·
                    refine ⟨13172736860721017250420293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8781824573814011500280195 13172736860721017250420293)
                    ·
                      refine ⟨2469888161385190734453805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13172736860721017250420293 2469888161385190734453805)
                      ·
                        rfl

theorem cell23_4810090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_4810090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810090 prefixEnd_4810090 := by exact prefixLift 4810090
  have htrace : WordTrace (prefixWord ++ tailWord_4810090) baseStart_4810090 baseEnd_4810090 := by
    simpa [prefixWord, tailWord_4810090, baseEnd_4810090] using wordTrace_append hprefix tailTrace_4810090
  have hstable : (prefixWord ++ tailWord_4810090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810090).length < 2 ^ (prefixWord ++ tailWord_4810090).sum := by decide
  have hdescent : baseEnd_4810090 < baseStart_4810090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810133 : List Nat := [1, 3, 2, 1, 1, 2, 2, 3, 3, 3, 2]
def baseStart_4810133 : Nat := 118140960795 + 4810133 * 2 ^ 59
def prefixEnd_4810133 : Nat := 4983230072969 + 3 ^ 40 * 4810133 * 2
def baseEnd_4810133 : Nat := 2469910241053334066216107

theorem tailTrace_4810133 : CollatzResearch.WordTrace tailWord_4810133 prefixEnd_4810133 2469910241053334066216107 := by
  unfold tailWord_4810133
  simp only [CollatzResearch.WordTrace]
  refine ⟨175439963482717121158131053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116959975655144747438754035 175439963482717121158131053)
  ·
    refine ⟨65789986306018920434299145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175439963482717121158131053 65789986306018920434299145)
    ·
      refine ⟨49342489729514190325724359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65789986306018920434299145 49342489729514190325724359)
      ·
        refine ⟨74013734594271285488586539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49342489729514190325724359 74013734594271285488586539)
        ·
          refine ⟨111020601891406928232879809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74013734594271285488586539 111020601891406928232879809)
          ·
            refine ⟨83265451418555196174659857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111020601891406928232879809 83265451418555196174659857)
            ·
              refine ⟨62449088563916397130994893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83265451418555196174659857 62449088563916397130994893)
              ·
                refine ⟨23418408211468648924123085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62449088563916397130994893 23418408211468648924123085)
                ·
                  refine ⟨8781903079300743346546157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23418408211468648924123085 8781903079300743346546157)
                  ·
                    refine ⟨3293213654737778754954809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8781903079300743346546157 3293213654737778754954809)
                    ·
                      refine ⟨2469910241053334066216107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3293213654737778754954809 2469910241053334066216107)
                      ·
                        rfl

theorem cell23_4810133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 3, 2].length) (baseStart_4810133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810133 prefixEnd_4810133 := by exact prefixLift 4810133
  have htrace : WordTrace (prefixWord ++ tailWord_4810133) baseStart_4810133 baseEnd_4810133 := by
    simpa [prefixWord, tailWord_4810133, baseEnd_4810133] using wordTrace_append hprefix tailTrace_4810133
  have hstable : (prefixWord ++ tailWord_4810133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810133).length < 2 ^ (prefixWord ++ tailWord_4810133).sum := by decide
  have hdescent : baseEnd_4810133 < baseStart_4810133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810176 : List Nat := [2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 4]
def baseStart_4810176 : Nat := 118140960795 + 4810176 * 2 ^ 59
def prefixEnd_4810176 : Nat := 4983230072969 + 3 ^ 40 * 4810176 * 2
def baseEnd_4810176 : Nat := 2469932320721477397978409

theorem tailTrace_4810176 : CollatzResearch.WordTrace tailWord_4810176 prefixEnd_4810176 2469932320721477397978409 := by
  unfold tailWord_4810176
  simp only [CollatzResearch.WordTrace]
  refine ⟨87720765910780669750973191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116961021214374226334630921 87720765910780669750973191)
  ·
    refine ⟨131581148866171004626459787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87720765910780669750973191 131581148866171004626459787)
    ·
      refine ⟨197371723299256506939689681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131581148866171004626459787 197371723299256506939689681)
      ·
        refine ⟨148028792474442380204767261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197371723299256506939689681 148028792474442380204767261)
        ·
          refine ⟨55510797177915892576787723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148028792474442380204767261 55510797177915892576787723)
          ·
            refine ⟨83266195766873838865181585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55510797177915892576787723 83266195766873838865181585)
            ·
              refine ⟨62449646825155379148886189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83266195766873838865181585 62449646825155379148886189)
              ·
                refine ⟨23418617559433267180832321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62449646825155379148886189 23418617559433267180832321)
                ·
                  refine ⟨17563963169574950385624241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23418617559433267180832321 17563963169574950385624241)
                  ·
                    refine ⟨13172972377181212789218181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17563963169574950385624241 13172972377181212789218181)
                    ·
                      refine ⟨2469932320721477397978409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13172972377181212789218181 2469932320721477397978409)
                      ·
                        rfl

theorem cell23_4810176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_4810176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810176 prefixEnd_4810176 := by exact prefixLift 4810176
  have htrace : WordTrace (prefixWord ++ tailWord_4810176) baseStart_4810176 baseEnd_4810176 := by
    simpa [prefixWord, tailWord_4810176, baseEnd_4810176] using wordTrace_append hprefix tailTrace_4810176
  have hstable : (prefixWord ++ tailWord_4810176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810176).length < 2 ^ (prefixWord ++ tailWord_4810176).sum := by decide
  have hdescent : baseEnd_4810176 < baseStart_4810176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810178 : List Nat := [3, 5, 2, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_4810178 : Nat := 118140960795 + 4810178 * 2 ^ 59
def prefixEnd_4810178 : Nat := 4983230072969 + 3 ^ 40 * 4810178 * 2
def baseEnd_4810178 : Nat := 2469933347682786390153401

theorem tailTrace_4810178 : CollatzResearch.WordTrace tailWord_4810178 prefixEnd_4810178 2469933347682786390153401 := by
  unfold tailWord_4810178
  simp only [CollatzResearch.WordTrace]
  refine ⟨43860401191888523460879797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116961069845036062562346125 43860401191888523460879797)
  ·
    refine ⟨4111912611739549074457481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43860401191888523460879797 4111912611739549074457481)
    ·
      refine ⟨3083934458804661805843111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4111912611739549074457481 3083934458804661805843111)
      ·
        refine ⟨4625901688206992708764667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3083934458804661805843111 4625901688206992708764667)
        ·
          refine ⟨6938852532310489063147001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4625901688206992708764667 6938852532310489063147001)
          ·
            refine ⟨5204139399232866797360251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6938852532310489063147001 5204139399232866797360251)
            ·
              refine ⟨7806209098849300196040377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5204139399232866797360251 7806209098849300196040377)
              ·
                refine ⟨5854656824136975147030283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7806209098849300196040377 5854656824136975147030283)
                ·
                  refine ⟨8781985236205462720545425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5854656824136975147030283 8781985236205462720545425)
                  ·
                    refine ⟨6586488927154097040409069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8781985236205462720545425 6586488927154097040409069)
                    ·
                      refine ⟨2469933347682786390153401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6586488927154097040409069 2469933347682786390153401)
                      ·
                        rfl

theorem cell23_4810178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_4810178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810178 prefixEnd_4810178 := by exact prefixLift 4810178
  have htrace : WordTrace (prefixWord ++ tailWord_4810178) baseStart_4810178 baseEnd_4810178 := by
    simpa [prefixWord, tailWord_4810178, baseEnd_4810178] using wordTrace_append hprefix tailTrace_4810178
  have hstable : (prefixWord ++ tailWord_4810178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810178).length < 2 ^ (prefixWord ++ tailWord_4810178).sum := by decide
  have hdescent : baseEnd_4810178 < baseStart_4810178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810223 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 2, 5, 2]
def baseStart_4810223 : Nat := 118140960795 + 4810223 * 2 ^ 59
def prefixEnd_4810223 : Nat := 4983230072969 + 3 ^ 40 * 4810223 * 2
def baseEnd_4810223 : Nat := 2469956454312238714090693

theorem tailTrace_4810223 : CollatzResearch.WordTrace tailWord_4810223 prefixEnd_4810223 2469956454312238714090693 := by
  unfold tailWord_4810223
  simp only [CollatzResearch.WordTrace]
  refine ⟨175443246052391066528907323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116962164034927377685938215 175443246052391066528907323)
  ·
    refine ⟨263164869078586599793360985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175443246052391066528907323 263164869078586599793360985)
    ·
      refine ⟨197373651808939949845020739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263164869078586599793360985 197373651808939949845020739)
      ·
        refine ⟨296060477713409924767531109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197373651808939949845020739 296060477713409924767531109)
        ·
          refine ⟨55511339571264360893912083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 296060477713409924767531109 55511339571264360893912083)
          ·
            refine ⟨83267009356896541340868125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55511339571264360893912083 83267009356896541340868125)
            ·
              refine ⟨31225128508836203002825547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83267009356896541340868125 31225128508836203002825547)
              ·
                refine ⟨46837692763254304504238321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31225128508836203002825547 46837692763254304504238321)
                ·
                  refine ⟨35128269572440728378178741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46837692763254304504238321 35128269572440728378178741)
                  ·
                    refine ⟨3293275272416318285454257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35128269572440728378178741 3293275272416318285454257)
                    ·
                      refine ⟨2469956454312238714090693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3293275272416318285454257 2469956454312238714090693)
                      ·
                        rfl

theorem cell23_4810223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 5, 2].length) (baseStart_4810223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810223 prefixEnd_4810223 := by exact prefixLift 4810223
  have htrace : WordTrace (prefixWord ++ tailWord_4810223) baseStart_4810223 baseEnd_4810223 := by
    simpa [prefixWord, tailWord_4810223, baseEnd_4810223] using wordTrace_append hprefix tailTrace_4810223
  have hstable : (prefixWord ++ tailWord_4810223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810223).length < 2 ^ (prefixWord ++ tailWord_4810223).sum := by decide
  have hdescent : baseEnd_4810223 < baseStart_4810223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810230 : List Nat := [5, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3]
def baseStart_4810230 : Nat := 118140960795 + 4810230 * 2 ^ 59
def prefixEnd_4810230 : Nat := 4983230072969 + 3 ^ 40 * 4810230 * 2
def baseEnd_4810230 : Nat := 2469960048676820186703161

theorem tailTrace_4810230 : CollatzResearch.WordTrace tailWord_4810230 prefixEnd_4810230 2469960048676820186703161 := by
  unfold tailWord_4810230
  simp only [CollatzResearch.WordTrace]
  refine ⟨10965218835210356670275759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116962334242243804482941429 10965218835210356670275759)
  ·
    refine ⟨16447828252815535005413639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10965218835210356670275759 16447828252815535005413639)
    ·
      refine ⟨24671742379223302508120459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16447828252815535005413639 24671742379223302508120459)
      ·
        refine ⟨37007613568834953762180689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24671742379223302508120459 37007613568834953762180689)
        ·
          refine ⟨27755710176626215321635517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37007613568834953762180689 27755710176626215321635517)
          ·
            refine ⟨10408391316234830745613319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27755710176626215321635517 10408391316234830745613319)
            ·
              refine ⟨15612586974352246118419979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10408391316234830745613319 15612586974352246118419979)
              ·
                refine ⟨23418880461528369177629969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15612586974352246118419979 23418880461528369177629969)
                ·
                  refine ⟨17564160346146276883222477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23418880461528369177629969 17564160346146276883222477)
                  ·
                    refine ⟨6586560129804853831208429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17564160346146276883222477 6586560129804853831208429)
                    ·
                      refine ⟨2469960048676820186703161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6586560129804853831208429 2469960048676820186703161)
                      ·
                        rfl

theorem cell23_4810230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_4810230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810230 prefixEnd_4810230 := by exact prefixLift 4810230
  have htrace : WordTrace (prefixWord ++ tailWord_4810230) baseStart_4810230 baseEnd_4810230 := by
    simpa [prefixWord, tailWord_4810230, baseEnd_4810230] using wordTrace_append hprefix tailTrace_4810230
  have hstable : (prefixWord ++ tailWord_4810230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810230).length < 2 ^ (prefixWord ++ tailWord_4810230).sum := by decide
  have hdescent : baseEnd_4810230 < baseStart_4810230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810250 : List Nat := [3, 1, 2, 2, 2, 4, 1, 1, 2, 5]
def baseStart_4810250 : Nat := 118140960795 + 4810250 * 2 ^ 59
def prefixEnd_4810250 : Nat := 4983230072969 + 3 ^ 40 * 4810250 * 2
def baseEnd_4810250 : Nat := 823323439429970036151023

theorem tailTrace_4810250 : CollatzResearch.WordTrace tailWord_4810250 prefixEnd_4810250 823323439429970036151023 := by
  unfold tailWord_4810250
  simp only [CollatzResearch.WordTrace]
  refine ⟨43861057705823312535035051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116962820548862166760093469 43861057705823312535035051)
  ·
    refine ⟨65791586558734968802552577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43861057705823312535035051 65791586558734968802552577)
    ·
      refine ⟨49343689919051226601914433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65791586558734968802552577 49343689919051226601914433)
      ·
        refine ⟨37007767439288419951435825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49343689919051226601914433 37007767439288419951435825)
        ·
          refine ⟨27755825579466314963576869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37007767439288419951435825 27755825579466314963576869)
          ·
            refine ⟨5204217296149934055670663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27755825579466314963576869 5204217296149934055670663)
            ·
              refine ⟨7806325944224901083505995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5204217296149934055670663 7806325944224901083505995)
              ·
                refine ⟨11709488916337351625258993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7806325944224901083505995 11709488916337351625258993)
                ·
                  refine ⟨8782116687253013718944245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11709488916337351625258993 8782116687253013718944245)
                  ·
                    refine ⟨823323439429970036151023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8782116687253013718944245 823323439429970036151023)
                    ·
                      rfl

theorem cell23_4810250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_4810250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810250 prefixEnd_4810250 := by exact prefixLift 4810250
  have htrace : WordTrace (prefixWord ++ tailWord_4810250) baseStart_4810250 baseEnd_4810250 := by
    simpa [prefixWord, tailWord_4810250, baseEnd_4810250] using wordTrace_append hprefix tailTrace_4810250
  have hstable : (prefixWord ++ tailWord_4810250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810250).length < 2 ^ (prefixWord ++ tailWord_4810250).sum := by decide
  have hdescent : baseEnd_4810250 < baseStart_4810250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810357 : List Nat := [1, 3, 4, 2, 1, 1, 3, 2, 1, 5]
def baseStart_4810357 : Nat := 118140960795 + 4810357 * 2 ^ 59
def prefixEnd_4810357 : Nat := 4983230072969 + 3 ^ 40 * 4810357 * 2
def baseEnd_4810357 : Nat := 823341753573313729938359

theorem tailTrace_4810357 : CollatzResearch.WordTrace tailWord_4810357 prefixEnd_4810357 823341753573313729938359 := by
  unfold tailWord_4810357
  simp only [CollatzResearch.WordTrace]
  refine ⟨175448133433905607414285325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116965422289270404942856883 175448133433905607414285325)
  ·
    refine ⟨65793050037714602780356997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175448133433905607414285325 65793050037714602780356997)
    ·
      refine ⟨12336196882071488021316937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65793050037714602780356997 12336196882071488021316937)
      ·
        refine ⟨9252147661553616015987703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12336196882071488021316937 9252147661553616015987703)
        ·
          refine ⟨13878221492330424023981555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9252147661553616015987703 13878221492330424023981555)
          ·
            refine ⟨20817332238495636035972333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13878221492330424023981555 20817332238495636035972333)
            ·
              refine ⟨7806499589435863513489625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20817332238495636035972333 7806499589435863513489625)
              ·
                refine ⟨5854874692076897635117219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7806499589435863513489625 5854874692076897635117219)
                ·
                  refine ⟨8782312038115346452675829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5854874692076897635117219 8782312038115346452675829)
                  ·
                    refine ⟨823341753573313729938359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8782312038115346452675829 823341753573313729938359)
                    ·
                      rfl

theorem cell23_4810357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_4810357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810357 prefixEnd_4810357 := by exact prefixLift 4810357
  have htrace : WordTrace (prefixWord ++ tailWord_4810357) baseStart_4810357 baseEnd_4810357 := by
    simpa [prefixWord, tailWord_4810357, baseEnd_4810357] using wordTrace_append hprefix tailTrace_4810357
  have hstable : (prefixWord ++ tailWord_4810357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810357).length < 2 ^ (prefixWord ++ tailWord_4810357).sum := by decide
  have hdescent : baseEnd_4810357 < baseStart_4810357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810400 : List Nat := [2, 1, 1, 4, 3, 3, 1, 8]
def baseStart_4810400 : Nat := 118140960795 + 4810400 * 2 ^ 59
def prefixEnd_4810400 : Nat := 4983230072969 + 3 ^ 40 * 4810400 * 2
def baseEnd_4810400 : Nat := 91483234829188315613977

theorem tailTrace_4810400 : CollatzResearch.WordTrace tailWord_4810400 prefixEnd_4810400 91483234829188315613977 := by
  unfold tailWord_4810400
  simp only [CollatzResearch.WordTrace]
  refine ⟨87724850886374912879050327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116966467848499883838733769 87724850886374912879050327)
  ·
    refine ⟨131587276329562369318575491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87724850886374912879050327 131587276329562369318575491)
    ·
      refine ⟨197380914494343553977863237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131587276329562369318575491 197380914494343553977863237)
      ·
        refine ⟨37008921467689416370849357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197380914494343553977863237 37008921467689416370849357)
        ·
          refine ⟨13878345550383531139068509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37008921467689416370849357 13878345550383531139068509)
          ·
            refine ⟨5204379581393824177150691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13878345550383531139068509 5204379581393824177150691)
            ·
              refine ⟨7806569372090736265726037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5204379581393824177150691 7806569372090736265726037)
              ·
                refine ⟨91483234829188315613977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7806569372090736265726037 91483234829188315613977)
                ·
                  rfl

theorem cell23_4810400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 8].length) (baseStart_4810400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810400 prefixEnd_4810400 := by exact prefixLift 4810400
  have htrace : WordTrace (prefixWord ++ tailWord_4810400) baseStart_4810400 baseEnd_4810400 := by
    simpa [prefixWord, tailWord_4810400, baseEnd_4810400] using wordTrace_append hprefix tailTrace_4810400
  have hstable : (prefixWord ++ tailWord_4810400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810400).length < 2 ^ (prefixWord ++ tailWord_4810400).sum := by decide
  have hdescent : baseEnd_4810400 < baseStart_4810400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810434 : List Nat := [3, 5, 1, 2, 1, 1, 10]
def baseStart_4810434 : Nat := 118140960795 + 4810434 * 2 ^ 59
def prefixEnd_4810434 : Nat := 4983230072969 + 3 ^ 40 * 4810434 * 2
def baseEnd_4810434 : Nat := 30494627144818980105583

theorem tailTrace_4810434 : CollatzResearch.WordTrace tailWord_4810434 prefixEnd_4810434 30494627144818980105583 := by
  unfold tailWord_4810434
  simp only [CollatzResearch.WordTrace]
  refine ⟨43862735463656662391209589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116967294569751099709892237 43862735463656662391209589)
  ·
    refine ⟨4112131449717812099175899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43862735463656662391209589 4112131449717812099175899)
    ·
      refine ⟨6168197174576718148763849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4112131449717812099175899 6168197174576718148763849)
      ·
        refine ⟨4626147880932538611572887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6168197174576718148763849 4626147880932538611572887)
        ·
          refine ⟨6939221821398807917359331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4626147880932538611572887 6939221821398807917359331)
          ·
            refine ⟨10408832732098211876038997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6939221821398807917359331 10408832732098211876038997)
            ·
              refine ⟨30494627144818980105583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10408832732098211876038997 30494627144818980105583)
              ·
                rfl

theorem cell23_4810434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 10].length) (baseStart_4810434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810434 prefixEnd_4810434 := by exact prefixLift 4810434
  have htrace : WordTrace (prefixWord ++ tailWord_4810434) baseStart_4810434 baseEnd_4810434 := by
    simpa [prefixWord, tailWord_4810434, baseEnd_4810434] using wordTrace_append hprefix tailTrace_4810434
  have hstable : (prefixWord ++ tailWord_4810434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810434).length < 2 ^ (prefixWord ++ tailWord_4810434).sum := by decide
  have hdescent : baseEnd_4810434 < baseStart_4810434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810437 : List Nat := [1, 3, 1, 1, 1, 1, 2, 7, 1, 3, 2]
def baseStart_4810437 : Nat := 118140960795 + 4810437 * 2 ^ 59
def prefixEnd_4810437 : Nat := 4983230072969 + 3 ^ 40 * 4810437 * 2
def baseEnd_4810437 : Nat := 2470066339172300876814709

theorem tailTrace_4810437 : CollatzResearch.WordTrace tailWord_4810437 prefixEnd_4810437 2470066339172300876814709 := by
  unfold tailWord_4810437
  simp only [CollatzResearch.WordTrace]
  refine ⟨175451051273615781077197565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116967367515743854051465043 175451051273615781077197565)
  ·
    refine ⟨65794144227605917903949087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175451051273615781077197565 65794144227605917903949087)
    ·
      refine ⟨98691216341408876855923631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65794144227605917903949087 98691216341408876855923631)
      ·
        refine ⟨148036824512113315283885447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98691216341408876855923631 148036824512113315283885447)
        ·
          refine ⟨222055236768169972925828171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148036824512113315283885447 222055236768169972925828171)
          ·
            refine ⟨333082855152254959388742257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222055236768169972925828171 333082855152254959388742257)
            ·
              refine ⟨249812141364191219541556693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 333082855152254959388742257 249812141364191219541556693)
              ·
                refine ⟨5854972063223231708005235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 249812141364191219541556693 5854972063223231708005235)
                ·
                  refine ⟨8782458094834847562007853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5854972063223231708005235 8782458094834847562007853)
                  ·
                    refine ⟨3293421785563067835752945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8782458094834847562007853 3293421785563067835752945)
                    ·
                      refine ⟨2470066339172300876814709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3293421785563067835752945 2470066339172300876814709)
                      ·
                        rfl

theorem cell23_4810437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 3, 2].length) (baseStart_4810437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810437 prefixEnd_4810437 := by exact prefixLift 4810437
  have htrace : WordTrace (prefixWord ++ tailWord_4810437) baseStart_4810437 baseEnd_4810437 := by
    simpa [prefixWord, tailWord_4810437, baseEnd_4810437] using wordTrace_append hprefix tailTrace_4810437
  have hstable : (prefixWord ++ tailWord_4810437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810437).length < 2 ^ (prefixWord ++ tailWord_4810437).sum := by decide
  have hdescent : baseEnd_4810437 < baseStart_4810437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810438 : List Nat := [6, 1, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_4810438 : Nat := 118140960795 + 4810438 * 2 ^ 59
def prefixEnd_4810438 : Nat := 4983230072969 + 3 ^ 40 * 4810438 * 2
def baseEnd_4810438 : Nat := 823355617550985124300735

theorem tailTrace_4810438 : CollatzResearch.WordTrace tailWord_4810438 prefixEnd_4810438 823355617550985124300735 := by
  unfold tailWord_4810438
  simp only [CollatzResearch.WordTrace]
  refine ⟨5482846492081629945249499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 116967391831074772165322645 5482846492081629945249499)
  ·
    refine ⟨8224269738122444917874249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5482846492081629945249499 8224269738122444917874249)
    ·
      refine ⟨6168202303591833688405687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8224269738122444917874249 6168202303591833688405687)
      ·
        refine ⟨9252303455387750532608531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6168202303591833688405687 9252303455387750532608531)
        ·
          refine ⟨13878455183081625798912797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9252303455387750532608531 13878455183081625798912797)
          ·
            refine ⟨5204420693655609674592299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13878455183081625798912797 5204420693655609674592299)
            ·
              refine ⟨7806631040483414511888449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5204420693655609674592299 7806631040483414511888449)
              ·
                refine ⟨5854973280362560883916337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7806631040483414511888449 5854973280362560883916337)
                ·
                  refine ⟨4391229960271920662937253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5854973280362560883916337 4391229960271920662937253)
                  ·
                    refine ⟨823355617550985124300735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4391229960271920662937253 823355617550985124300735)
                    ·
                      rfl

theorem cell23_4810438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_4810438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810438 prefixEnd_4810438 := by exact prefixLift 4810438
  have htrace : WordTrace (prefixWord ++ tailWord_4810438) baseStart_4810438 baseEnd_4810438 := by
    simpa [prefixWord, tailWord_4810438, baseEnd_4810438] using wordTrace_append hprefix tailTrace_4810438
  have hstable : (prefixWord ++ tailWord_4810438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810438).length < 2 ^ (prefixWord ++ tailWord_4810438).sum := by decide
  have hdescent : baseEnd_4810438 < baseStart_4810438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810444 : List Nat := [2, 2, 1, 5, 2, 1, 1, 1, 4, 1, 3]
def baseStart_4810444 : Nat := 118140960795 + 4810444 * 2 ^ 59
def prefixEnd_4810444 : Nat := 4983230072969 + 3 ^ 40 * 4810444 * 2
def baseEnd_4810444 : Nat := 2470069933536882349427177

theorem tailTrace_4810444 : CollatzResearch.WordTrace tailWord_4810444 prefixEnd_4810444 2470069933536882349427177 := by
  unfold tailWord_4810444
  simp only [CollatzResearch.WordTrace]
  refine ⟨87725653292295210636351193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116967537723060280848468257 87725653292295210636351193)
  ·
    refine ⟨65794239969221407977263395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87725653292295210636351193 65794239969221407977263395)
    ·
      refine ⟨98691359953832111965895093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65794239969221407977263395 98691359953832111965895093)
      ·
        refine ⟨9252314995671760496802665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98691359953832111965895093 9252314995671760496802665)
        ·
          refine ⟨6939236246753820372601999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9252314995671760496802665 6939236246753820372601999)
          ·
            refine ⟨10408854370130730558902999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6939236246753820372601999 10408854370130730558902999)
            ·
              refine ⟨15613281555196095838354499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10408854370130730558902999 15613281555196095838354499)
              ·
                refine ⟨23419922332794143757531749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15613281555196095838354499 23419922332794143757531749)
                ·
                  refine ⟨4391235437398901954537203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23419922332794143757531749 4391235437398901954537203)
                  ·
                    refine ⟨6586853156098352931805805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4391235437398901954537203 6586853156098352931805805)
                    ·
                      refine ⟨2470069933536882349427177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6586853156098352931805805 2470069933536882349427177)
                      ·
                        rfl

theorem cell23_4810444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_4810444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810444 prefixEnd_4810444 := by exact prefixLift 4810444
  have htrace : WordTrace (prefixWord ++ tailWord_4810444) baseStart_4810444 baseEnd_4810444 := by
    simpa [prefixWord, tailWord_4810444, baseEnd_4810444] using wordTrace_append hprefix tailTrace_4810444
  have hstable : (prefixWord ++ tailWord_4810444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810444).length < 2 ^ (prefixWord ++ tailWord_4810444).sum := by decide
  have hdescent : baseEnd_4810444 < baseStart_4810444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810461 : List Nat := [1, 4, 3, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_4810461 : Nat := 118140960795 + 4810461 * 2 ^ 59
def prefixEnd_4810461 : Nat := 4983230072969 + 3 ^ 40 * 4810461 * 2
def baseEnd_4810461 : Nat := 2470078662708008782914599

theorem tailTrace_4810461 : CollatzResearch.WordTrace tailWord_4810461 prefixEnd_4810461 2470078662708008782914599 := by
  unfold tailWord_4810461
  simp only [CollatzResearch.WordTrace]
  refine ⟨175451926625528833176071237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116967951083685888784047491 175451926625528833176071237)
  ·
    refine ⟨32897236242286656220513357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175451926625528833176071237 32897236242286656220513357)
    ·
      refine ⟨12336463590857496082692509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32897236242286656220513357 12336463590857496082692509)
      ·
        refine ⟨4626173846571561031009691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12336463590857496082692509 4626173846571561031009691)
        ·
          refine ⟨6939260769857341546514537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4626173846571561031009691 6939260769857341546514537)
          ·
            refine ⟨5204445577393006159885903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6939260769857341546514537 5204445577393006159885903)
            ·
              refine ⟨7806668366089509239828855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5204445577393006159885903 7806668366089509239828855)
              ·
                refine ⟨11710002549134263859743283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7806668366089509239828855 11710002549134263859743283)
                ·
                  refine ⟨17565003823701395789614925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11710002549134263859743283 17565003823701395789614925)
                  ·
                    refine ⟨6586876433888023421105597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17565003823701395789614925 6586876433888023421105597)
                    ·
                      refine ⟨2470078662708008782914599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6586876433888023421105597 2470078662708008782914599)
                      ·
                        rfl

theorem cell23_4810461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_4810461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810461 prefixEnd_4810461 := by exact prefixLift 4810461
  have htrace : WordTrace (prefixWord ++ tailWord_4810461) baseStart_4810461 baseEnd_4810461 := by
    simpa [prefixWord, tailWord_4810461, baseEnd_4810461] using wordTrace_append hprefix tailTrace_4810461
  have hstable : (prefixWord ++ tailWord_4810461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810461).length < 2 ^ (prefixWord ++ tailWord_4810461).sum := by decide
  have hdescent : baseEnd_4810461 < baseStart_4810461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810530 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_4810530 : Nat := 118140960795 + 4810530 * 2 ^ 59
def prefixEnd_4810530 : Nat := 4983230072969 + 3 ^ 40 * 4810530 * 2
def baseEnd_4810530 : Nat := 2470114092873169012951781

theorem tailTrace_4810530 : CollatzResearch.WordTrace tailWord_4810530 prefixEnd_4810530 2470114092873169012951781 := by
  unfold tailWord_4810530
  simp only [CollatzResearch.WordTrace]
  refine ⟨43863610815569714490083261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116969628841519238640222029 43863610815569714490083261)
  ·
    refine ⟨16448854055838642933781223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43863610815569714490083261 16448854055838642933781223)
    ·
      refine ⟨24673281083757964400671835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16448854055838642933781223 24673281083757964400671835)
      ·
        refine ⟨37009921625636946601007753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24673281083757964400671835 37009921625636946601007753)
        ·
          refine ⟨27757441219227709950755815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37009921625636946601007753 27757441219227709950755815)
          ·
            refine ⟨41636161828841564926133723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27757441219227709950755815 41636161828841564926133723)
            ·
              refine ⟨62454242743262347389200585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41636161828841564926133723 62454242743262347389200585)
              ·
                refine ⟨46840682057446760541900439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62454242743262347389200585 46840682057446760541900439)
                ·
                  refine ⟨70261023086170140812850659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46840682057446760541900439 70261023086170140812850659)
                  ·
                    refine ⟨105391534629255211219275989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70261023086170140812850659 105391534629255211219275989)
                    ·
                      refine ⟨2470114092873169012951781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 105391534629255211219275989 2470114092873169012951781)
                      ·
                        rfl

theorem cell23_4810530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_4810530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810530 prefixEnd_4810530 := by exact prefixLift 4810530
  have htrace : WordTrace (prefixWord ++ tailWord_4810530) baseStart_4810530 baseEnd_4810530 := by
    simpa [prefixWord, tailWord_4810530, baseEnd_4810530] using wordTrace_append hprefix tailTrace_4810530
  have hstable : (prefixWord ++ tailWord_4810530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810530).length < 2 ^ (prefixWord ++ tailWord_4810530).sum := by decide
  have hdescent : baseEnd_4810530 < baseStart_4810530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810560 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 3]
def baseStart_4810560 : Nat := 118140960795 + 4810560 * 2 ^ 59
def prefixEnd_4810560 : Nat := 4983230072969 + 3 ^ 40 * 4810560 * 2
def baseEnd_4810560 : Nat := 2470129497292803895576643

theorem tailTrace_4810560 : CollatzResearch.WordTrace tailWord_4810560 prefixEnd_4810560 2470129497292803895576643 := by
  unfold tailWord_4810560
  simp only [CollatzResearch.WordTrace]
  refine ⟨87727768726085086541962567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116970358301446782055950089 87727768726085086541962567)
  ·
    refine ⟨131591653089127629812943851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87727768726085086541962567 131591653089127629812943851)
    ·
      refine ⟨197387479633691444719415777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131591653089127629812943851 197387479633691444719415777)
      ·
        refine ⟨148040609725268583539561833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197387479633691444719415777 148040609725268583539561833)
        ·
          refine ⟨111030457293951437654671375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148040609725268583539561833 111030457293951437654671375)
          ·
            refine ⟨166545685940927156482007063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111030457293951437654671375 166545685940927156482007063)
            ·
              refine ⟨249818528911390734723010595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166545685940927156482007063 249818528911390734723010595)
              ·
                refine ⟨374727793367086102084515893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249818528911390734723010595 374727793367086102084515893)
                ·
                  refine ⟨35130730628164322070423365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 374727793367086102084515893 35130730628164322070423365)
                  ·
                    refine ⟨6587011992780810388204381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35130730628164322070423365 6587011992780810388204381)
                    ·
                      refine ⟨2470129497292803895576643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6587011992780810388204381 2470129497292803895576643)
                      ·
                        rfl

theorem cell23_4810560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 3].length) (baseStart_4810560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810560 prefixEnd_4810560 := by exact prefixLift 4810560
  have htrace : WordTrace (prefixWord ++ tailWord_4810560) baseStart_4810560 baseEnd_4810560 := by
    simpa [prefixWord, tailWord_4810560, baseEnd_4810560] using wordTrace_append hprefix tailTrace_4810560
  have hstable : (prefixWord ++ tailWord_4810560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810560).length < 2 ^ (prefixWord ++ tailWord_4810560).sum := by decide
  have hdescent : baseEnd_4810560 < baseStart_4810560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810594 : List Nat := [3, 3, 2, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_4810594 : Nat := 118140960795 + 4810594 * 2 ^ 59
def prefixEnd_4810594 : Nat := 4983230072969 + 3 ^ 40 * 4810594 * 2
def baseEnd_4810594 : Nat := 2470146955635056762551487

theorem tailTrace_4810594 : CollatzResearch.WordTrace tailWord_4810594 prefixEnd_4810594 2470146955635056762551487 := by
  unfold tailWord_4810594
  simp only [CollatzResearch.WordTrace]
  refine ⟨43864194383511749222665709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116971185022697997927108557 43864194383511749222665709)
  ·
    refine ⟨16449072893816905958499641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43864194383511749222665709 16449072893816905958499641)
    ·
      refine ⟨12336804670362679468874731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16449072893816905958499641 12336804670362679468874731)
      ·
        refine ⟨18505207005544019203312097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12336804670362679468874731 18505207005544019203312097)
        ·
          refine ⟨13878905254158014402484073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18505207005544019203312097 13878905254158014402484073)
          ·
            refine ⟨10409178940618510801863055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13878905254158014402484073 10409178940618510801863055)
            ·
              refine ⟨15613768410927766202794583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10409178940618510801863055 15613768410927766202794583)
              ·
                refine ⟨23420652616391649304191875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15613768410927766202794583 23420652616391649304191875)
                ·
                  refine ⟨35130978924587473956287813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23420652616391649304191875 35130978924587473956287813)
                  ·
                    refine ⟨6587058548360151366803965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35130978924587473956287813 6587058548360151366803965)
                    ·
                      refine ⟨2470146955635056762551487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6587058548360151366803965 2470146955635056762551487)
                      ·
                        rfl

theorem cell23_4810594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_4810594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810594 prefixEnd_4810594 := by exact prefixLift 4810594
  have htrace : WordTrace (prefixWord ++ tailWord_4810594) baseStart_4810594 baseEnd_4810594 := by
    simpa [prefixWord, tailWord_4810594, baseEnd_4810594] using wordTrace_append hprefix tailTrace_4810594
  have hstable : (prefixWord ++ tailWord_4810594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810594).length < 2 ^ (prefixWord ++ tailWord_4810594).sum := by decide
  have hdescent : baseEnd_4810594 < baseStart_4810594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810614 : List Nat := [5, 1, 1, 3, 2, 1, 1, 1, 8]
def baseStart_4810614 : Nat := 118140960795 + 4810614 * 2 ^ 59
def prefixEnd_4810614 : Nat := 4983230072969 + 3 ^ 40 * 4810614 * 2
def baseEnd_4810614 : Nat := 274461913916460742700155

theorem tailTrace_4810614 : CollatzResearch.WordTrace tailWord_4810614 prefixEnd_4810614 274461913916460742700155 := by
  unfold tailWord_4810614
  simp only [CollatzResearch.WordTrace]
  refine ⟨10966094187123408769149431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116971671329316360204260597 10966094187123408769149431)
  ·
    refine ⟨16449141280685113153724147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10966094187123408769149431 16449141280685113153724147)
    ·
      refine ⟨24673711921027669730586221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16449141280685113153724147 24673711921027669730586221)
      ·
        refine ⟨9252641970385376148969833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24673711921027669730586221 9252641970385376148969833)
        ·
          refine ⟨6939481477789032111727375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9252641970385376148969833 6939481477789032111727375)
          ·
            refine ⟨10409222216683548167591063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6939481477789032111727375 10409222216683548167591063)
            ·
              refine ⟨15613833325025322251386595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10409222216683548167591063 15613833325025322251386595)
              ·
                refine ⟨23420749987537983377079893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15613833325025322251386595 23420749987537983377079893)
                ·
                  refine ⟨274461913916460742700155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23420749987537983377079893 274461913916460742700155)
                  ·
                    rfl

theorem cell23_4810614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_4810614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810614 prefixEnd_4810614 := by exact prefixLift 4810614
  have htrace : WordTrace (prefixWord ++ tailWord_4810614) baseStart_4810614 baseEnd_4810614 := by
    simpa [prefixWord, tailWord_4810614, baseEnd_4810614] using wordTrace_append hprefix tailTrace_4810614
  have hstable : (prefixWord ++ tailWord_4810614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810614).length < 2 ^ (prefixWord ++ tailWord_4810614).sum := by decide
  have hdescent : baseEnd_4810614 < baseStart_4810614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810624 : List Nat := [2, 1, 1, 2, 1, 2, 6, 1, 3, 1, 3]
def baseStart_4810624 : Nat := 118140960795 + 4810624 * 2 ^ 59
def prefixEnd_4810624 : Nat := 4983230072969 + 3 ^ 40 * 4810624 * 2
def baseEnd_4810624 : Nat := 2470162360054691645176349

theorem tailTrace_4810624 : CollatzResearch.WordTrace tailWord_4810624 prefixEnd_4810624 2470162360054691645176349 := by
  unfold tailWord_4810624
  simp only [CollatzResearch.WordTrace]
  refine ⟨87728935861969156007127463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116971914482625541342836617 87728935861969156007127463)
  ·
    refine ⟨131593403792953734010691195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87728935861969156007127463 131593403792953734010691195)
    ·
      refine ⟨197390105689430601016036793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131593403792953734010691195 197390105689430601016036793)
      ·
        refine ⟨148042579267072950762027595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197390105689430601016036793 148042579267072950762027595)
        ·
          refine ⟨222063868900609426143041393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148042579267072950762027595 222063868900609426143041393)
          ·
            refine ⟨166547901675457069607281045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222063868900609426143041393 166547901675457069607281045)
            ·
              refine ⟨7806932891037050137841299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 166547901675457069607281045 7806932891037050137841299)
              ·
                refine ⟨11710399336555575206761949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7806932891037050137841299 11710399336555575206761949)
                ·
                  refine ⟨4391399751208340702535731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11710399336555575206761949 4391399751208340702535731)
                  ·
                    refine ⟨6587099626812511053803597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4391399751208340702535731 6587099626812511053803597)
                    ·
                      refine ⟨2470162360054691645176349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6587099626812511053803597 2470162360054691645176349)
                      ·
                        rfl

theorem cell23_4810624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 3, 1, 3].length) (baseStart_4810624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810624 prefixEnd_4810624 := by exact prefixLift 4810624
  have htrace : WordTrace (prefixWord ++ tailWord_4810624) baseStart_4810624 baseEnd_4810624 := by
    simpa [prefixWord, tailWord_4810624, baseEnd_4810624] using wordTrace_append hprefix tailTrace_4810624
  have hstable : (prefixWord ++ tailWord_4810624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810624).length < 2 ^ (prefixWord ++ tailWord_4810624).sum := by decide
  have hdescent : baseEnd_4810624 < baseStart_4810624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810644 : List Nat := [2, 4, 2, 1, 1, 2, 1, 4, 1, 5]
def baseStart_4810644 : Nat := 118140960795 + 4810644 * 2 ^ 59
def prefixEnd_4810644 : Nat := 4983230072969 + 3 ^ 40 * 4810644 * 2
def baseEnd_4810644 : Nat := 823390876555927188975419

theorem tailTrace_4810644 : CollatzResearch.WordTrace tailWord_4810644 prefixEnd_4810644 823390876555927188975419 := by
  unfold tailWord_4810644
  simp only [CollatzResearch.WordTrace]
  refine ⟨87729300591932927714991493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116972400789243903619988657 87729300591932927714991493)
  ·
    refine ⟨16449243860987423946560905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87729300591932927714991493 16449243860987423946560905)
    ·
      refine ⟨12336932895740567959920679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16449243860987423946560905 12336932895740567959920679)
      ·
        refine ⟨18505399343610851939881019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12336932895740567959920679 18505399343610851939881019)
        ·
          refine ⟨27758099015416277909821529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18505399343610851939881019 27758099015416277909821529)
          ·
            refine ⟨20818574261562208432366147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27758099015416277909821529 20818574261562208432366147)
            ·
              refine ⟨31227861392343312648549221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20818574261562208432366147 31227861392343312648549221)
              ·
                refine ⟨5855224011064371121602979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31227861392343312648549221 5855224011064371121602979)
                ·
                  refine ⟨8782836016596556682404469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5855224011064371121602979 8782836016596556682404469)
                  ·
                    refine ⟨823390876555927188975419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8782836016596556682404469 823390876555927188975419)
                    ·
                      rfl

theorem cell23_4810644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_4810644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810644 prefixEnd_4810644 := by exact prefixLift 4810644
  have htrace : WordTrace (prefixWord ++ tailWord_4810644) baseStart_4810644 baseEnd_4810644 := by
    simpa [prefixWord, tailWord_4810644, baseEnd_4810644] using wordTrace_append hprefix tailTrace_4810644
  have hstable : (prefixWord ++ tailWord_4810644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810644).length < 2 ^ (prefixWord ++ tailWord_4810644).sum := by decide
  have hdescent : baseEnd_4810644 < baseStart_4810644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810677 : List Nat := [1, 3, 3, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_4810677 : Nat := 118140960795 + 4810677 * 2 ^ 59
def prefixEnd_4810677 : Nat := 4983230072969 + 3 ^ 40 * 4810677 * 2
def baseEnd_4810677 : Nat := 2470189574529379937813605

theorem tailTrace_4810677 : CollatzResearch.WordTrace tailWord_4810677 prefixEnd_4810677 2470189574529379937813605 := by
  unfold tailWord_4810677
  simp only [CollatzResearch.WordTrace]
  refine ⟨175459804792746302065934285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116973203195164201377289523 175459804792746302065934285)
  ·
    refine ⟨65797426797279863274725357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175459804792746302065934285 65797426797279863274725357)
    ·
      refine ⟨24674035048979948728022009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65797426797279863274725357 24674035048979948728022009)
      ·
        refine ⟨18505526286734961546016507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24674035048979948728022009 18505526286734961546016507)
        ·
          refine ⟨27758289430102442319024761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18505526286734961546016507 27758289430102442319024761)
          ·
            refine ⟨20818717072576831739268571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27758289430102442319024761 20818717072576831739268571)
            ·
              refine ⟨31228075608865247608902857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20818717072576831739268571 31228075608865247608902857)
              ·
                refine ⟨23421056706648935706677143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31228075608865247608902857 23421056706648935706677143)
                ·
                  refine ⟨35131585059973403560015715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23421056706648935706677143 35131585059973403560015715)
                  ·
                    refine ⟨52697377589960105340023573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35131585059973403560015715 52697377589960105340023573)
                    ·
                      refine ⟨2470189574529379937813605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52697377589960105340023573 2470189574529379937813605)
                      ·
                        rfl

theorem cell23_4810677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_4810677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810677 prefixEnd_4810677 := by exact prefixLift 4810677
  have htrace : WordTrace (prefixWord ++ tailWord_4810677) baseStart_4810677 baseEnd_4810677 := by
    simpa [prefixWord, tailWord_4810677, baseEnd_4810677] using wordTrace_append hprefix tailTrace_4810677
  have hstable : (prefixWord ++ tailWord_4810677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810677).length < 2 ^ (prefixWord ++ tailWord_4810677).sum := by decide
  have hdescent : baseEnd_4810677 < baseStart_4810677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810794 : List Nat := [3, 1, 4, 1, 2, 1, 1, 3, 7]
def baseStart_4810794 : Nat := 118140960795 + 4810794 * 2 ^ 59
def prefixEnd_4810794 : Nat := 4983230072969 + 3 ^ 40 * 4810794 * 2
def baseEnd_4810794 : Nat := 274472183529550664450063

theorem tailTrace_4810794 : CollatzResearch.WordTrace tailWord_4810794 prefixEnd_4810794 274472183529550664450063 := by
  unfold tailWord_4810794
  simp only [CollatzResearch.WordTrace]
  refine ⟨43866018033330607761985859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116976048088881620698628957 43866018033330607761985859)
  ·
    refine ⟨65799027049995911642978789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43866018033330607761985859 65799027049995911642978789)
    ·
      refine ⟨12337317571874233433058523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65799027049995911642978789 12337317571874233433058523)
      ·
        refine ⟨18505976357811350149587785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12337317571874233433058523 18505976357811350149587785)
        ·
          refine ⟨13879482268358512612190839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18505976357811350149587785 13879482268358512612190839)
          ·
            refine ⟨20819223402537768918286259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13879482268358512612190839 20819223402537768918286259)
            ·
              refine ⟨31228835103806653377429389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20819223402537768918286259 31228835103806653377429389)
              ·
                refine ⟨11710813163927495016536021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31228835103806653377429389 11710813163927495016536021)
                ·
                  refine ⟨274472183529550664450063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11710813163927495016536021 274472183529550664450063)
                  ·
                    rfl

theorem cell23_4810794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 7].length) (baseStart_4810794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810794 prefixEnd_4810794 := by exact prefixLift 4810794
  have htrace : WordTrace (prefixWord ++ tailWord_4810794) baseStart_4810794 baseEnd_4810794 := by
    simpa [prefixWord, tailWord_4810794, baseEnd_4810794] using wordTrace_append hprefix tailTrace_4810794
  have hstable : (prefixWord ++ tailWord_4810794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810794).length < 2 ^ (prefixWord ++ tailWord_4810794).sum := by decide
  have hdescent : baseEnd_4810794 < baseStart_4810794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810807 : List Nat := [1, 1, 3, 1, 2, 2, 3, 2, 1, 7]
def baseStart_4810807 : Nat := 118140960795 + 4810807 * 2 ^ 59
def prefixEnd_4810807 : Nat := 4983230072969 + 3 ^ 40 * 4810807 * 2
def baseEnd_4810807 : Nat := 823418775671488143062669

theorem tailTrace_4810807 : CollatzResearch.WordTrace tailWord_4810807 prefixEnd_4810807 823418775671488143062669 := by
  unfold tailWord_4810807
  simp only [CollatzResearch.WordTrace]
  refine ⟨175464546282275334268166675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116976364188183556178777783 175464546282275334268166675)
  ·
    refine ⟨263196819423413001402250013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175464546282275334268166675 263196819423413001402250013)
    ·
      refine ⟨98698807283779875525843755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263196819423413001402250013 98698807283779875525843755)
      ·
        refine ⟨148048210925669813288765633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98698807283779875525843755 148048210925669813288765633)
        ·
          refine ⟨111036158194252359966574225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148048210925669813288765633 111036158194252359966574225)
          ·
            refine ⟨83277118645689269974930669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111036158194252359966574225 83277118645689269974930669)
            ·
              refine ⟨31228919492133476240599001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83277118645689269974930669 31228919492133476240599001)
              ·
                refine ⟨23421689619100107180449251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31228919492133476240599001 23421689619100107180449251)
                ·
                  refine ⟨35132534428650160770673877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23421689619100107180449251 35132534428650160770673877)
                  ·
                    refine ⟨823418775671488143062669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35132534428650160770673877 823418775671488143062669)
                    ·
                      rfl

theorem cell23_4810807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_4810807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810807 prefixEnd_4810807 := by exact prefixLift 4810807
  have htrace : WordTrace (prefixWord ++ tailWord_4810807) baseStart_4810807 baseEnd_4810807 := by
    simpa [prefixWord, tailWord_4810807, baseEnd_4810807] using wordTrace_append hprefix tailTrace_4810807
  have hstable : (prefixWord ++ tailWord_4810807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810807).length < 2 ^ (prefixWord ++ tailWord_4810807).sum := by decide
  have hdescent : baseEnd_4810807 < baseStart_4810807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810845 : List Nat := [1, 4, 4, 1, 1, 2, 3, 2, 5]
def baseStart_4810845 : Nat := 118140960795 + 4810845 * 2 ^ 59
def prefixEnd_4810845 : Nat := 4983230072969 + 3 ^ 40 * 4810845 * 2
def baseEnd_4810845 : Nat := 274475093253259475612537

theorem tailTrace_4810845 : CollatzResearch.WordTrace tailWord_4810845 prefixEnd_4810845 274475093253259475612537 := by
  unfold tailWord_4810845
  simp only [CollatzResearch.WordTrace]
  refine ⟨175465932256137666758049989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116977288170758444505366659 175465932256137666758049989)
  ·
    refine ⟨32899862298025812517134373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175465932256137666758049989 32899862298025812517134373)
    ·
      refine ⟨6168724180879839846962695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32899862298025812517134373 6168724180879839846962695)
      ·
        refine ⟨9253086271319759770444043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6168724180879839846962695 9253086271319759770444043)
        ·
          refine ⟨13879629406979639655666065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9253086271319759770444043 13879629406979639655666065)
          ·
            refine ⟨10409722055234729741749549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13879629406979639655666065 10409722055234729741749549)
            ·
              refine ⟨3903645770713023653156081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10409722055234729741749549 3903645770713023653156081)
              ·
                refine ⟨2927734328034767739867061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3903645770713023653156081 2927734328034767739867061)
                ·
                  refine ⟨274475093253259475612537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2927734328034767739867061 274475093253259475612537)
                  ·
                    rfl

theorem cell23_4810845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 5].length) (baseStart_4810845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810845 prefixEnd_4810845 := by exact prefixLift 4810845
  have htrace : WordTrace (prefixWord ++ tailWord_4810845) baseStart_4810845 baseEnd_4810845 := by
    simpa [prefixWord, tailWord_4810845, baseEnd_4810845] using wordTrace_append hprefix tailTrace_4810845
  have hstable : (prefixWord ++ tailWord_4810845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810845).length < 2 ^ (prefixWord ++ tailWord_4810845).sum := by decide
  have hdescent : baseEnd_4810845 < baseStart_4810845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810847 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 5]
def baseStart_4810847 : Nat := 118140960795 + 4810847 * 2 ^ 59
def prefixEnd_4810847 : Nat := 4983230072969 + 3 ^ 40 * 4810847 * 2
def baseEnd_4810847 : Nat := 2470276866240644272687823

theorem tailTrace_4810847 : CollatzResearch.WordTrace tailWord_4810847 prefixEnd_4810847 2470276866240644272687823 := by
  unfold tailWord_4810847
  simp only [CollatzResearch.WordTrace]
  refine ⟨175466005202130421099622795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116977336801420280733081863 175466005202130421099622795)
  ·
    refine ⟨263199007803195631649434193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175466005202130421099622795 263199007803195631649434193)
    ·
      refine ⟨197399255852396723737075645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263199007803195631649434193 197399255852396723737075645)
      ·
        refine ⟨74024720944648771401403367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197399255852396723737075645 74024720944648771401403367)
        ·
          refine ⟨111037081416973157102105051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74024720944648771401403367 111037081416973157102105051)
          ·
            refine ⟨166555622125459735653157577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111037081416973157102105051 166555622125459735653157577)
            ·
              refine ⟨124916716594094801739868183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166555622125459735653157577 124916716594094801739868183)
              ·
                refine ⟨187375074891142202609802275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124916716594094801739868183 187375074891142202609802275)
                ·
                  refine ⟨281062612336713303914703413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187375074891142202609802275 281062612336713303914703413)
                  ·
                    refine ⟨26349619906566872242003445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 281062612336713303914703413 26349619906566872242003445)
                    ·
                      refine ⟨2470276866240644272687823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26349619906566872242003445 2470276866240644272687823)
                      ·
                        rfl

theorem cell23_4810847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_4810847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810847 prefixEnd_4810847 := by exact prefixLift 4810847
  have htrace : WordTrace (prefixWord ++ tailWord_4810847) baseStart_4810847 baseEnd_4810847 := by
    simpa [prefixWord, tailWord_4810847, baseEnd_4810847] using wordTrace_append hprefix tailTrace_4810847
  have hstable : (prefixWord ++ tailWord_4810847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810847).length < 2 ^ (prefixWord ++ tailWord_4810847).sum := by decide
  have hdescent : baseEnd_4810847 < baseStart_4810847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810861 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 1, 6, 2]
def baseStart_4810861 : Nat := 118140960795 + 4810861 * 2 ^ 59
def prefixEnd_4810861 : Nat := 4983230072969 + 3 ^ 40 * 4810861 * 2
def baseEnd_4810861 : Nat := 2470284054969807217912759

theorem tailTrace_4810861 : CollatzResearch.WordTrace tailWord_4810861 prefixEnd_4810861 2470284054969807217912759 := by
  unfold tailWord_4810861
  simp only [CollatzResearch.WordTrace]
  refine ⟨175466515824079701490632437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116977677216053134327088291 175466515824079701490632437)
  ·
    refine ⟨16449985858507472014746791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 175466515824079701490632437 16449985858507472014746791)
    ·
      refine ⟨24674978787761208022120187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16449985858507472014746791 24674978787761208022120187)
      ·
        refine ⟨37012468181641812033180281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24674978787761208022120187 37012468181641812033180281)
        ·
          refine ⟨27759351136231359024885211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37012468181641812033180281 27759351136231359024885211)
          ·
            refine ⟨41639026704347038537327817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27759351136231359024885211 41639026704347038537327817)
            ·
              refine ⟨31229270028260278902995863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41639026704347038537327817 31229270028260278902995863)
              ·
                refine ⟨46843905042390418354493795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31229270028260278902995863 46843905042390418354493795)
                ·
                  refine ⟨70265857563585627531740693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46843905042390418354493795 70265857563585627531740693)
                  ·
                    refine ⟨3293712073293076290550345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70265857563585627531740693 3293712073293076290550345)
                    ·
                      refine ⟨2470284054969807217912759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3293712073293076290550345 2470284054969807217912759)
                      ·
                        rfl

theorem cell23_4810861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_4810861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810861 prefixEnd_4810861 := by exact prefixLift 4810861
  have htrace : WordTrace (prefixWord ++ tailWord_4810861) baseStart_4810861 baseEnd_4810861 := by
    simpa [prefixWord, tailWord_4810861, baseEnd_4810861] using wordTrace_append hprefix tailTrace_4810861
  have hstable : (prefixWord ++ tailWord_4810861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810861).length < 2 ^ (prefixWord ++ tailWord_4810861).sum := by decide
  have hdescent : baseEnd_4810861 < baseStart_4810861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810932 : List Nat := [2, 5, 3, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_4810932 : Nat := 118140960795 + 4810932 * 2 ^ 59
def prefixEnd_4810932 : Nat := 4983230072969 + 3 ^ 40 * 4810932 * 2
def baseEnd_4810932 : Nat := 2470320512096276440124933

theorem tailTrace_4810932 : CollatzResearch.WordTrace tailWord_4810932 prefixEnd_4810932 2470320512096276440124933 := by
  unfold tailWord_4810932
  simp only [CollatzResearch.WordTrace]
  refine ⟨87734552703411240308233525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116979403604548320410978033 87734552703411240308233525)
  ·
    refine ⟨8225114315944803778896893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87734552703411240308233525 8225114315944803778896893)
    ·
      refine ⟨3084417868479301417086335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8225114315944803778896893 3084417868479301417086335)
      ·
        refine ⟨4626626802718952125629503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3084417868479301417086335 4626626802718952125629503)
        ·
          refine ⟨6939940204078428188444255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4626626802718952125629503 6939940204078428188444255)
          ·
            refine ⟨10409910306117642282666383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6939940204078428188444255 10409910306117642282666383)
            ·
              refine ⟨15614865459176463423999575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10409910306117642282666383 15614865459176463423999575)
              ·
                refine ⟨23422298188764695135999363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15614865459176463423999575 23422298188764695135999363)
                ·
                  refine ⟨35133447283147042703999045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23422298188764695135999363 35133447283147042703999045)
                  ·
                    refine ⟨6587521365590070506999821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35133447283147042703999045 6587521365590070506999821)
                    ·
                      refine ⟨2470320512096276440124933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6587521365590070506999821 2470320512096276440124933)
                      ·
                        rfl

theorem cell23_4810932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_4810932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810932 prefixEnd_4810932 := by exact prefixLift 4810932
  have htrace : WordTrace (prefixWord ++ tailWord_4810932) baseStart_4810932 baseEnd_4810932 := by
    simpa [prefixWord, tailWord_4810932, baseEnd_4810932] using wordTrace_append hprefix tailTrace_4810932
  have hstable : (prefixWord ++ tailWord_4810932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810932).length < 2 ^ (prefixWord ++ tailWord_4810932).sum := by decide
  have hdescent : baseEnd_4810932 < baseStart_4810932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810938 : List Nat := [3, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2]
def baseStart_4810938 : Nat := 118140960795 + 4810938 * 2 ^ 59
def prefixEnd_4810938 : Nat := 4983230072969 + 3 ^ 40 * 4810938 * 2
def baseEnd_4810938 : Nat := 2470323592980203416649905

theorem tailTrace_4810938 : CollatzResearch.WordTrace tailWord_4810938 prefixEnd_4810938 2470323592980203416649905 := by
  unfold tailWord_4810938
  simp only [CollatzResearch.WordTrace]
  refine ⟨43867331061200185910296367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116979549496533829094123645 43867331061200185910296367)
  ·
    refine ⟨65800996591800278865444551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43867331061200185910296367 65800996591800278865444551)
    ·
      refine ⟨98701494887700418298166827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65800996591800278865444551 98701494887700418298166827)
      ·
        refine ⟨148052242331550627447250241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98701494887700418298166827 148052242331550627447250241)
        ·
          refine ⟨111039181748662970585437681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148052242331550627447250241 111039181748662970585437681)
          ·
            refine ⟨83279386311497227939078261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111039181748662970585437681 83279386311497227939078261)
            ·
              refine ⟨7807442466702865119288587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83279386311497227939078261 7807442466702865119288587)
              ·
                refine ⟨11711163700054297678932881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7807442466702865119288587 11711163700054297678932881)
                ·
                  refine ⟨8783372775040723259199661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11711163700054297678932881 8783372775040723259199661)
                  ·
                    refine ⟨3293764790640271222199873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8783372775040723259199661 3293764790640271222199873)
                    ·
                      refine ⟨2470323592980203416649905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3293764790640271222199873 2470323592980203416649905)
                      ·
                        rfl

theorem cell23_4810938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2].length) (baseStart_4810938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810938 prefixEnd_4810938 := by exact prefixLift 4810938
  have htrace : WordTrace (prefixWord ++ tailWord_4810938) baseStart_4810938 baseEnd_4810938 := by
    simpa [prefixWord, tailWord_4810938, baseEnd_4810938] using wordTrace_append hprefix tailTrace_4810938
  have hstable : (prefixWord ++ tailWord_4810938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810938).length < 2 ^ (prefixWord ++ tailWord_4810938).sum := by decide
  have hdescent : baseEnd_4810938 < baseStart_4810938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810948 : List Nat := [2, 3, 3, 1, 2, 2, 1, 3, 1, 5]
def baseStart_4810948 : Nat := 118140960795 + 4810948 * 2 ^ 59
def prefixEnd_4810948 : Nat := 4983230072969 + 3 ^ 40 * 4810948 * 2
def baseEnd_4810948 : Nat := 823442909262249459174953

theorem tailTrace_4810948 : CollatzResearch.WordTrace tailWord_4810948 prefixEnd_4810948 823442909262249459174953 := by
  unfold tailWord_4810948
  simp only [CollatzResearch.WordTrace]
  refine ⟨87734844487382257674524749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116979792649843010232699665 87734844487382257674524749)
  ·
    refine ⟨32900566682768346627946781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87734844487382257674524749 32900566682768346627946781)
    ·
      refine ⟨12337712506038129985480043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32900566682768346627946781 12337712506038129985480043)
      ·
        refine ⟨18506568759057194978220065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12337712506038129985480043 18506568759057194978220065)
        ·
          refine ⟨13879926569292896233665049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18506568759057194978220065 13879926569292896233665049)
          ·
            refine ⟨10409944926969672175248787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13879926569292896233665049 10409944926969672175248787)
            ·
              refine ⟨15614917390454508262873181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10409944926969672175248787 15614917390454508262873181)
              ·
                refine ⟨5855594021420440598577443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15614917390454508262873181 5855594021420440598577443)
                ·
                  refine ⟨8783391032130660897866165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5855594021420440598577443 8783391032130660897866165)
                  ·
                    refine ⟨823442909262249459174953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8783391032130660897866165 823442909262249459174953)
                    ·
                      rfl

theorem cell23_4810948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_4810948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810948 prefixEnd_4810948 := by exact prefixLift 4810948
  have htrace : WordTrace (prefixWord ++ tailWord_4810948) baseStart_4810948 baseEnd_4810948 := by
    simpa [prefixWord, tailWord_4810948, baseEnd_4810948] using wordTrace_append hprefix tailTrace_4810948
  have hstable : (prefixWord ++ tailWord_4810948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810948).length < 2 ^ (prefixWord ++ tailWord_4810948).sum := by decide
  have hdescent : baseEnd_4810948 < baseStart_4810948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810981 : List Nat := [1, 3, 1, 4, 2, 2, 1, 1, 1, 1, 6]
def baseStart_4810981 : Nat := 118140960795 + 4810981 * 2 ^ 59
def prefixEnd_4810981 : Nat := 4983230072969 + 3 ^ 40 * 4810981 * 2
def baseEnd_4810981 : Nat := 2470345672648346748412207

theorem tailTrace_4810981 : CollatzResearch.WordTrace tailWord_4810981 prefixEnd_4810981 2470345672648346748412207 := by
  unfold tailWord_4810981
  simp only [CollatzResearch.WordTrace]
  refine ⟨175470892583644961985000797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116980595055763307990000531 175470892583644961985000797)
  ·
    refine ⟨65801584718866860744375299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175470892583644961985000797 65801584718866860744375299)
    ·
      refine ⟨98702377078300291116562949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65801584718866860744375299 98702377078300291116562949)
      ·
        refine ⟨18506695702181304584355553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98702377078300291116562949 18506695702181304584355553)
        ·
          refine ⟨13880021776635978438266665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18506695702181304584355553 13880021776635978438266665)
          ·
            refine ⟨10410016332476983828699999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13880021776635978438266665 10410016332476983828699999)
            ·
              refine ⟨15615024498715475743049999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10410016332476983828699999 15615024498715475743049999)
              ·
                refine ⟨23422536748073213614574999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15615024498715475743049999 23422536748073213614574999)
                ·
                  refine ⟨35133805122109820421862499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23422536748073213614574999 35133805122109820421862499)
                  ·
                    refine ⟨52700707683164730632793749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35133805122109820421862499 52700707683164730632793749)
                    ·
                      refine ⟨2470345672648346748412207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52700707683164730632793749 2470345672648346748412207)
                      ·
                        rfl

theorem cell23_4810981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_4810981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810981 prefixEnd_4810981 := by exact prefixLift 4810981
  have htrace : WordTrace (prefixWord ++ tailWord_4810981) baseStart_4810981 baseEnd_4810981 := by
    simpa [prefixWord, tailWord_4810981, baseEnd_4810981] using wordTrace_append hprefix tailTrace_4810981
  have hstable : (prefixWord ++ tailWord_4810981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810981).length < 2 ^ (prefixWord ++ tailWord_4810981).sum := by decide
  have hdescent : baseEnd_4810981 < baseStart_4810981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810988 : List Nat := [2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 3]
def baseStart_4810988 : Nat := 118140960795 + 4810988 * 2 ^ 59
def prefixEnd_4810988 : Nat := 4983230072969 + 3 ^ 40 * 4810988 * 2
def baseEnd_4810988 : Nat := 2470349267012928221024675

theorem tailTrace_4810988 : CollatzResearch.WordTrace tailWord_4810988 prefixEnd_4810988 2470349267012928221024675 := by
  unfold tailWord_4810988
  simp only [CollatzResearch.WordTrace]
  refine ⟨87735573947309801090252809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116980765263079734787003745 87735573947309801090252809)
  ·
    refine ⟨65801680460482350817689607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87735573947309801090252809 65801680460482350817689607)
    ·
      refine ⟨98702520690723526226534411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65801680460482350817689607 98702520690723526226534411)
      ·
        refine ⟨148053781036085289339801617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98702520690723526226534411 148053781036085289339801617)
        ·
          refine ⟨111040335777063967004851213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148053781036085289339801617 111040335777063967004851213)
          ·
            refine ⟨41640125916398987626819205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111040335777063967004851213 41640125916398987626819205)
            ·
              refine ⟨7807523609324810180028601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41640125916398987626819205 7807523609324810180028601)
              ·
                refine ⟨5855642706993607635021451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7807523609324810180028601 5855642706993607635021451)
                ·
                  refine ⟨8783464060490411452532177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5855642706993607635021451 8783464060490411452532177)
                  ·
                    refine ⟨6587598045367808589399133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8783464060490411452532177 6587598045367808589399133)
                    ·
                      refine ⟨2470349267012928221024675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6587598045367808589399133 2470349267012928221024675)
                      ·
                        rfl

theorem cell23_4810988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 3].length) (baseStart_4810988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810988 prefixEnd_4810988 := by exact prefixLift 4810988
  have htrace : WordTrace (prefixWord ++ tailWord_4810988) baseStart_4810988 baseEnd_4810988 := by
    simpa [prefixWord, tailWord_4810988, baseEnd_4810988] using wordTrace_append hprefix tailTrace_4810988
  have hstable : (prefixWord ++ tailWord_4810988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810988).length < 2 ^ (prefixWord ++ tailWord_4810988).sum := by decide
  have hdescent : baseEnd_4810988 < baseStart_4810988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4810991 : List Nat := [1, 1, 2, 1, 6, 1, 4, 7]
def baseStart_4810991 : Nat := 118140960795 + 4810991 * 2 ^ 59
def prefixEnd_4810991 : Nat := 4983230072969 + 3 ^ 40 * 4810991 * 2
def baseEnd_4810991 : Nat := 91494474350181174418043

theorem tailTrace_4810991 : CollatzResearch.WordTrace tailWord_4810991 prefixEnd_4810991 91494474350181174418043 := by
  unfold tailWord_4810991
  simp only [CollatzResearch.WordTrace]
  refine ⟨175471257313608733692864827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116980838209072489128576551 175471257313608733692864827)
  ·
    refine ⟨263206885970413100539297241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175471257313608733692864827 263206885970413100539297241)
    ·
      refine ⟨197405164477809825404472931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263206885970413100539297241 197405164477809825404472931)
      ·
        refine ⟨296107746716714738106709397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197405164477809825404472931 296107746716714738106709397)
        ·
          refine ⟨13880050627346003348752003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 296107746716714738106709397 13880050627346003348752003)
          ·
            refine ⟨20820075941019005023128005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13880050627346003348752003 20820075941019005023128005)
            ·
              refine ⟨3903764238941063441836501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20820075941019005023128005 3903764238941063441836501)
              ·
                refine ⟨91494474350181174418043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3903764238941063441836501 91494474350181174418043)
                ·
                  rfl

theorem cell23_4810991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 7].length) (baseStart_4810991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4810991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4810991 prefixEnd_4810991 := by exact prefixLift 4810991
  have htrace : WordTrace (prefixWord ++ tailWord_4810991) baseStart_4810991 baseEnd_4810991 := by
    simpa [prefixWord, tailWord_4810991, baseEnd_4810991] using wordTrace_append hprefix tailTrace_4810991
  have hstable : (prefixWord ++ tailWord_4810991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4810991).length < 2 ^ (prefixWord ++ tailWord_4810991).sum := by decide
  have hdescent : baseEnd_4810991 < baseStart_4810991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4810991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811002 : List Nat := [3, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2]
def baseStart_4811002 : Nat := 118140960795 + 4811002 * 2 ^ 59
def prefixEnd_4811002 : Nat := 4983230072969 + 3 ^ 40 * 4811002 * 2
def baseEnd_4811002 : Nat := 2470356455742091166249611

theorem tailTrace_4811002 : CollatzResearch.WordTrace tailWord_4811002 prefixEnd_4811002 2470356455742091166249611 := by
  unfold tailWord_4811002
  simp only [CollatzResearch.WordTrace]
  refine ⟨43867914629142220642878815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116981105677712588381010173 43867914629142220642878815)
  ·
    refine ⟨65801871943713330964318223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43867914629142220642878815 65801871943713330964318223)
    ·
      refine ⟨98702807915569996446477335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65801871943713330964318223 98702807915569996446477335)
      ·
        refine ⟨148054211873354994669716003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98702807915569996446477335 148054211873354994669716003)
        ·
          refine ⟨222081317810032492004574005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148054211873354994669716003 222081317810032492004574005)
          ·
            refine ⟨20820123544690546125428813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 222081317810032492004574005 20820123544690546125428813)
            ·
              refine ⟨7807546329258954797035805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20820123544690546125428813 7807546329258954797035805)
              ·
                refine ⟨2927829873472108048888427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7807546329258954797035805 2927829873472108048888427)
                ·
                  refine ⟨4391744810208162073332641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2927829873472108048888427 4391744810208162073332641)
                  ·
                    refine ⟨3293808607656121554999481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4391744810208162073332641 3293808607656121554999481)
                    ·
                      refine ⟨2470356455742091166249611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3293808607656121554999481 2470356455742091166249611)
                      ·
                        rfl

theorem cell23_4811002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2].length) (baseStart_4811002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811002 prefixEnd_4811002 := by exact prefixLift 4811002
  have htrace : WordTrace (prefixWord ++ tailWord_4811002) baseStart_4811002 baseEnd_4811002 := by
    simpa [prefixWord, tailWord_4811002, baseEnd_4811002] using wordTrace_append hprefix tailTrace_4811002
  have hstable : (prefixWord ++ tailWord_4811002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811002).length < 2 ^ (prefixWord ++ tailWord_4811002).sum := by decide
  have hdescent : baseEnd_4811002 < baseStart_4811002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811018 : List Nat := [3, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3]
def baseStart_4811018 : Nat := 118140960795 + 4811018 * 2 ^ 59
def prefixEnd_4811018 : Nat := 4983230072969 + 3 ^ 40 * 4811018 * 2
def baseEnd_4811018 : Nat := 2470364671432563103649537

theorem tailTrace_4811018 : CollatzResearch.WordTrace tailWord_4811018 prefixEnd_4811018 2470364671432563103649537 := by
  unfold tailWord_4811018
  simp only [CollatzResearch.WordTrace]
  refine ⟨43868060521127729326024427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116981494723007278202731805 43868060521127729326024427)
  ·
    refine ⟨65802090781691593989036641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43868060521127729326024427 65802090781691593989036641)
    ·
      refine ⟨49351568086268695491777481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65802090781691593989036641 49351568086268695491777481)
      ·
        refine ⟨37013676064701521618833111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49351568086268695491777481 37013676064701521618833111)
        ·
          refine ⟨55520514097052282428249667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37013676064701521618833111 55520514097052282428249667)
          ·
            refine ⟨83280771145578423642374501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55520514097052282428249667 83280771145578423642374501)
            ·
              refine ⟨15615144589795954432945219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83280771145578423642374501 15615144589795954432945219)
              ·
                refine ⟨23422716884693931649417829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15615144589795954432945219 23422716884693931649417829)
                ·
                  refine ⟨4391759415880112184265843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23422716884693931649417829 4391759415880112184265843)
                  ·
                    refine ⟨6587639123820168276398765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4391759415880112184265843 6587639123820168276398765)
                    ·
                      refine ⟨2470364671432563103649537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6587639123820168276398765 2470364671432563103649537)
                      ·
                        rfl

theorem cell23_4811018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_4811018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811018 prefixEnd_4811018 := by exact prefixLift 4811018
  have htrace : WordTrace (prefixWord ++ tailWord_4811018) baseStart_4811018 baseEnd_4811018 := by
    simpa [prefixWord, tailWord_4811018, baseEnd_4811018] using wordTrace_append hprefix tailTrace_4811018
  have hstable : (prefixWord ++ tailWord_4811018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811018).length < 2 ^ (prefixWord ++ tailWord_4811018).sum := by decide
  have hdescent : baseEnd_4811018 < baseStart_4811018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811035 : List Nat := [1, 1, 1, 1, 1, 1, 10, 1, 2, 1, 3]
def baseStart_4811035 : Nat := 118140960795 + 4811035 * 2 ^ 59
def prefixEnd_4811035 : Nat := 4983230072969 + 3 ^ 40 * 4811035 * 2
def baseEnd_4811035 : Nat := 2470373400603689537136959

theorem tailTrace_4811035 : CollatzResearch.WordTrace tailWord_4811035 prefixEnd_4811035 2470373400603689537136959 := by
  unfold tailWord_4811035
  simp only [CollatzResearch.WordTrace]
  refine ⟨175472862125449329207466559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116981908083632886138311039 175472862125449329207466559)
  ·
    refine ⟨263209293188173993811199839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175472862125449329207466559 263209293188173993811199839)
    ·
      refine ⟨394813939782260990716799759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263209293188173993811199839 394813939782260990716799759)
      ·
        refine ⟨592220909673391486075199639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394813939782260990716799759 592220909673391486075199639)
        ·
          refine ⟨888331364510087229112799459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 592220909673391486075199639 888331364510087229112799459)
          ·
            refine ⟨1332497046765130843669199189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888331364510087229112799459 1332497046765130843669199189)
            ·
              refine ⟨3903799941694719268562107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1332497046765130843669199189 3903799941694719268562107)
              ·
                refine ⟨5855699912542078902843161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3903799941694719268562107 5855699912542078902843161)
                ·
                  refine ⟨4391774934406559177132371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5855699912542078902843161 4391774934406559177132371)
                  ·
                    refine ⟨6587662401609838765698557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4391774934406559177132371 6587662401609838765698557)
                    ·
                      refine ⟨2470373400603689537136959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6587662401609838765698557 2470373400603689537136959)
                      ·
                        rfl

theorem cell23_4811035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 2, 1, 3].length) (baseStart_4811035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811035 prefixEnd_4811035 := by exact prefixLift 4811035
  have htrace : WordTrace (prefixWord ++ tailWord_4811035) baseStart_4811035 baseEnd_4811035 := by
    simpa [prefixWord, tailWord_4811035, baseEnd_4811035] using wordTrace_append hprefix tailTrace_4811035
  have hstable : (prefixWord ++ tailWord_4811035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811035).length < 2 ^ (prefixWord ++ tailWord_4811035).sum := by decide
  have hdescent : baseEnd_4811035 < baseStart_4811035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811045 : List Nat := [1, 3, 1, 2, 5, 1, 1, 1, 3, 3, 2]
def baseStart_4811045 : Nat := 118140960795 + 4811045 * 2 ^ 59
def prefixEnd_4811045 : Nat := 4983230072969 + 3 ^ 40 * 4811045 * 2
def baseEnd_4811045 : Nat := 2470378535410234498011913

theorem tailTrace_4811045 : CollatzResearch.WordTrace tailWord_4811045 prefixEnd_4811045 2470378535410234498011913 := by
  unfold tailWord_4811045
  simp only [CollatzResearch.WordTrace]
  refine ⟨175473226855413100915330589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116982151236942067276887059 175473226855413100915330589)
  ·
    refine ⟨65802460070779912843248971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175473226855413100915330589 65802460070779912843248971)
    ·
      refine ⟨98703690106169869264873457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65802460070779912843248971 98703690106169869264873457)
      ·
        refine ⟨74027767579627401948655093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98703690106169869264873457 74027767579627401948655093)
        ·
          refine ⟨6940103210590068932686415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74027767579627401948655093 6940103210590068932686415)
          ·
            refine ⟨10410154815885103399029623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6940103210590068932686415 10410154815885103399029623)
            ·
              refine ⟨15615232223827655098544435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10410154815885103399029623 15615232223827655098544435)
              ·
                refine ⟨23422848335741482647816653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15615232223827655098544435 23422848335741482647816653)
                ·
                  refine ⟨8783568125903055992931245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23422848335741482647816653 8783568125903055992931245)
                  ·
                    refine ⟨3293838047213645997349217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8783568125903055992931245 3293838047213645997349217)
                    ·
                      refine ⟨2470378535410234498011913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3293838047213645997349217 2470378535410234498011913)
                      ·
                        rfl

theorem cell23_4811045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 3, 2].length) (baseStart_4811045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811045 prefixEnd_4811045 := by exact prefixLift 4811045
  have htrace : WordTrace (prefixWord ++ tailWord_4811045) baseStart_4811045 baseEnd_4811045 := by
    simpa [prefixWord, tailWord_4811045, baseEnd_4811045] using wordTrace_append hprefix tailTrace_4811045
  have hstable : (prefixWord ++ tailWord_4811045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811045).length < 2 ^ (prefixWord ++ tailWord_4811045).sum := by decide
  have hdescent : baseEnd_4811045 < baseStart_4811045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811061 : List Nat := [1, 3, 3, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_4811061 : Nat := 118140960795 + 4811061 * 2 ^ 59
def prefixEnd_4811061 : Nat := 4983230072969 + 3 ^ 40 * 4811061 * 2
def baseEnd_4811061 : Nat := 2470386751100706435411839

theorem tailTrace_4811061 : CollatzResearch.WordTrace tailWord_4811061 prefixEnd_4811061 2470386751100706435411839 := by
  unfold tailWord_4811061
  simp only [CollatzResearch.WordTrace]
  refine ⟨175473810423355135647913037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116982540282236757098608691 175473810423355135647913037)
  ·
    refine ⟨65802678908758175867967389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175473810423355135647913037 65802678908758175867967389)
    ·
      refine ⟨24676004590784315950487771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65802678908758175867967389 24676004590784315950487771)
      ·
        refine ⟨37014006886176473925731657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24676004590784315950487771 37014006886176473925731657)
        ·
          refine ⟨27760505164632355444298743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37014006886176473925731657 27760505164632355444298743)
          ·
            refine ⟨41640757746948533166448115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27760505164632355444298743 41640757746948533166448115)
            ·
              refine ⟨62461136620422799749672173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41640757746948533166448115 62461136620422799749672173)
              ·
                refine ⟨23422926232658549906127065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62461136620422799749672173 23422926232658549906127065)
                ·
                  refine ⟨17567194674493912429595299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23422926232658549906127065 17567194674493912429595299)
                  ·
                    refine ⟨26350792011740868644392949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17567194674493912429595299 26350792011740868644392949)
                    ·
                      refine ⟨2470386751100706435411839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26350792011740868644392949 2470386751100706435411839)
                      ·
                        rfl

theorem cell23_4811061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_4811061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811061 prefixEnd_4811061 := by exact prefixLift 4811061
  have htrace : WordTrace (prefixWord ++ tailWord_4811061) baseStart_4811061 baseEnd_4811061 := by
    simpa [prefixWord, tailWord_4811061, baseEnd_4811061] using wordTrace_append hprefix tailTrace_4811061
  have hstable : (prefixWord ++ tailWord_4811061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811061).length < 2 ^ (prefixWord ++ tailWord_4811061).sum := by decide
  have hdescent : baseEnd_4811061 < baseStart_4811061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811071 : List Nat := [1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 4]
def baseStart_4811071 : Nat := 118140960795 + 4811071 * 2 ^ 59
def prefixEnd_4811071 : Nat := 4983230072969 + 3 ^ 40 * 4811071 * 2
def baseEnd_4811071 : Nat := 2470391885907251396286793

theorem tailTrace_4811071 : CollatzResearch.WordTrace tailWord_4811071 prefixEnd_4811071 2470391885907251396286793 := by
  unfold tailWord_4811071
  simp only [CollatzResearch.WordTrace]
  refine ⟨175474175153318907355777067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116982783435545938237184711 175474175153318907355777067)
  ·
    refine ⟨263211262729978361033665601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175474175153318907355777067 263211262729978361033665601)
    ·
      refine ⟨197408447047483770775249201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263211262729978361033665601 197408447047483770775249201)
      ·
        refine ⟨148056335285612828081436901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197408447047483770775249201 148056335285612828081436901)
        ·
          refine ⟨27760562866052405265269419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148056335285612828081436901 27760562866052405265269419)
          ·
            refine ⟨41640844299078607897904129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27760562866052405265269419 41640844299078607897904129)
            ·
              refine ⟨31230633224308955923428097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41640844299078607897904129 31230633224308955923428097)
              ·
                refine ⟨23422974918231716942571073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31230633224308955923428097 23422974918231716942571073)
                ·
                  refine ⟨17567231188673787706928305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23422974918231716942571073 17567231188673787706928305)
                  ·
                    refine ⟨13175423391505340780196229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17567231188673787706928305 13175423391505340780196229)
                    ·
                      refine ⟨2470391885907251396286793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13175423391505340780196229 2470391885907251396286793)
                      ·
                        rfl

theorem cell23_4811071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_4811071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811071 prefixEnd_4811071 := by exact prefixLift 4811071
  have htrace : WordTrace (prefixWord ++ tailWord_4811071) baseStart_4811071 baseEnd_4811071 := by
    simpa [prefixWord, tailWord_4811071, baseEnd_4811071] using wordTrace_append hprefix tailTrace_4811071
  have hstable : (prefixWord ++ tailWord_4811071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811071).length < 2 ^ (prefixWord ++ tailWord_4811071).sum := by decide
  have hdescent : baseEnd_4811071 < baseStart_4811071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811075 : List Nat := [1, 1, 1, 3, 1, 3, 3, 4, 2, 2, 2]
def baseStart_4811075 : Nat := 118140960795 + 4811075 * 2 ^ 59
def prefixEnd_4811075 : Nat := 4983230072969 + 3 ^ 40 * 4811075 * 2
def baseEnd_4811075 : Nat := 2470393939829869380636775

theorem tailTrace_4811075 : CollatzResearch.WordTrace tailWord_4811075 prefixEnd_4811075 2470393939829869380636775 := by
  unfold tailWord_4811075
  simp only [CollatzResearch.WordTrace]
  refine ⟨175474321045304416038922679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116982880696869610692615119 175474321045304416038922679)
  ·
    refine ⟨263211481567956624058384019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175474321045304416038922679 263211481567956624058384019)
    ·
      refine ⟨394817222351934936087576029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263211481567956624058384019 394817222351934936087576029)
      ·
        refine ⟨148056458381975601032841011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 394817222351934936087576029 148056458381975601032841011)
        ·
          refine ⟨222084687572963401549261517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148056458381975601032841011 222084687572963401549261517)
          ·
            refine ⟨83281757839861275580973069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222084687572963401549261517 83281757839861275580973069)
            ·
              refine ⟨31230659189947978342864901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83281757839861275580973069 31230659189947978342864901)
              ·
                refine ⟨5855748598115245939287169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31230659189947978342864901 5855748598115245939287169)
                ·
                  refine ⟨4391811448586434454465377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5855748598115245939287169 4391811448586434454465377)
                  ·
                    refine ⟨3293858586439825840849033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4391811448586434454465377 3293858586439825840849033)
                    ·
                      refine ⟨2470393939829869380636775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3293858586439825840849033 2470393939829869380636775)
                      ·
                        rfl

theorem cell23_4811075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 2, 2].length) (baseStart_4811075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811075 prefixEnd_4811075 := by exact prefixLift 4811075
  have htrace : WordTrace (prefixWord ++ tailWord_4811075) baseStart_4811075 baseEnd_4811075 := by
    simpa [prefixWord, tailWord_4811075, baseEnd_4811075] using wordTrace_append hprefix tailTrace_4811075
  have hstable : (prefixWord ++ tailWord_4811075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811075).length < 2 ^ (prefixWord ++ tailWord_4811075).sum := by decide
  have hdescent : baseEnd_4811075 < baseStart_4811075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811092 : List Nat := [2, 4, 1, 1, 2, 2, 2, 3, 2, 2, 2]
def baseStart_4811092 : Nat := 118140960795 + 4811092 * 2 ^ 59
def prefixEnd_4811092 : Nat := 4983230072969 + 3 ^ 40 * 4811092 * 2
def baseEnd_4811092 : Nat := 2470402669000995814124197

theorem tailTrace_4811092 : CollatzResearch.WordTrace tailWord_4811092 prefixEnd_4811092 2470402669000995814124197 := by
  unfold tailWord_4811092
  simp only [CollatzResearch.WordTrace]
  refine ⟨87737470543121413971145765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116983294057495218628194353 87737470543121413971145765)
  ·
    refine ⟨16450775726835265119589831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87737470543121413971145765 16450775726835265119589831)
    ·
      refine ⟨24676163590252897679384747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16450775726835265119589831 24676163590252897679384747)
      ·
        refine ⟨37014245385379346519077121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24676163590252897679384747 37014245385379346519077121)
        ·
          refine ⟨27760684039034509889307841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37014245385379346519077121 27760684039034509889307841)
          ·
            refine ⟨20820513029275882416980881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27760684039034509889307841 20820513029275882416980881)
            ·
              refine ⟨15615384771956911812735661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20820513029275882416980881 15615384771956911812735661)
              ·
                refine ⟨5855769289483841929775873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15615384771956911812735661 5855769289483841929775873)
                ·
                  refine ⟨4391826967112881447331905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5855769289483841929775873 4391826967112881447331905)
                  ·
                    refine ⟨3293870225334661085498929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4391826967112881447331905 3293870225334661085498929)
                    ·
                      refine ⟨2470402669000995814124197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3293870225334661085498929 2470402669000995814124197)
                      ·
                        rfl

theorem cell23_4811092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_4811092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811092 prefixEnd_4811092 := by exact prefixLift 4811092
  have htrace : WordTrace (prefixWord ++ tailWord_4811092) baseStart_4811092 baseEnd_4811092 := by
    simpa [prefixWord, tailWord_4811092, baseEnd_4811092] using wordTrace_append hprefix tailTrace_4811092
  have hstable : (prefixWord ++ tailWord_4811092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811092).length < 2 ^ (prefixWord ++ tailWord_4811092).sum := by decide
  have hdescent : baseEnd_4811092 < baseStart_4811092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811161 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 2, 4, 4]
def baseStart_4811161 : Nat := 118140960795 + 4811161 * 2 ^ 59
def prefixEnd_4811161 : Nat := 4983230072969 + 3 ^ 40 * 4811161 * 2
def baseEnd_4811161 : Nat := 2470438099166156044161379

theorem tailTrace_4811161 : CollatzResearch.WordTrace tailWord_4811161 prefixEnd_4811161 2470438099166156044161379 := by
  unfold tailWord_4811161
  simp only [CollatzResearch.WordTrace]
  refine ⟨175477457722992852726553337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116984971815328568484368891 175477457722992852726553337)
  ·
    refine ⟨131608093292244639544915003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175477457722992852726553337 131608093292244639544915003)
    ·
      refine ⟨197412139938366959317372505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131608093292244639544915003 197412139938366959317372505)
      ·
        refine ⟨148059104953775219488029379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197412139938366959317372505 148059104953775219488029379)
        ·
          refine ⟨222088657430662829232044069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148059104953775219488029379 222088657430662829232044069)
          ·
            refine ⟨41641623268249280481008263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 222088657430662829232044069 41641623268249280481008263)
            ·
              refine ⟨62462434902373920721512395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41641623268249280481008263 62462434902373920721512395)
              ·
                refine ⟨93693652353560881082268593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62462434902373920721512395 93693652353560881082268593)
                ·
                  refine ⟨70270239265170660811701445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93693652353560881082268593 70270239265170660811701445)
                  ·
                    refine ⟨13175669862219498902194021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70270239265170660811701445 13175669862219498902194021)
                    ·
                      refine ⟨2470438099166156044161379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13175669862219498902194021 2470438099166156044161379)
                      ·
                        rfl

theorem cell23_4811161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_4811161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811161 prefixEnd_4811161 := by exact prefixLift 4811161
  have htrace : WordTrace (prefixWord ++ tailWord_4811161) baseStart_4811161 baseEnd_4811161 := by
    simpa [prefixWord, tailWord_4811161, baseEnd_4811161] using wordTrace_append hprefix tailTrace_4811161
  have hstable : (prefixWord ++ tailWord_4811161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811161).length < 2 ^ (prefixWord ++ tailWord_4811161).sum := by decide
  have hdescent : baseEnd_4811161 < baseStart_4811161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811168 : List Nat := [2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 3]
def baseStart_4811168 : Nat := 118140960795 + 4811168 * 2 ^ 59
def prefixEnd_4811168 : Nat := 4983230072969 + 3 ^ 40 * 4811168 * 2
def baseEnd_4811168 : Nat := 2470441693530737516773847

theorem tailTrace_4811168 : CollatzResearch.WordTrace tailWord_4811168 prefixEnd_4811168 2470441693530737516773847 := by
  unfold tailWord_4811168
  simp only [CollatzResearch.WordTrace]
  refine ⟨87738856516983746461029079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116985142022644995281372105 87738856516983746461029079)
  ·
    refine ⟨131608284775475619691543619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87738856516983746461029079 131608284775475619691543619)
    ·
      refine ⟨197412427163213429537315429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131608284775475619691543619 197412427163213429537315429)
      ·
        refine ⟨37014830093102518038246643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197412427163213429537315429 37014830093102518038246643)
        ·
          refine ⟨55522245139653777057369965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37014830093102518038246643 55522245139653777057369965)
          ·
            refine ⟨20820841927370166396513737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55522245139653777057369965 20820841927370166396513737)
            ·
              refine ⟨15615631445527624797385303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20820841927370166396513737 15615631445527624797385303)
              ·
                refine ⟨23423447168291437196077955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15615631445527624797385303 23423447168291437196077955)
                ·
                  refine ⟨35135170752437155794116933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23423447168291437196077955 35135170752437155794116933)
                  ·
                    refine ⟨6587844516081966711396925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35135170752437155794116933 6587844516081966711396925)
                    ·
                      refine ⟨2470441693530737516773847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6587844516081966711396925 2470441693530737516773847)
                      ·
                        rfl

theorem cell23_4811168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_4811168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811168 prefixEnd_4811168 := by exact prefixLift 4811168
  have htrace : WordTrace (prefixWord ++ tailWord_4811168) baseStart_4811168 baseEnd_4811168 := by
    simpa [prefixWord, tailWord_4811168, baseEnd_4811168] using wordTrace_append hprefix tailTrace_4811168
  have hstable : (prefixWord ++ tailWord_4811168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811168).length < 2 ^ (prefixWord ++ tailWord_4811168).sum := by decide
  have hdescent : baseEnd_4811168 < baseStart_4811168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811171 : List Nat := [1, 1, 1, 4, 1, 4, 1, 2, 8]
def baseStart_4811171 : Nat := 118140960795 + 4811171 * 2 ^ 59
def prefixEnd_4811171 : Nat := 4983230072969 + 3 ^ 40 * 4811171 * 2
def baseEnd_4811171 : Nat := 274493692663633445004037

theorem tailTrace_4811171 : CollatzResearch.WordTrace tailWord_4811171 prefixEnd_4811171 274493692663633445004037 := by
  unfold tailWord_4811171
  simp only [CollatzResearch.WordTrace]
  refine ⟨175477822452956624434417367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116985214968637749622944911 175477822452956624434417367)
  ·
    refine ⟨263216733679434936651626051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175477822452956624434417367 263216733679434936651626051)
    ·
      refine ⟨394825100519152404977439077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263216733679434936651626051 394825100519152404977439077)
      ·
        refine ⟨74029706347341075933269827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 394825100519152404977439077 74029706347341075933269827)
        ·
          refine ⟨111044559521011613899904741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74029706347341075933269827 111044559521011613899904741)
          ·
            refine ⟨20820854910189677606232139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111044559521011613899904741 20820854910189677606232139)
            ·
              refine ⟨31231282365284516409348209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20820854910189677606232139 31231282365284516409348209)
              ·
                refine ⟨23423461773963387307011157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31231282365284516409348209 23423461773963387307011157)
                ·
                  refine ⟨274493692663633445004037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23423461773963387307011157 274493692663633445004037)
                  ·
                    rfl

theorem cell23_4811171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 8].length) (baseStart_4811171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811171 prefixEnd_4811171 := by exact prefixLift 4811171
  have htrace : WordTrace (prefixWord ++ tailWord_4811171) baseStart_4811171 baseEnd_4811171 := by
    simpa [prefixWord, tailWord_4811171, baseEnd_4811171] using wordTrace_append hprefix tailTrace_4811171
  have hstable : (prefixWord ++ tailWord_4811171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811171).length < 2 ^ (prefixWord ++ tailWord_4811171).sum := by decide
  have hdescent : baseEnd_4811171 < baseStart_4811171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811185 : List Nat := [1, 2, 2, 4, 1, 3, 1, 2, 2, 2, 3]
def baseStart_4811185 : Nat := 118140960795 + 4811185 * 2 ^ 59
def prefixEnd_4811185 : Nat := 4983230072969 + 3 ^ 40 * 4811185 * 2
def baseEnd_4811185 : Nat := 2470450422701863950261269

theorem tailTrace_4811185 : CollatzResearch.WordTrace tailWord_4811185 prefixEnd_4811185 2470450422701863950261269 := by
  unfold tailWord_4811185
  simp only [CollatzResearch.WordTrace]
  refine ⟨175478333074905904825427009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116985555383270603216951339 175478333074905904825427009)
  ·
    refine ⟨131608749806179428619070257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175478333074905904825427009 131608749806179428619070257)
    ·
      refine ⟨98706562354634571464302693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131608749806179428619070257 98706562354634571464302693)
      ·
        refine ⟨18507480441493982149556755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98706562354634571464302693 18507480441493982149556755)
        ·
          refine ⟨27761220662240973224335133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18507480441493982149556755 27761220662240973224335133)
          ·
            refine ⟨10410457748340364959125675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27761220662240973224335133 10410457748340364959125675)
            ·
              refine ⟨15615686622510547438688513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10410457748340364959125675 15615686622510547438688513)
              ·
                refine ⟨11711764966882910579016385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15615686622510547438688513 11711764966882910579016385)
                ·
                  refine ⟨8783823725162182934262289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11711764966882910579016385 8783823725162182934262289)
                  ·
                    refine ⟨6587867793871637200696717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8783823725162182934262289 6587867793871637200696717)
                    ·
                      refine ⟨2470450422701863950261269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6587867793871637200696717 2470450422701863950261269)
                      ·
                        rfl

theorem cell23_4811185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_4811185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811185 prefixEnd_4811185 := by exact prefixLift 4811185
  have htrace : WordTrace (prefixWord ++ tailWord_4811185) baseStart_4811185 baseEnd_4811185 := by
    simpa [prefixWord, tailWord_4811185, baseEnd_4811185] using wordTrace_append hprefix tailTrace_4811185
  have hstable : (prefixWord ++ tailWord_4811185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811185).length < 2 ^ (prefixWord ++ tailWord_4811185).sum := by decide
  have hdescent : baseEnd_4811185 < baseStart_4811185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811232 : List Nat := [2, 1, 1, 3, 1, 1, 4, 5, 1, 1, 3]
def baseStart_4811232 : Nat := 118140960795 + 4811232 * 2 ^ 59
def prefixEnd_4811232 : Nat := 4983230072969 + 3 ^ 40 * 4811232 * 2
def baseEnd_4811232 : Nat := 2470474556292625266373553

theorem tailTrace_4811232 : CollatzResearch.WordTrace tailWord_4811232 prefixEnd_4811232 2470474556292625266373553 := by
  unfold tailWord_4811232
  simp only [CollatzResearch.WordTrace]
  refine ⟨87740023652867815926193975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116986698203823754568258633 87740023652867815926193975)
  ·
    refine ⟨131610035479301723889290963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87740023652867815926193975 131610035479301723889290963)
    ·
      refine ⟨197415053218952585833936445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131610035479301723889290963 197415053218952585833936445)
      ·
        refine ⟨74030644957107219687726167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197415053218952585833936445 74030644957107219687726167)
        ·
          refine ⟨111045967435660829531589251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74030644957107219687726167 111045967435660829531589251)
          ·
            refine ⟨166568951153491244297383877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111045967435660829531589251 166568951153491244297383877)
            ·
              refine ⟨31231678341279608305759477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 166568951153491244297383877 31231678341279608305759477)
              ·
                refine ⟨2927969844494963278664951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31231678341279608305759477 2927969844494963278664951)
                ·
                  refine ⟨4391954766742444917997427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2927969844494963278664951 4391954766742444917997427)
                  ·
                    refine ⟨6587932150113667376996141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4391954766742444917997427 6587932150113667376996141)
                    ·
                      refine ⟨2470474556292625266373553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6587932150113667376996141 2470474556292625266373553)
                      ·
                        rfl

theorem cell23_4811232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 1, 1, 3].length) (baseStart_4811232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811232 prefixEnd_4811232 := by exact prefixLift 4811232
  have htrace : WordTrace (prefixWord ++ tailWord_4811232) baseStart_4811232 baseEnd_4811232 := by
    simpa [prefixWord, tailWord_4811232, baseEnd_4811232] using wordTrace_append hprefix tailTrace_4811232
  have hstable : (prefixWord ++ tailWord_4811232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811232).length < 2 ^ (prefixWord ++ tailWord_4811232).sum := by decide
  have hdescent : baseEnd_4811232 < baseStart_4811232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811242 : List Nat := [3, 1, 3, 1, 3, 1, 2, 2, 2, 3, 2]
def baseStart_4811242 : Nat := 118140960795 + 4811242 * 2 ^ 59
def prefixEnd_4811242 : Nat := 4983230072969 + 3 ^ 40 * 4811242 * 2
def baseEnd_4811242 : Nat := 2470479691099170227248507

theorem tailTrace_4811242 : CollatzResearch.WordTrace tailWord_4811242 prefixEnd_4811242 2470479691099170227248507 := by
  unfold tailWord_4811242
  simp only [CollatzResearch.WordTrace]
  refine ⟨43870103008924850890062995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116986941357132935706834653 43870103008924850890062995)
  ·
    refine ⟨65805154513387276335094493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43870103008924850890062995 65805154513387276335094493)
    ·
      refine ⟨24676932942520228625660435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65805154513387276335094493 24676932942520228625660435)
      ·
        refine ⟨37015399413780342938490653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24676932942520228625660435 37015399413780342938490653)
        ·
          refine ⟨13880774780167628601933995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37015399413780342938490653 13880774780167628601933995)
          ·
            refine ⟨20821162170251442902900993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13880774780167628601933995 20821162170251442902900993)
            ·
              refine ⟨15615871627688582177175745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20821162170251442902900993 15615871627688582177175745)
              ·
                refine ⟨11711903720766436632881809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15615871627688582177175745 11711903720766436632881809)
                ·
                  refine ⟨8783927790574827474661357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11711903720766436632881809 8783927790574827474661357)
                  ·
                    refine ⟨3293972921465560302998009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8783927790574827474661357 3293972921465560302998009)
                    ·
                      refine ⟨2470479691099170227248507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3293972921465560302998009 2470479691099170227248507)
                      ·
                        rfl

theorem cell23_4811242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_4811242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811242 prefixEnd_4811242 := by exact prefixLift 4811242
  have htrace : WordTrace (prefixWord ++ tailWord_4811242) baseStart_4811242 baseEnd_4811242 := by
    simpa [prefixWord, tailWord_4811242, baseEnd_4811242] using wordTrace_append hprefix tailTrace_4811242
  have hstable : (prefixWord ++ tailWord_4811242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811242).length < 2 ^ (prefixWord ++ tailWord_4811242).sum := by decide
  have hdescent : baseEnd_4811242 < baseStart_4811242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811265 : List Nat := [1, 2, 4, 1, 3, 2, 2, 1, 1, 6]
def baseStart_4811265 : Nat := 118140960795 + 4811265 * 2 ^ 59
def prefixEnd_4811265 : Nat := 4983230072969 + 3 ^ 40 * 4811265 * 2
def baseEnd_4811265 : Nat := 823497167051407879086967

theorem tailTrace_4811265 : CollatzResearch.WordTrace tailWord_4811265 prefixEnd_4811265 823497167051407879086967 := by
  unfold tailWord_4811265
  simp only [CollatzResearch.WordTrace]
  refine ⟨175481250914616078488339249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116987500609744052325559499 175481250914616078488339249)
  ·
    refine ⟨131610938185962058866254437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175481250914616078488339249 131610938185962058866254437)
    ·
      refine ⟨24677050909867886037422707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131610938185962058866254437 24677050909867886037422707)
      ·
        refine ⟨37015576364801829056134061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24677050909867886037422707 37015576364801829056134061)
        ·
          refine ⟨13880841136800685896050273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37015576364801829056134061 13880841136800685896050273)
          ·
            refine ⟨10410630852600514422037705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13880841136800685896050273 10410630852600514422037705)
            ·
              refine ⟨7807973139450385816528279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10410630852600514422037705 7807973139450385816528279)
              ·
                refine ⟨11711959709175578724792419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7807973139450385816528279 11711959709175578724792419)
                ·
                  refine ⟨17567939563763368087188629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11711959709175578724792419 17567939563763368087188629)
                  ·
                    refine ⟨823497167051407879086967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17567939563763368087188629 823497167051407879086967)
                    ·
                      rfl

theorem cell23_4811265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_4811265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811265 prefixEnd_4811265 := by exact prefixLift 4811265
  have htrace : WordTrace (prefixWord ++ tailWord_4811265) baseStart_4811265 baseEnd_4811265 := by
    simpa [prefixWord, tailWord_4811265, baseEnd_4811265] using wordTrace_append hprefix tailTrace_4811265
  have hstable : (prefixWord ++ tailWord_4811265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811265).length < 2 ^ (prefixWord ++ tailWord_4811265).sum := by decide
  have hdescent : baseEnd_4811265 < baseStart_4811265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811275 : List Nat := [1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 3]
def baseStart_4811275 : Nat := 118140960795 + 4811275 * 2 ^ 59
def prefixEnd_4811275 : Nat := 4983230072969 + 3 ^ 40 * 4811275 * 2
def baseEnd_4811275 : Nat := 2470496635960768598135855

theorem tailTrace_4811275 : CollatzResearch.WordTrace tailWord_4811275 prefixEnd_4811275 2470496635960768598135855 := by
  unfold tailWord_4811275
  simp only [CollatzResearch.WordTrace]
  refine ⟨175481615644579850196203279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116987743763053233464135519 175481615644579850196203279)
  ·
    refine ⟨263222423466869775294304919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175481615644579850196203279 263222423466869775294304919)
    ·
      refine ⟨394833635200304662941457379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263222423466869775294304919 394833635200304662941457379)
      ·
        refine ⟨592250452800456994412186069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394833635200304662941457379 592250452800456994412186069)
        ·
          refine ⟨13880869987510710806535611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 592250452800456994412186069 13880869987510710806535611)
          ·
            refine ⟨20821304981266066209803417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13880869987510710806535611 20821304981266066209803417)
            ·
              refine ⟨15615978735949549657352563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20821304981266066209803417 15615978735949549657352563)
              ·
                refine ⟨23423968103924324486028845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15615978735949549657352563 23423968103924324486028845)
                ·
                  refine ⟨8783988038971621682260817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23423968103924324486028845 8783988038971621682260817)
                  ·
                    refine ⟨6587991029228716261695613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8783988038971621682260817 6587991029228716261695613)
                    ·
                      refine ⟨2470496635960768598135855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6587991029228716261695613 2470496635960768598135855)
                      ·
                        rfl

theorem cell23_4811275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 3].length) (baseStart_4811275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811275 prefixEnd_4811275 := by exact prefixLift 4811275
  have htrace : WordTrace (prefixWord ++ tailWord_4811275) baseStart_4811275 baseEnd_4811275 := by
    simpa [prefixWord, tailWord_4811275, baseEnd_4811275] using wordTrace_append hprefix tailTrace_4811275
  have hstable : (prefixWord ++ tailWord_4811275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811275).length < 2 ^ (prefixWord ++ tailWord_4811275).sum := by decide
  have hdescent : baseEnd_4811275 < baseStart_4811275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811292 : List Nat := [2, 2, 3, 1, 2, 3, 1, 3, 1, 2, 3]
def baseStart_4811292 : Nat := 118140960795 + 4811292 * 2 ^ 59
def prefixEnd_4811292 : Nat := 4983230072969 + 3 ^ 40 * 4811292 * 2
def baseEnd_4811292 : Nat := 2470505365131895031623277

theorem tailTrace_4811292 : CollatzResearch.WordTrace tailWord_4811292 prefixEnd_4811292 2470505365131895031623277 := by
  unfold tailWord_4811292
  simp only [CollatzResearch.WordTrace]
  refine ⟨87741117842759131049786065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116988157123678841399714753 87741117842759131049786065)
  ·
    refine ⟨65805838382069348287339549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87741117842759131049786065 65805838382069348287339549)
    ·
      refine ⟨24677189393276005607752331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65805838382069348287339549 24677189393276005607752331)
      ·
        refine ⟨37015784089914008411628497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24677189393276005607752331 37015784089914008411628497)
        ·
          refine ⟨27761838067435506308721373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37015784089914008411628497 27761838067435506308721373)
          ·
            refine ⟨10410689275288314865770515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27761838067435506308721373 10410689275288314865770515)
            ·
              refine ⟨15616033912932472298655773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10410689275288314865770515 15616033912932472298655773)
              ·
                refine ⟨5856012717349677111995915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15616033912932472298655773 5856012717349677111995915)
                ·
                  refine ⟨8784019076024515667993873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5856012717349677111995915 8784019076024515667993873)
                  ·
                    refine ⟨6588014307018386750995405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8784019076024515667993873 6588014307018386750995405)
                    ·
                      refine ⟨2470505365131895031623277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6588014307018386750995405 2470505365131895031623277)
                      ·
                        rfl

theorem cell23_4811292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_4811292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811292 prefixEnd_4811292 := by exact prefixLift 4811292
  have htrace : WordTrace (prefixWord ++ tailWord_4811292) baseStart_4811292 baseEnd_4811292 := by
    simpa [prefixWord, tailWord_4811292, baseEnd_4811292] using wordTrace_append hprefix tailTrace_4811292
  have hstable : (prefixWord ++ tailWord_4811292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811292).length < 2 ^ (prefixWord ++ tailWord_4811292).sum := by decide
  have hdescent : baseEnd_4811292 < baseStart_4811292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811298 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_4811298 : Nat := 118140960795 + 4811298 * 2 ^ 59
def prefixEnd_4811298 : Nat := 4983230072969 + 3 ^ 40 * 4811298 * 2
def baseEnd_4811298 : Nat := 2470508446015822008148249

theorem tailTrace_4811298 : CollatzResearch.WordTrace tailWord_4811298 prefixEnd_4811298 2470508446015822008148249 := by
  unfold tailWord_4811298
  simp only [CollatzResearch.WordTrace]
  refine ⟨43870613630874131281072637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116988303015664350082860365 43870613630874131281072637)
  ·
    refine ⟨16451480111577799230402239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43870613630874131281072637 16451480111577799230402239)
    ·
      refine ⟨24677220167366698845603359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16451480111577799230402239 24677220167366698845603359)
      ·
        refine ⟨37015830251050048268405039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24677220167366698845603359 37015830251050048268405039)
        ·
          refine ⟨55523745376575072402607559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37015830251050048268405039 55523745376575072402607559)
          ·
            refine ⟨83285618064862608603911339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55523745376575072402607559 83285618064862608603911339)
            ·
              refine ⟨124928427097293912905867009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83285618064862608603911339 124928427097293912905867009)
              ·
                refine ⟨93696320322970434679400257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124928427097293912905867009 93696320322970434679400257)
                ·
                  refine ⟨70272240242227826009550193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93696320322970434679400257 70272240242227826009550193)
                  ·
                    refine ⟨52704180181670869507162645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70272240242227826009550193 52704180181670869507162645)
                    ·
                      refine ⟨2470508446015822008148249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52704180181670869507162645 2470508446015822008148249)
                      ·
                        rfl

theorem cell23_4811298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_4811298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811298 prefixEnd_4811298 := by exact prefixLift 4811298
  have htrace : WordTrace (prefixWord ++ tailWord_4811298) baseStart_4811298 baseEnd_4811298 := by
    simpa [prefixWord, tailWord_4811298, baseEnd_4811298] using wordTrace_append hprefix tailTrace_4811298
  have hstable : (prefixWord ++ tailWord_4811298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811298).length < 2 ^ (prefixWord ++ tailWord_4811298).sum := by decide
  have hdescent : baseEnd_4811298 < baseStart_4811298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811306 : List Nat := [3, 1, 4, 1, 1, 2, 2, 4, 1, 2, 2]
def baseStart_4811306 : Nat := 118140960795 + 4811306 * 2 ^ 59
def prefixEnd_4811306 : Nat := 4983230072969 + 3 ^ 40 * 4811306 * 2
def baseEnd_4811306 : Nat := 2470512553861057976848213

theorem tailTrace_4811306 : CollatzResearch.WordTrace tailWord_4811306 prefixEnd_4811306 2470512553861057976848213 := by
  unfold tailWord_4811306
  simp only [CollatzResearch.WordTrace]
  refine ⟨43870686576866885622645443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116988497538311694993721181 43870686576866885622645443)
  ·
    refine ⟨65806029865300328433968165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43870686576866885622645443 65806029865300328433968165)
    ·
      refine ⟨12338630599743811581369031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65806029865300328433968165 12338630599743811581369031)
      ·
        refine ⟨18507945899615717372053547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12338630599743811581369031 18507945899615717372053547)
        ·
          refine ⟨27761918849423576058080321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18507945899615717372053547 27761918849423576058080321)
          ·
            refine ⟨20821439137067682043560241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27761918849423576058080321 20821439137067682043560241)
            ·
              refine ⟨15616079352800761532670181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20821439137067682043560241 15616079352800761532670181)
              ·
                refine ⟨2928014878650142787375659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15616079352800761532670181 2928014878650142787375659)
                ·
                  refine ⟨4392022317975214181063489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2928014878650142787375659 4392022317975214181063489)
                  ·
                    refine ⟨3294016738481410635797617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4392022317975214181063489 3294016738481410635797617)
                    ·
                      refine ⟨2470512553861057976848213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3294016738481410635797617 2470512553861057976848213)
                      ·
                        rfl

theorem cell23_4811306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_4811306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811306 prefixEnd_4811306 := by exact prefixLift 4811306
  have htrace : WordTrace (prefixWord ++ tailWord_4811306) baseStart_4811306 baseEnd_4811306 := by
    simpa [prefixWord, tailWord_4811306, baseEnd_4811306] using wordTrace_append hprefix tailTrace_4811306
  have hstable : (prefixWord ++ tailWord_4811306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811306).length < 2 ^ (prefixWord ++ tailWord_4811306).sum := by decide
  have hdescent : baseEnd_4811306 < baseStart_4811306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811316 : List Nat := [2, 5, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_4811316 : Nat := 118140960795 + 4811316 * 2 ^ 59
def prefixEnd_4811316 : Nat := 4983230072969 + 3 ^ 40 * 4811316 * 2
def baseEnd_4811316 : Nat := 823505896222534312574389

theorem tailTrace_4811316 : CollatzResearch.WordTrace tailWord_4811316 prefixEnd_4811316 823505896222534312574389 := by
  unfold tailWord_4811316
  simp only [CollatzResearch.WordTrace]
  refine ⟨87741555518715657099222901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116988740691620876132297201 87741555518715657099222901)
  ·
    refine ⟨8225770829879592853052147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87741555518715657099222901 8225770829879592853052147)
    ·
      refine ⟨12338656244819389279578221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8225770829879592853052147 12338656244819389279578221)
      ·
        refine ⟨4626996091807270979841833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12338656244819389279578221 4626996091807270979841833)
        ·
          refine ⟨3470247068855453234881375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4626996091807270979841833 3470247068855453234881375)
          ·
            refine ⟨5205370603283179852322063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3470247068855453234881375 5205370603283179852322063)
            ·
              refine ⟨7808055904924769778483095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5205370603283179852322063 7808055904924769778483095)
              ·
                refine ⟨11712083857387154667724643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7808055904924769778483095 11712083857387154667724643)
                ·
                  refine ⟨17568125786080732001586965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11712083857387154667724643 17568125786080732001586965)
                  ·
                    refine ⟨823505896222534312574389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17568125786080732001586965 823505896222534312574389)
                    ·
                      rfl

theorem cell23_4811316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_4811316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811316 prefixEnd_4811316 := by exact prefixLift 4811316
  have htrace : WordTrace (prefixWord ++ tailWord_4811316) baseStart_4811316 baseEnd_4811316 := by
    simpa [prefixWord, tailWord_4811316, baseEnd_4811316] using wordTrace_append hprefix tailTrace_4811316
  have hstable : (prefixWord ++ tailWord_4811316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811316).length < 2 ^ (prefixWord ++ tailWord_4811316).sum := by decide
  have hdescent : baseEnd_4811316 < baseStart_4811316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811322 : List Nat := [3, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3]
def baseStart_4811322 : Nat := 118140960795 + 4811322 * 2 ^ 59
def prefixEnd_4811322 : Nat := 4983230072969 + 3 ^ 40 * 4811322 * 2
def baseEnd_4811322 : Nat := 2470520769551529914248139

theorem tailTrace_4811322 : CollatzResearch.WordTrace tailWord_4811322 prefixEnd_4811322 2470520769551529914248139 := by
  unfold tailWord_4811322
  simp only [CollatzResearch.WordTrace]
  refine ⟨43870832468852394305791055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116988886583606384815442813 43870832468852394305791055)
  ·
    refine ⟨65806248703278591458686583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43870832468852394305791055 65806248703278591458686583)
    ·
      refine ⟨98709373054917887188029875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65806248703278591458686583 98709373054917887188029875)
      ·
        refine ⟨148064059582376830782044813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98709373054917887188029875 148064059582376830782044813)
        ·
          refine ⟨55524022343391311543266805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148064059582376830782044813 55524022343391311543266805)
          ·
            refine ⟨5205377094692935457181263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55524022343391311543266805 5205377094692935457181263)
            ·
              refine ⟨7808065642039403185771895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5205377094692935457181263 7808065642039403185771895)
              ·
                refine ⟨11712098463059104778657843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7808065642039403185771895 11712098463059104778657843)
                ·
                  refine ⟨17568147694588657167986765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11712098463059104778657843 17568147694588657167986765)
                  ·
                    refine ⟨6588055385470746437995037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17568147694588657167986765 6588055385470746437995037)
                    ·
                      refine ⟨2470520769551529914248139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6588055385470746437995037 2470520769551529914248139)
                      ·
                        rfl

theorem cell23_4811322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3].length) (baseStart_4811322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811322 prefixEnd_4811322 := by exact prefixLift 4811322
  have htrace : WordTrace (prefixWord ++ tailWord_4811322) baseStart_4811322 baseEnd_4811322 := by
    simpa [prefixWord, tailWord_4811322, baseEnd_4811322] using wordTrace_append hprefix tailTrace_4811322
  have hstable : (prefixWord ++ tailWord_4811322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811322).length < 2 ^ (prefixWord ++ tailWord_4811322).sum := by decide
  have hdescent : baseEnd_4811322 < baseStart_4811322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811326 : List Nat := [4, 2, 1, 4, 1, 1, 2, 2, 1, 2, 3]
def baseStart_4811326 : Nat := 118140960795 + 4811326 * 2 ^ 59
def prefixEnd_4811326 : Nat := 4983230072969 + 3 ^ 40 * 4811326 * 2
def baseEnd_4811326 : Nat := 2470522823474147898598121

theorem tailTrace_4811326 : CollatzResearch.WordTrace tailWord_4811326 prefixEnd_4811326 2470522823474147898598121 := by
  unfold tailWord_4811326
  simp only [CollatzResearch.WordTrace]
  refine ⟨21935434470924385738288729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116988983844930057270873221 21935434470924385738288729)
  ·
    refine ⟨16451575853193289303716547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21935434470924385738288729 16451575853193289303716547)
    ·
      refine ⟨24677363779789933955574821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16451575853193289303716547 24677363779789933955574821)
      ·
        refine ⟨4627005708710612616670279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24677363779789933955574821 4627005708710612616670279)
        ·
          refine ⟨6940508563065918925005419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4627005708710612616670279 6940508563065918925005419)
          ·
            refine ⟨10410762844598878387508129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6940508563065918925005419 10410762844598878387508129)
            ·
              refine ⟨7808072133449158790631097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10410762844598878387508129 7808072133449158790631097)
              ·
                refine ⟨5856054100086869092973323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7808072133449158790631097 5856054100086869092973323)
                ·
                  refine ⟨8784081150130303639459985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5856054100086869092973323 8784081150130303639459985)
                  ·
                    refine ⟨6588060862597727729594989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8784081150130303639459985 6588060862597727729594989)
                    ·
                      refine ⟨2470522823474147898598121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6588060862597727729594989 2470522823474147898598121)
                      ·
                        rfl

theorem cell23_4811326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_4811326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811326 prefixEnd_4811326 := by exact prefixLift 4811326
  have htrace : WordTrace (prefixWord ++ tailWord_4811326) baseStart_4811326 baseEnd_4811326 := by
    simpa [prefixWord, tailWord_4811326, baseEnd_4811326] using wordTrace_append hprefix tailTrace_4811326
  have hstable : (prefixWord ++ tailWord_4811326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811326).length < 2 ^ (prefixWord ++ tailWord_4811326).sum := by decide
  have hdescent : baseEnd_4811326 < baseStart_4811326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811328 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 4]
def baseStart_4811328 : Nat := 118140960795 + 4811328 * 2 ^ 59
def prefixEnd_4811328 : Nat := 4983230072969 + 3 ^ 40 * 4811328 * 2
def baseEnd_4811328 : Nat := 2470523850435456890773111

theorem tailTrace_4811328 : CollatzResearch.WordTrace tailWord_4811328 prefixEnd_4811328 2470523850435456890773111 := by
  unfold tailWord_4811328
  simp only [CollatzResearch.WordTrace]
  refine ⟨87741774356693920123941319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116989032475591893498588425 87741774356693920123941319)
  ·
    refine ⟨131612661535040880185911979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87741774356693920123941319 131612661535040880185911979)
    ·
      refine ⟨197418992302561320278867969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131612661535040880185911979 197418992302561320278867969)
      ·
        refine ⟨148064244226920990209150977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197418992302561320278867969 148064244226920990209150977)
        ·
          refine ⟨111048183170190742656863233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148064244226920990209150977 111048183170190742656863233)
          ·
            refine ⟨83286137377643056992647425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111048183170190742656863233 83286137377643056992647425)
            ·
              refine ⟨62464603033232292744485569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83286137377643056992647425 62464603033232292744485569)
              ·
                refine ⟨46848452274924219558364177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62464603033232292744485569 46848452274924219558364177)
                ·
                  refine ⟨35136339206193164668773133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46848452274924219558364177 35136339206193164668773133)
                  ·
                    refine ⟨13176127202322436750789925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35136339206193164668773133 13176127202322436750789925)
                    ·
                      refine ⟨2470523850435456890773111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13176127202322436750789925 2470523850435456890773111)
                      ·
                        rfl

theorem cell23_4811328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_4811328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811328 prefixEnd_4811328 := by exact prefixLift 4811328
  have htrace : WordTrace (prefixWord ++ tailWord_4811328) baseStart_4811328 baseEnd_4811328 := by
    simpa [prefixWord, tailWord_4811328, baseEnd_4811328] using wordTrace_append hprefix tailTrace_4811328
  have hstable : (prefixWord ++ tailWord_4811328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811328).length < 2 ^ (prefixWord ++ tailWord_4811328).sum := by decide
  have hdescent : baseEnd_4811328 < baseStart_4811328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811415 : List Nat := [1, 1, 3, 3, 2, 1, 1, 4, 2, 5]
def baseStart_4811415 : Nat := 118140960795 + 4811415 * 2 ^ 59
def prefixEnd_4811415 : Nat := 4983230072969 + 3 ^ 40 * 4811415 * 2
def baseEnd_4811415 : Nat := 823522841084132683461737

theorem tailTrace_4811415 : CollatzResearch.WordTrace tailWord_4811415 prefixEnd_4811415 823522841084132683461737 := by
  unfold tailWord_4811415
  simp only [CollatzResearch.WordTrace]
  refine ⟨175486721864072654106299699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116991147909381769404199799 175486721864072654106299699)
  ·
    refine ⟨263230082796108981159449549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175486721864072654106299699 263230082796108981159449549)
    ·
      refine ⟨98711281048540867934793581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263230082796108981159449549 98711281048540867934793581)
      ·
        refine ⟨37016730393202825475547593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98711281048540867934793581 37016730393202825475547593)
        ·
          refine ⟨27762547794902119106660695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37016730393202825475547593 27762547794902119106660695)
          ·
            refine ⟨41643821692353178659991043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27762547794902119106660695 41643821692353178659991043)
            ·
              refine ⟨62465732538529767989986565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41643821692353178659991043 62465732538529767989986565)
              ·
                refine ⟨11712324850974331498122481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62465732538529767989986565 11712324850974331498122481)
                ·
                  refine ⟨8784243638230748623591861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11712324850974331498122481 8784243638230748623591861)
                  ·
                    refine ⟨823522841084132683461737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8784243638230748623591861 823522841084132683461737)
                    ·
                      rfl

theorem cell23_4811415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 5].length) (baseStart_4811415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811415 prefixEnd_4811415 := by exact prefixLift 4811415
  have htrace : WordTrace (prefixWord ++ tailWord_4811415) baseStart_4811415 baseEnd_4811415 := by
    simpa [prefixWord, tailWord_4811415, baseEnd_4811415] using wordTrace_append hprefix tailTrace_4811415
  have hstable : (prefixWord ++ tailWord_4811415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811415).length < 2 ^ (prefixWord ++ tailWord_4811415).sum := by decide
  have hdescent : baseEnd_4811415 < baseStart_4811415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811452 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 1, 6, 2]
def baseStart_4811452 : Nat := 118140960795 + 4811452 * 2 ^ 59
def prefixEnd_4811452 : Nat := 4983230072969 + 3 ^ 40 * 4811452 * 2
def baseEnd_4811452 : Nat := 2470587522036614405622541

theorem tailTrace_4811452 : CollatzResearch.WordTrace tailWord_4811452 prefixEnd_4811452 2470587522036614405622541 := by
  unfold tailWord_4811452
  simp only [CollatzResearch.WordTrace]
  refine ⟨87744035682469304712698305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116992047576625739616931073 87744035682469304712698305)
  ·
    refine ⟨65808026761851978534523729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87744035682469304712698305 65808026761851978534523729)
    ·
      refine ⟨49356020071388983900892797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65808026761851978534523729 49356020071388983900892797)
      ·
        refine ⟨18508507526770868962834799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49356020071388983900892797 18508507526770868962834799)
        ·
          refine ⟨27762761290156303444252199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18508507526770868962834799 27762761290156303444252199)
          ·
            refine ⟨41644141935234455166378299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27762761290156303444252199 41644141935234455166378299)
            ·
              refine ⟨62466212902851682749567449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41644141935234455166378299 62466212902851682749567449)
              ·
                refine ⟨46849659677138762062175587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62466212902851682749567449 46849659677138762062175587)
                ·
                  refine ⟨70274489515708143093263381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46849659677138762062175587 70274489515708143093263381)
                  ·
                    refine ⟨3294116696048819207496721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70274489515708143093263381 3294116696048819207496721)
                    ·
                      refine ⟨2470587522036614405622541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3294116696048819207496721 2470587522036614405622541)
                      ·
                        rfl

theorem cell23_4811452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_4811452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811452 prefixEnd_4811452 := by exact prefixLift 4811452
  have htrace : WordTrace (prefixWord ++ tailWord_4811452) baseStart_4811452 baseEnd_4811452 := by
    simpa [prefixWord, tailWord_4811452, baseEnd_4811452] using wordTrace_append hprefix tailTrace_4811452
  have hstable : (prefixWord ++ tailWord_4811452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811452).length < 2 ^ (prefixWord ++ tailWord_4811452).sum := by decide
  have hdescent : baseEnd_4811452 < baseStart_4811452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811479 : List Nat := [1, 1, 3, 2, 1, 4, 2, 4, 1, 4]
def baseStart_4811479 : Nat := 118140960795 + 4811479 * 2 ^ 59
def prefixEnd_4811479 : Nat := 4983230072969 + 3 ^ 40 * 4811479 * 2
def baseEnd_4811479 : Nat := 823533795338095266661639

theorem tailTrace_4811479 : CollatzResearch.WordTrace tailWord_4811479 prefixEnd_4811479 823533795338095266661639 := by
  unfold tailWord_4811479
  simp only [CollatzResearch.WordTrace]
  refine ⟨175489056135840793036629491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116992704090560528691086327 175489056135840793036629491)
  ·
    refine ⟨263233584203761189554944237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175489056135840793036629491 263233584203761189554944237)
    ·
      refine ⟨98712594076410446083104089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263233584203761189554944237 98712594076410446083104089)
      ·
        refine ⟨74034445557307834562328067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98712594076410446083104089 74034445557307834562328067)
        ·
          refine ⟨111051668335961751843492101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74034445557307834562328067 111051668335961751843492101)
          ·
            refine ⟨20822187812992828470654769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111051668335961751843492101 20822187812992828470654769)
            ·
              refine ⟨15616640859744621352991077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20822187812992828470654769 15616640859744621352991077)
              ·
                refine ⟨2928120161202116503685827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15616640859744621352991077 2928120161202116503685827)
                ·
                  refine ⟨4392180241803174755528741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2928120161202116503685827 4392180241803174755528741)
                  ·
                    refine ⟨823533795338095266661639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4392180241803174755528741 823533795338095266661639)
                    ·
                      rfl

theorem cell23_4811479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 1, 4].length) (baseStart_4811479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811479 prefixEnd_4811479 := by exact prefixLift 4811479
  have htrace : WordTrace (prefixWord ++ tailWord_4811479) baseStart_4811479 baseEnd_4811479 := by
    simpa [prefixWord, tailWord_4811479, baseEnd_4811479] using wordTrace_append hprefix tailTrace_4811479
  have hstable : (prefixWord ++ tailWord_4811479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811479).length < 2 ^ (prefixWord ++ tailWord_4811479).sum := by decide
  have hdescent : baseEnd_4811479 < baseStart_4811479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811512 : List Nat := [2, 1, 2, 1, 1, 2, 3, 3, 1, 5, 2]
def baseStart_4811512 : Nat := 118140960795 + 4811512 * 2 ^ 59
def prefixEnd_4811512 : Nat := 4983230072969 + 3 ^ 40 * 4811512 * 2
def baseEnd_4811512 : Nat := 2470618330875884170872265

theorem tailTrace_4811512 : CollatzResearch.WordTrace tailWord_4811512 prefixEnd_4811512 2470618330875884170872265 := by
  unfold tailWord_4811512
  simp only [CollatzResearch.WordTrace]
  refine ⟨87745129872360619836290395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116993506496480826448387193 87745129872360619836290395)
  ·
    refine ⟨131617694808540929754435593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87745129872360619836290395 131617694808540929754435593)
    ·
      refine ⟨98713271106405697315826695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131617694808540929754435593 98713271106405697315826695)
      ·
        refine ⟨148069906659608545973740043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98713271106405697315826695 148069906659608545973740043)
        ·
          refine ⟨222104859989412818960610065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148069906659608545973740043 222104859989412818960610065)
          ·
            refine ⟨166578644992059614220457549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222104859989412818960610065 166578644992059614220457549)
            ·
              refine ⟨62466991872022355332671581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166578644992059614220457549 62466991872022355332671581)
              ·
                refine ⟨23425121952008383249751843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62466991872022355332671581 23425121952008383249751843)
                ·
                  refine ⟨35137682928012574874627765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23425121952008383249751843 35137682928012574874627765)
                  ·
                    refine ⟨3294157774501178894496353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35137682928012574874627765 3294157774501178894496353)
                    ·
                      refine ⟨2470618330875884170872265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3294157774501178894496353 2470618330875884170872265)
                      ·
                        rfl

theorem cell23_4811512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 1, 5, 2].length) (baseStart_4811512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811512 prefixEnd_4811512 := by exact prefixLift 4811512
  have htrace : WordTrace (prefixWord ++ tailWord_4811512) baseStart_4811512 baseEnd_4811512 := by
    simpa [prefixWord, tailWord_4811512, baseEnd_4811512] using wordTrace_append hprefix tailTrace_4811512
  have hstable : (prefixWord ++ tailWord_4811512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811512).length < 2 ^ (prefixWord ++ tailWord_4811512).sum := by decide
  have hdescent : baseEnd_4811512 < baseStart_4811512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811545 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 3, 1, 5]
def baseStart_4811545 : Nat := 118140960795 + 4811545 * 2 ^ 59
def prefixEnd_4811545 : Nat := 4983230072969 + 3 ^ 40 * 4811545 * 2
def baseEnd_4811545 : Nat := 2470635275737482541759613

theorem tailTrace_4811545 : CollatzResearch.WordTrace tailWord_4811545 prefixEnd_4811545 2470635275737482541759613 := by
  unfold tailWord_4811545
  simp only [CollatzResearch.WordTrace]
  refine ⟨175491463353601686308532089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116994308902401124205688059 175491463353601686308532089)
  ·
    refine ⟨131618597515201264731399067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175491463353601686308532089 131618597515201264731399067)
    ·
      refine ⟨197427896272801897097098601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131618597515201264731399067 197427896272801897097098601)
      ·
        refine ⟨148070922204601422822823951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197427896272801897097098601 148070922204601422822823951)
        ·
          refine ⟨222106383306902134234235927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148070922204601422822823951 222106383306902134234235927)
          ·
            refine ⟨333159574960353201351353891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222106383306902134234235927 333159574960353201351353891)
            ·
              refine ⟨499739362440529802027030837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333159574960353201351353891 499739362440529802027030837)
              ·
                refine ⟨46850565228799668940034141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 499739362440529802027030837 46850565228799668940034141)
                ·
                  refine ⟨17568961960799875852512803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46850565228799668940034141 17568961960799875852512803)
                  ·
                    refine ⟨26353442941199813778769205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17568961960799875852512803 26353442941199813778769205)
                    ·
                      refine ⟨2470635275737482541759613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26353442941199813778769205 2470635275737482541759613)
                      ·
                        rfl

theorem cell23_4811545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_4811545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811545 prefixEnd_4811545 := by exact prefixLift 4811545
  have htrace : WordTrace (prefixWord ++ tailWord_4811545) baseStart_4811545 baseEnd_4811545 := by
    simpa [prefixWord, tailWord_4811545, baseEnd_4811545] using wordTrace_append hprefix tailTrace_4811545
  have hstable : (prefixWord ++ tailWord_4811545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811545).length < 2 ^ (prefixWord ++ tailWord_4811545).sum := by decide
  have hdescent : baseEnd_4811545 < baseStart_4811545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811556 : List Nat := [2, 3, 1, 3, 3, 2, 1, 2, 1, 5]
def baseStart_4811556 : Nat := 118140960795 + 4811556 * 2 ^ 59
def prefixEnd_4811556 : Nat := 4983230072969 + 3 ^ 40 * 4811556 * 2
def baseEnd_4811556 : Nat := 823546974674893999574021

theorem tailTrace_4811556 : CollatzResearch.WordTrace tailWord_4811556 prefixEnd_4811556 823546974674893999574021 := by
  unfold tailWord_4811556
  simp only [CollatzResearch.WordTrace]
  refine ⟨87745932278280917593591261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116994576371041223458121681 87745932278280917593591261)
  ·
    refine ⟨32904724604355344097596723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87745932278280917593591261 32904724604355344097596723)
    ·
      refine ⟨49357086906533016146395085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32904724604355344097596723 49357086906533016146395085)
      ·
        refine ⟨18508907589949881054898157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49357086906533016146395085 18508907589949881054898157)
        ·
          refine ⟨6940840346231205395586809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18508907589949881054898157 6940840346231205395586809)
          ·
            refine ⟨5205630259673404046690107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6940840346231205395586809 5205630259673404046690107)
            ·
              refine ⟨7808445389510106070035161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5205630259673404046690107 7808445389510106070035161)
              ·
                refine ⟨5856334042132579552526371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7808445389510106070035161 5856334042132579552526371)
                ·
                  refine ⟨8784501063198869328789557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5856334042132579552526371 8784501063198869328789557)
                  ·
                    refine ⟨823546974674893999574021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8784501063198869328789557 823546974674893999574021)
                    ·
                      rfl

theorem cell23_4811556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_4811556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811556 prefixEnd_4811556 := by exact prefixLift 4811556
  have htrace : WordTrace (prefixWord ++ tailWord_4811556) baseStart_4811556 baseEnd_4811556 := by
    simpa [prefixWord, tailWord_4811556, baseEnd_4811556] using wordTrace_append hprefix tailTrace_4811556
  have hstable : (prefixWord ++ tailWord_4811556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811556).length < 2 ^ (prefixWord ++ tailWord_4811556).sum := by decide
  have hdescent : baseEnd_4811556 < baseStart_4811556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811582 : List Nat := [4, 2, 1, 2, 3, 11]
def baseStart_4811582 : Nat := 118140960795 + 4811582 * 2 ^ 59
def prefixEnd_4811582 : Nat := 4983230072969 + 3 ^ 40 * 4811582 * 2
def baseEnd_4811582 : Nat := 10167301541241559246901

theorem tailTrace_4811582 : CollatzResearch.WordTrace tailWord_4811582 prefixEnd_4811582 10167301541241559246901 := by
  unfold tailWord_4811582
  simp only [CollatzResearch.WordTrace]
  refine ⟨21936601606808455203453625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116995208569645094418419333 21936601606808455203453625)
  ·
    refine ⟨16452451205106341402590219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21936601606808455203453625 16452451205106341402590219)
    ·
      refine ⟨24678676807659512103885329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16452451205106341402590219 24678676807659512103885329)
      ·
        refine ⟨18509007605744634077913997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24678676807659512103885329 18509007605744634077913997)
        ·
          refine ⟨6940877852154237779217749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18509007605744634077913997 6940877852154237779217749)
          ·
            refine ⟨10167301541241559246901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6940877852154237779217749 10167301541241559246901)
            ·
              rfl

theorem cell23_4811582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 11].length) (baseStart_4811582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811582 prefixEnd_4811582 := by exact prefixLift 4811582
  have htrace : WordTrace (prefixWord ++ tailWord_4811582) baseStart_4811582 baseEnd_4811582 := by
    simpa [prefixWord, tailWord_4811582, baseEnd_4811582] using wordTrace_append hprefix tailTrace_4811582
  have hstable : (prefixWord ++ tailWord_4811582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811582).length < 2 ^ (prefixWord ++ tailWord_4811582).sum := by decide
  have hdescent : baseEnd_4811582 < baseStart_4811582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811592 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 3, 3, 3]
def baseStart_4811592 : Nat := 118140960795 + 4811592 * 2 ^ 59
def prefixEnd_4811592 : Nat := 4983230072969 + 3 ^ 40 * 4811592 * 2
def baseEnd_4811592 : Nat := 2470659409328243857871897

theorem tailTrace_4811592 : CollatzResearch.WordTrace tailWord_4811592 prefixEnd_4811592 2470659409328243857871897 := by
  unfold tailWord_4811592
  simp only [CollatzResearch.WordTrace]
  refine ⟨87746588792215706667746515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116995451722954275556995353 87746588792215706667746515)
  ·
    refine ⟨131619883188323560001619773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87746588792215706667746515 131619883188323560001619773)
    ·
      refine ⟨49357456195621335000607415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131619883188323560001619773 49357456195621335000607415)
      ·
        refine ⟨74036184293432002500911123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49357456195621335000607415 74036184293432002500911123)
        ·
          refine ⟨111054276440148003751366685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74036184293432002500911123 111054276440148003751366685)
          ·
            refine ⟨41645353665055501406762507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111054276440148003751366685 41645353665055501406762507)
            ·
              refine ⟨62468030497583252110143761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41645353665055501406762507 62468030497583252110143761)
              ·
                refine ⟨46851022873187439082607821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62468030497583252110143761 46851022873187439082607821)
                ·
                  refine ⟨17569133577445289655977933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46851022873187439082607821 17569133577445289655977933)
                  ·
                    refine ⟨6588425091541983620991725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17569133577445289655977933 6588425091541983620991725)
                    ·
                      refine ⟨2470659409328243857871897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6588425091541983620991725 2470659409328243857871897)
                      ·
                        rfl

theorem cell23_4811592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_4811592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811592 prefixEnd_4811592 := by exact prefixLift 4811592
  have htrace : WordTrace (prefixWord ++ tailWord_4811592) baseStart_4811592 baseEnd_4811592 := by
    simpa [prefixWord, tailWord_4811592, baseEnd_4811592] using wordTrace_append hprefix tailTrace_4811592
  have hstable : (prefixWord ++ tailWord_4811592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811592).length < 2 ^ (prefixWord ++ tailWord_4811592).sum := by decide
  have hdescent : baseEnd_4811592 < baseStart_4811592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811593 : List Nat := [1, 2, 1, 1, 2, 6, 1, 4, 1, 2, 2]
def baseStart_4811593 : Nat := 118140960795 + 4811593 * 2 ^ 59
def prefixEnd_4811593 : Nat := 4983230072969 + 3 ^ 40 * 4811593 * 2
def baseEnd_4811593 : Nat := 2470659922808898353959393

theorem tailTrace_4811593 : CollatzResearch.WordTrace tailWord_4811593 prefixEnd_4811593 2470659922808898353959393 := by
  unfold tailWord_4811593
  simp only [CollatzResearch.WordTrace]
  refine ⟨175493214057427790506279433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116995476038285193670852955 175493214057427790506279433)
  ·
    refine ⟨131619910543070842879709575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175493214057427790506279433 131619910543070842879709575)
    ·
      refine ⟨197429865814606264319564363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131619910543070842879709575 197429865814606264319564363)
      ·
        refine ⟨296144798721909396479346545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197429865814606264319564363 296144798721909396479346545)
        ·
          refine ⟨222108599041432047359509909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 296144798721909396479346545 222108599041432047359509909)
          ·
            refine ⟨10411340580067127219977027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 222108599041432047359509909 10411340580067127219977027)
            ·
              refine ⟨15617010870100690829965541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10411340580067127219977027 15617010870100690829965541)
              ·
                refine ⟨2928189538143879530618539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15617010870100690829965541 2928189538143879530618539)
                ·
                  refine ⟨4392284307215819295927809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2928189538143879530618539 4392284307215819295927809)
                  ·
                    refine ⟨3294213230411864471945857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4392284307215819295927809 3294213230411864471945857)
                    ·
                      refine ⟨2470659922808898353959393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3294213230411864471945857 2470659922808898353959393)
                      ·
                        rfl

theorem cell23_4811593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 1, 2, 2].length) (baseStart_4811593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811593 prefixEnd_4811593 := by exact prefixLift 4811593
  have htrace : WordTrace (prefixWord ++ tailWord_4811593) baseStart_4811593 baseEnd_4811593 := by
    simpa [prefixWord, tailWord_4811593, baseEnd_4811593] using wordTrace_append hprefix tailTrace_4811593
  have hstable : (prefixWord ++ tailWord_4811593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811593).length < 2 ^ (prefixWord ++ tailWord_4811593).sum := by decide
  have hdescent : baseEnd_4811593 < baseStart_4811593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811609 : List Nat := [1, 2, 1, 2, 2, 5, 2, 1, 1, 3, 3]
def baseStart_4811609 : Nat := 118140960795 + 4811609 * 2 ^ 59
def prefixEnd_4811609 : Nat := 4983230072969 + 3 ^ 40 * 4811609 * 2
def baseEnd_4811609 : Nat := 2470668138499370291359319

theorem tailTrace_4811609 : CollatzResearch.WordTrace tailWord_4811609 prefixEnd_4811609 2470668138499370291359319 := by
  unfold tailWord_4811609
  simp only [CollatzResearch.WordTrace]
  refine ⟨175493797625369825238861881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116995865083579883492574587 175493797625369825238861881)
  ·
    refine ⟨131620348219027368929146411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175493797625369825238861881 131620348219027368929146411)
    ·
      refine ⟨197430522328541053393719617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131620348219027368929146411 197430522328541053393719617)
      ·
        refine ⟨148072891746405790045289713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197430522328541053393719617 148072891746405790045289713)
        ·
          refine ⟨111054668809804342533967285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148072891746405790045289713 111054668809804342533967285)
          ·
            refine ⟨10411375200919157112559433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111054668809804342533967285 10411375200919157112559433)
            ·
              refine ⟨7808531400689367834419575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10411375200919157112559433 7808531400689367834419575)
              ·
                refine ⟨11712797101034051751629363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7808531400689367834419575 11712797101034051751629363)
                ·
                  refine ⟨17569195651551077627444045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11712797101034051751629363 17569195651551077627444045)
                  ·
                    refine ⟨6588448369331654110291517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17569195651551077627444045 6588448369331654110291517)
                    ·
                      refine ⟨2470668138499370291359319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6588448369331654110291517 2470668138499370291359319)
                      ·
                        rfl

theorem cell23_4811609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 3, 3].length) (baseStart_4811609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811609 prefixEnd_4811609 := by exact prefixLift 4811609
  have htrace : WordTrace (prefixWord ++ tailWord_4811609) baseStart_4811609 baseEnd_4811609 := by
    simpa [prefixWord, tailWord_4811609, baseEnd_4811609] using wordTrace_append hprefix tailTrace_4811609
  have hstable : (prefixWord ++ tailWord_4811609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811609).length < 2 ^ (prefixWord ++ tailWord_4811609).sum := by decide
  have hdescent : baseEnd_4811609 < baseStart_4811609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811630 : List Nat := [4, 1, 2, 3, 2, 2, 2, 1, 1, 2, 3]
def baseStart_4811630 : Nat := 118140960795 + 4811630 * 2 ^ 59
def prefixEnd_4811630 : Nat := 4983230072969 + 3 ^ 40 * 4811630 * 2
def baseEnd_4811630 : Nat := 2470678921593114709196723

theorem tailTrace_4811630 : CollatzResearch.WordTrace tailWord_4811630 prefixEnd_4811630 2470678921593114709196723 := by
  unfold tailWord_4811630
  simp only [CollatzResearch.WordTrace]
  refine ⟨21936820444786718228172043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116996375705529163883584229 21936820444786718228172043)
  ·
    refine ⟨32905230667180077342258065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21936820444786718228172043 32905230667180077342258065)
    ·
      refine ⟨24678923000385058006693549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32905230667180077342258065 24678923000385058006693549)
      ·
        refine ⟨9254596125144396752510081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24678923000385058006693549 9254596125144396752510081)
        ·
          refine ⟨6940947093858297564382561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9254596125144396752510081 6940947093858297564382561)
          ·
            refine ⟨5205710320393723173286921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6940947093858297564382561 5205710320393723173286921)
            ·
              refine ⟨3904282740295292379965191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5205710320393723173286921 3904282740295292379965191)
              ·
                refine ⟨5856424110442938569947787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3904282740295292379965191 5856424110442938569947787)
                ·
                  refine ⟨8784636165664407854921681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5856424110442938569947787 8784636165664407854921681)
                  ·
                    refine ⟨6588477124248305891191261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8784636165664407854921681 6588477124248305891191261)
                    ·
                      refine ⟨2470678921593114709196723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6588477124248305891191261 2470678921593114709196723)
                      ·
                        rfl

theorem cell23_4811630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_4811630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811630 prefixEnd_4811630 := by exact prefixLift 4811630
  have htrace : WordTrace (prefixWord ++ tailWord_4811630) baseStart_4811630 baseEnd_4811630 := by
    simpa [prefixWord, tailWord_4811630, baseEnd_4811630] using wordTrace_append hprefix tailTrace_4811630
  have hstable : (prefixWord ++ tailWord_4811630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811630).length < 2 ^ (prefixWord ++ tailWord_4811630).sum := by decide
  have hdescent : baseEnd_4811630 < baseStart_4811630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811652 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_4811652 : Nat := 118140960795 + 4811652 * 2 ^ 59
def prefixEnd_4811652 : Nat := 4983230072969 + 3 ^ 40 * 4811652 * 2
def baseEnd_4811652 : Nat := 2470690218167513623121621

theorem tailTrace_4811652 : CollatzResearch.WordTrace tailWord_4811652 prefixEnd_4811652 2470690218167513623121621 := by
  unfold tailWord_4811652
  simp only [CollatzResearch.WordTrace]
  refine ⟨87747682982107021791338605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116996910642809362388451473 87747682982107021791338605)
  ·
    refine ⟨32905381118290133171751977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87747682982107021791338605 32905381118290133171751977)
    ·
      refine ⟨24679035838717599878813983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32905381118290133171751977 24679035838717599878813983)
      ·
        refine ⟨37018553758076399818220975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24679035838717599878813983 37018553758076399818220975)
        ·
          refine ⟨55527830637114599727331463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37018553758076399818220975 55527830637114599727331463)
          ·
            refine ⟨83291745955671899590997195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55527830637114599727331463 83291745955671899590997195)
            ·
              refine ⟨124937618933507849386495793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83291745955671899590997195 124937618933507849386495793)
              ·
                refine ⟨93703214200130887039871845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124937618933507849386495793 93703214200130887039871845)
                ·
                  refine ⟨17569352662524541319975971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93703214200130887039871845 17569352662524541319975971)
                  ·
                    refine ⟨26354028993786811979963957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17569352662524541319975971 26354028993786811979963957)
                    ·
                      refine ⟨2470690218167513623121621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26354028993786811979963957 2470690218167513623121621)
                      ·
                        rfl

theorem cell23_4811652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_4811652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811652 prefixEnd_4811652 := by exact prefixLift 4811652
  have htrace : WordTrace (prefixWord ++ tailWord_4811652) baseStart_4811652 baseEnd_4811652 := by
    simpa [prefixWord, tailWord_4811652, baseEnd_4811652] using wordTrace_append hprefix tailTrace_4811652
  have hstable : (prefixWord ++ tailWord_4811652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811652).length < 2 ^ (prefixWord ++ tailWord_4811652).sum := by decide
  have hdescent : baseEnd_4811652 < baseStart_4811652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811700 : List Nat := [2, 5, 2, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_4811700 : Nat := 118140960795 + 4811700 * 2 ^ 59
def prefixEnd_4811700 : Nat := 4983230072969 + 3 ^ 40 * 4811700 * 2
def baseEnd_4811700 : Nat := 2470714865238929435321401

theorem tailTrace_4811700 : CollatzResearch.WordTrace tailWord_4811700 prefixEnd_4811700 2470714865238929435321401 := by
  unfold tailWord_4811700
  simp only [CollatzResearch.WordTrace]
  refine ⟨87748558334020073890212277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116998077778693431853616369 87748558334020073890212277)
  ·
    refine ⟨8226427343814381927207401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87748558334020073890212277 8226427343814381927207401)
    ·
      refine ⟨6169820507860786445405551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8226427343814381927207401 6169820507860786445405551)
      ·
        refine ⟨9254730761791179668108327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6169820507860786445405551 9254730761791179668108327)
        ·
          refine ⟨13882096142686769502162491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9254730761791179668108327 13882096142686769502162491)
          ·
            refine ⟨20823144214030154253243737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13882096142686769502162491 20823144214030154253243737)
            ·
              refine ⟨15617358160522615689932803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20823144214030154253243737 15617358160522615689932803)
              ·
                refine ⟨23426037240783923534899205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15617358160522615689932803 23426037240783923534899205)
                ·
                  refine ⟨4392381982646985662793601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23426037240783923534899205 4392381982646985662793601)
                  ·
                    refine ⟨3294286486985239247095201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4392381982646985662793601 3294286486985239247095201)
                    ·
                      refine ⟨2470714865238929435321401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3294286486985239247095201 2470714865238929435321401)
                      ·
                        rfl

theorem cell23_4811700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_4811700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811700 prefixEnd_4811700 := by exact prefixLift 4811700
  have htrace : WordTrace (prefixWord ++ tailWord_4811700) baseStart_4811700 baseEnd_4811700 := by
    simpa [prefixWord, tailWord_4811700, baseEnd_4811700] using wordTrace_append hprefix tailTrace_4811700
  have hstable : (prefixWord ++ tailWord_4811700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811700).length < 2 ^ (prefixWord ++ tailWord_4811700).sum := by decide
  have hdescent : baseEnd_4811700 < baseStart_4811700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811706 : List Nat := [3, 1, 1, 1, 2, 1, 7, 2, 5]
def baseStart_4811706 : Nat := 118140960795 + 4811706 * 2 ^ 59
def prefixEnd_4811706 : Nat := 4983230072969 + 3 ^ 40 * 4811706 * 2
def baseEnd_4811706 : Nat := 274524216235872934649597

theorem tailTrace_4811706 : CollatzResearch.WordTrace tailWord_4811706 prefixEnd_4811706 274524216235872934649597 := by
  unfold tailWord_4811706
  simp only [CollatzResearch.WordTrace]
  refine ⟨43874333876504602701285743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116998223670678940536761981 43874333876504602701285743)
  ·
    refine ⟨65811500814756904051928615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43874333876504602701285743 65811500814756904051928615)
    ·
      refine ⟨98717251222135356077892923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65811500814756904051928615 98717251222135356077892923)
      ·
        refine ⟨148075876833203034116839385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98717251222135356077892923 148075876833203034116839385)
        ·
          refine ⟨111056907624902275587629539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148075876833203034116839385 111056907624902275587629539)
          ·
            refine ⟨166585361437353413381444309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111056907624902275587629539 166585361437353413381444309)
            ·
              refine ⟨3904344408687970626127601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 166585361437353413381444309 3904344408687970626127601)
              ·
                refine ⟨2928258306515977969595701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3904344408687970626127601 2928258306515977969595701)
                ·
                  refine ⟨274524216235872934649597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2928258306515977969595701 274524216235872934649597)
                  ·
                    rfl

theorem cell23_4811706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 5].length) (baseStart_4811706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811706 prefixEnd_4811706 := by exact prefixLift 4811706
  have htrace : WordTrace (prefixWord ++ tailWord_4811706) baseStart_4811706 baseEnd_4811706 := by
    simpa [prefixWord, tailWord_4811706, baseEnd_4811706] using wordTrace_append hprefix tailTrace_4811706
  have hstable : (prefixWord ++ tailWord_4811706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811706).length < 2 ^ (prefixWord ++ tailWord_4811706).sum := by decide
  have hdescent : baseEnd_4811706 < baseStart_4811706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811712 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 7]
def baseStart_4811712 : Nat := 118140960795 + 4811712 * 2 ^ 59
def prefixEnd_4811712 : Nat := 4983230072969 + 3 ^ 40 * 4811712 * 2
def baseEnd_4811712 : Nat := 2470721027006783388371345

theorem tailTrace_4811712 : CollatzResearch.WordTrace tailWord_4811712 prefixEnd_4811712 2470721027006783388371345 := by
  unfold tailWord_4811712
  simp only [CollatzResearch.WordTrace]
  refine ⟨87748777171998336914930695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116998369562664449219907593 87748777171998336914930695)
  ·
    refine ⟨131623165757997505372396043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87748777171998336914930695 131623165757997505372396043)
    ·
      refine ⟨197434748636996258058594065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131623165757997505372396043 197434748636996258058594065)
      ·
        refine ⟨148076061477747193543945549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197434748636996258058594065 148076061477747193543945549)
        ·
          refine ⟨55528523054155197578979581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148076061477747193543945549 55528523054155197578979581)
          ·
            refine ⟨20823196145308199092117343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55528523054155197578979581 20823196145308199092117343)
            ·
              refine ⟨31234794217962298638176015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20823196145308199092117343 31234794217962298638176015)
              ·
                refine ⟨46852191326943447957264023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31234794217962298638176015 46852191326943447957264023)
                ·
                  refine ⟨70278286990415171935896035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46852191326943447957264023 70278286990415171935896035)
                  ·
                    refine ⟨105417430485622757903844053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70278286990415171935896035 105417430485622757903844053)
                    ·
                      refine ⟨2470721027006783388371345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 105417430485622757903844053 2470721027006783388371345)
                      ·
                        rfl

theorem cell23_4811712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_4811712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811712 prefixEnd_4811712 := by exact prefixLift 4811712
  have htrace : WordTrace (prefixWord ++ tailWord_4811712) baseStart_4811712 baseEnd_4811712 := by
    simpa [prefixWord, tailWord_4811712, baseEnd_4811712] using wordTrace_append hprefix tailTrace_4811712
  have hstable : (prefixWord ++ tailWord_4811712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811712).length < 2 ^ (prefixWord ++ tailWord_4811712).sum := by decide
  have hdescent : baseEnd_4811712 < baseStart_4811712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811746 : List Nat := [3, 3, 3, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_4811746 : Nat := 118140960795 + 4811746 * 2 ^ 59
def prefixEnd_4811746 : Nat := 4983230072969 + 3 ^ 40 * 4811746 * 2
def baseEnd_4811746 : Nat := 2470738485349036255346189

theorem tailTrace_4811746 : CollatzResearch.WordTrace tailWord_4811746 prefixEnd_4811746 2470738485349036255346189 := by
  unfold tailWord_4811746
  simp only [CollatzResearch.WordTrace]
  refine ⟨43874698606468374409149773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116999196283915665091066061 43874698606468374409149773)
  ·
    refine ⟨16453011977425640403431165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43874698606468374409149773 16453011977425640403431165)
    ·
      refine ⟨6169879491534615151286687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16453011977425640403431165 6169879491534615151286687)
      ·
        refine ⟨9254819237301922726930031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6169879491534615151286687 9254819237301922726930031)
        ·
          refine ⟨13882228855952884090395047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9254819237301922726930031 13882228855952884090395047)
          ·
            refine ⟨20823343283929326135592571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13882228855952884090395047 20823343283929326135592571)
            ·
              refine ⟨31235014925893989203388857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20823343283929326135592571 31235014925893989203388857)
              ·
                refine ⟨23426261194420491902541643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31235014925893989203388857 23426261194420491902541643)
                ·
                  refine ⟨35139391791630737853812465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23426261194420491902541643 35139391791630737853812465)
                  ·
                    refine ⟨26354543843723053390359349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35139391791630737853812465 26354543843723053390359349)
                    ·
                      refine ⟨2470738485349036255346189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26354543843723053390359349 2470738485349036255346189)
                      ·
                        rfl

theorem cell23_4811746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_4811746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811746 prefixEnd_4811746 := by exact prefixLift 4811746
  have htrace : WordTrace (prefixWord ++ tailWord_4811746) baseStart_4811746 baseEnd_4811746 := by
    simpa [prefixWord, tailWord_4811746, baseEnd_4811746] using wordTrace_append hprefix tailTrace_4811746
  have hstable : (prefixWord ++ tailWord_4811746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811746).length < 2 ^ (prefixWord ++ tailWord_4811746).sum := by decide
  have hdescent : baseEnd_4811746 < baseStart_4811746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811874 : List Nat := [3, 3, 2, 2, 1, 2, 3, 2, 1, 1, 3]
def baseStart_4811874 : Nat := 118140960795 + 4811874 * 2 ^ 59
def prefixEnd_4811874 : Nat := 4983230072969 + 3 ^ 40 * 4811874 * 2
def baseEnd_4811874 : Nat := 2470804210872811754545601

theorem tailTrace_4811874 : CollatzResearch.WordTrace tailWord_4811874 prefixEnd_4811874 2470804210872811754545601 := by
  unfold tailWord_4811874
  simp only [CollatzResearch.WordTrace]
  refine ⟨43875865742352443874314669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117002308646273183664839117 43875865742352443874314669)
  ·
    refine ⟨16453449653382166452868001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43875865742352443874314669 16453449653382166452868001)
    ·
      refine ⟨12340087240036624839651001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16453449653382166452868001 12340087240036624839651001)
      ·
        refine ⟨9255065430027468629738251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12340087240036624839651001 9255065430027468629738251)
        ·
          refine ⟨13882598145041202944607377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9255065430027468629738251 13882598145041202944607377)
          ·
            refine ⟨10411948608780902208455533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13882598145041202944607377 10411948608780902208455533)
            ·
              refine ⟨3904480728292838328170825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10411948608780902208455533 3904480728292838328170825)
              ·
                refine ⟨2928360546219628746128119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3904480728292838328170825 2928360546219628746128119)
                ·
                  refine ⟨4392540819329443119192179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2928360546219628746128119 4392540819329443119192179)
                  ·
                    refine ⟨6588811228994164678788269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4392540819329443119192179 6588811228994164678788269)
                    ·
                      refine ⟨2470804210872811754545601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6588811228994164678788269 2470804210872811754545601)
                      ·
                        rfl

theorem cell23_4811874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_4811874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811874 prefixEnd_4811874 := by exact prefixLift 4811874
  have htrace : WordTrace (prefixWord ++ tailWord_4811874) baseStart_4811874 baseEnd_4811874 := by
    simpa [prefixWord, tailWord_4811874, baseEnd_4811874] using wordTrace_append hprefix tailTrace_4811874
  have hstable : (prefixWord ++ tailWord_4811874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811874).length < 2 ^ (prefixWord ++ tailWord_4811874).sum := by decide
  have hdescent : baseEnd_4811874 < baseStart_4811874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811886 : List Nat := [4, 1, 2, 2, 1, 3, 2, 8]
def baseStart_4811886 : Nat := 118140960795 + 4811886 * 2 ^ 59
def prefixEnd_4811886 : Nat := 4983230072969 + 3 ^ 40 * 4811886 * 2
def baseEnd_4811886 : Nat := 91511495282987618799835

theorem tailTrace_4811886 : CollatzResearch.WordTrace tailWord_4811886 prefixEnd_4811886 91511495282987618799835 := by
  unfold tailWord_4811886
  simp only [CollatzResearch.WordTrace]
  refine ⟨21937987580670787693336939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117002600430244201031130341 21937987580670787693336939)
  ·
    refine ⟨32906981371006181540005409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21937987580670787693336939 32906981371006181540005409)
    ·
      refine ⟨24680236028254636155004057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32906981371006181540005409 24680236028254636155004057)
      ·
        refine ⟨18510177021190977116253043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24680236028254636155004057 18510177021190977116253043)
        ·
          refine ⟨27765265531786465674379565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18510177021190977116253043 27765265531786465674379565)
          ·
            refine ⟨10411974574419924627892337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27765265531786465674379565 10411974574419924627892337)
            ·
              refine ⟨7808980930814943470919253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10411974574419924627892337 7808980930814943470919253)
              ·
                refine ⟨91511495282987618799835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7808980930814943470919253 91511495282987618799835)
                ·
                  rfl

theorem cell23_4811886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 8].length) (baseStart_4811886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811886 prefixEnd_4811886 := by exact prefixLift 4811886
  have htrace : WordTrace (prefixWord ++ tailWord_4811886) baseStart_4811886 baseEnd_4811886 := by
    simpa [prefixWord, tailWord_4811886, baseEnd_4811886] using wordTrace_append hprefix tailTrace_4811886
  have hstable : (prefixWord ++ tailWord_4811886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811886).length < 2 ^ (prefixWord ++ tailWord_4811886).sum := by decide
  have hdescent : baseEnd_4811886 < baseStart_4811886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811923 : List Nat := [1, 1, 1, 2, 1, 2, 4, 5, 1, 3, 2]
def baseStart_4811923 : Nat := 118140960795 + 4811923 * 2 ^ 59
def prefixEnd_4811923 : Nat := 4983230072969 + 3 ^ 40 * 4811923 * 2
def baseEnd_4811923 : Nat := 2470829371424882062832875

theorem tailTrace_4811923 : CollatzResearch.WordTrace tailWord_4811923 prefixEnd_4811923 2470829371424882062832875 := by
  unfold tailWord_4811923
  simp only [CollatzResearch.WordTrace]
  refine ⟨175505250146232256865792423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117003500097488171243861615 175505250146232256865792423)
  ·
    refine ⟨263257875219348385298688635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175505250146232256865792423 263257875219348385298688635)
    ·
      refine ⟨394886812829022577948032953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263257875219348385298688635 394886812829022577948032953)
      ·
        refine ⟨296165109621766933461024715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 394886812829022577948032953 296165109621766933461024715)
        ·
          refine ⟨444247664432650400191537073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296165109621766933461024715 444247664432650400191537073)
          ·
            refine ⟨333185748324487800143652805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 444247664432650400191537073 333185748324487800143652805)
            ·
              refine ⟨62472327810841462526934901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 333185748324487800143652805 62472327810841462526934901)
              ·
                refine ⟨5856780732266387111900147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62472327810841462526934901 5856780732266387111900147)
                ·
                  refine ⟨8785171098399580667850221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5856780732266387111900147 8785171098399580667850221)
                  ·
                    refine ⟨3294439161899842750443833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8785171098399580667850221 3294439161899842750443833)
                    ·
                      refine ⟨2470829371424882062832875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3294439161899842750443833 2470829371424882062832875)
                      ·
                        rfl

theorem cell23_4811923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 3, 2].length) (baseStart_4811923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811923 prefixEnd_4811923 := by exact prefixLift 4811923
  have htrace : WordTrace (prefixWord ++ tailWord_4811923) baseStart_4811923 baseEnd_4811923 := by
    simpa [prefixWord, tailWord_4811923, baseEnd_4811923] using wordTrace_append hprefix tailTrace_4811923
  have hstable : (prefixWord ++ tailWord_4811923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811923).length < 2 ^ (prefixWord ++ tailWord_4811923).sum := by decide
  have hdescent : baseEnd_4811923 < baseStart_4811923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811930 : List Nat := [3, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3]
def baseStart_4811930 : Nat := 118140960795 + 4811930 * 2 ^ 59
def prefixEnd_4811930 : Nat := 4983230072969 + 3 ^ 40 * 4811930 * 2
def baseEnd_4811930 : Nat := 2470832965789463535445343

theorem tailTrace_4811930 : CollatzResearch.WordTrace tailWord_4811930 prefixEnd_4811930 2470832965789463535445343 := by
  unfold tailWord_4811930
  simp only [CollatzResearch.WordTrace]
  refine ⟨43876376364301724265324311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117003670304804598040864829 43876376364301724265324311)
  ·
    refine ⟨65814564546452586397986467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43876376364301724265324311 65814564546452586397986467)
    ·
      refine ⟨98721846819678879596979701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65814564546452586397986467 98721846819678879596979701)
      ·
        refine ⟨9255173139344894962216847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98721846819678879596979701 9255173139344894962216847)
        ·
          refine ⟨13882759709017342443325271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9255173139344894962216847 13882759709017342443325271)
          ·
            refine ⟨20824139563526013664987907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13882759709017342443325271 20824139563526013664987907)
            ·
              refine ⟨31236209345289020497481861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20824139563526013664987907 31236209345289020497481861)
              ·
                refine ⟨5856789252241691343277849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31236209345289020497481861 5856789252241691343277849)
                ·
                  refine ⟨4392591939181268507458387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5856789252241691343277849 4392591939181268507458387)
                  ·
                    refine ⟨6588887908771902761187581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4392591939181268507458387 6588887908771902761187581)
                    ·
                      refine ⟨2470832965789463535445343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6588887908771902761187581 2470832965789463535445343)
                      ·
                        rfl

theorem cell23_4811930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_4811930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811930 prefixEnd_4811930 := by exact prefixLift 4811930
  have htrace : WordTrace (prefixWord ++ tailWord_4811930) baseStart_4811930 baseEnd_4811930 := by
    simpa [prefixWord, tailWord_4811930, baseEnd_4811930] using wordTrace_append hprefix tailTrace_4811930
  have hstable : (prefixWord ++ tailWord_4811930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811930).length < 2 ^ (prefixWord ++ tailWord_4811930).sum := by decide
  have hdescent : baseEnd_4811930 < baseStart_4811930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811939 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 5]
def baseStart_4811939 : Nat := 118140960795 + 4811939 * 2 ^ 59
def prefixEnd_4811939 : Nat := 4983230072969 + 3 ^ 40 * 4811939 * 2
def baseEnd_4811939 : Nat := 2470837587115354000232801

theorem tailTrace_4811939 : CollatzResearch.WordTrace tailWord_4811939 prefixEnd_4811939 2470837587115354000232801 := by
  unfold tailWord_4811939
  simp only [CollatzResearch.WordTrace]
  refine ⟨175505833714174291598374871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117003889142782861065583247 175505833714174291598374871)
  ·
    refine ⟨263258750571261437397562307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175505833714174291598374871 263258750571261437397562307)
    ·
      refine ⟨394888125856892156096343461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263258750571261437397562307 394888125856892156096343461)
      ·
        refine ⟨74041523598167279268064399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 394888125856892156096343461 74041523598167279268064399)
        ·
          refine ⟨111062285397250918902096599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74041523598167279268064399 111062285397250918902096599)
          ·
            refine ⟨166593428095876378353144899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111062285397250918902096599 166593428095876378353144899)
            ·
              refine ⟨249890142143814567529717349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166593428095876378353144899 249890142143814567529717349)
              ·
                refine ⟨46854401651965231411822003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 249890142143814567529717349 46854401651965231411822003)
                ·
                  refine ⟨70281602477947847117733005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46854401651965231411822003 70281602477947847117733005)
                  ·
                    refine ⟨26355600929230442669149877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70281602477947847117733005 26355600929230442669149877)
                    ·
                      refine ⟨2470837587115354000232801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26355600929230442669149877 2470837587115354000232801)
                      ·
                        rfl

theorem cell23_4811939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_4811939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811939 prefixEnd_4811939 := by exact prefixLift 4811939
  have htrace : WordTrace (prefixWord ++ tailWord_4811939) baseStart_4811939 baseEnd_4811939 := by
    simpa [prefixWord, tailWord_4811939, baseEnd_4811939] using wordTrace_append hprefix tailTrace_4811939
  have hstable : (prefixWord ++ tailWord_4811939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811939).length < 2 ^ (prefixWord ++ tailWord_4811939).sum := by decide
  have hdescent : baseEnd_4811939 < baseStart_4811939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4811981 : List Nat := [1, 6, 2, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_4811981 : Nat := 118140960795 + 4811981 * 2 ^ 59
def prefixEnd_4811981 : Nat := 4983230072969 + 3 ^ 40 * 4811981 * 2
def baseEnd_4811981 : Nat := 2470859153302842835907609

theorem tailTrace_4811981 : CollatzResearch.WordTrace tailWord_4811981 prefixEnd_4811981 2470859153302842835907609 := by
  unfold tailWord_4811981
  simp only [CollatzResearch.WordTrace]
  refine ⟨175507365580022132771403797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117004910386681421847602531 175507365580022132771403797)
  ·
    refine ⟨8226907761563537473659553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 175507365580022132771403797 8226907761563537473659553)
    ·
      refine ⟨6170180821172653105244665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8226907761563537473659553 6170180821172653105244665)
      ·
        refine ⟨4627635615879489828933499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6170180821172653105244665 4627635615879489828933499)
        ·
          refine ⟨6941453423819234743400249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4627635615879489828933499 6941453423819234743400249)
          ·
            refine ⟨5206090067864426057550187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6941453423819234743400249 5206090067864426057550187)
            ·
              refine ⟨7809135101796639086325281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5206090067864426057550187 7809135101796639086325281)
              ·
                refine ⟨5856851326347479314743961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7809135101796639086325281 5856851326347479314743961)
                ·
                  refine ⟨4392638494760609486057971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5856851326347479314743961 4392638494760609486057971)
                  ·
                    refine ⟨6588957742140914229086957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4392638494760609486057971 6588957742140914229086957)
                    ·
                      refine ⟨2470859153302842835907609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6588957742140914229086957 2470859153302842835907609)
                      ·
                        rfl

theorem cell23_4811981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_4811981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4811981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4811981 prefixEnd_4811981 := by exact prefixLift 4811981
  have htrace : WordTrace (prefixWord ++ tailWord_4811981) baseStart_4811981 baseEnd_4811981 := by
    simpa [prefixWord, tailWord_4811981, baseEnd_4811981] using wordTrace_append hprefix tailTrace_4811981
  have hstable : (prefixWord ++ tailWord_4811981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4811981).length < 2 ^ (prefixWord ++ tailWord_4811981).sum := by decide
  have hdescent : baseEnd_4811981 < baseStart_4811981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4811981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812026 : List Nat := [3, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4]
def baseStart_4812026 : Nat := 118140960795 + 4812026 * 2 ^ 59
def prefixEnd_4812026 : Nat := 4983230072969 + 3 ^ 40 * 4812026 * 2
def baseEnd_4812026 : Nat := 2470882259932295159844901

theorem tailTrace_4812026 : CollatzResearch.WordTrace tailWord_4812026 prefixEnd_4812026 2470882259932295159844901 := by
  unfold tailWord_4812026
  simp only [CollatzResearch.WordTrace]
  refine ⟨43877251716214776364197983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117006004576572736971194621 43877251716214776364197983)
  ·
    refine ⟨65815877574322164546296975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43877251716214776364197983 65815877574322164546296975)
    ·
      refine ⟨98723816361483246819445463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65815877574322164546296975 98723816361483246819445463)
      ·
        refine ⟨148085724542224870229168195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98723816361483246819445463 148085724542224870229168195)
        ·
          refine ⟨222128586813337305343752293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148085724542224870229168195 222128586813337305343752293)
          ·
            refine ⟨41649110027500744751953555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 222128586813337305343752293 41649110027500744751953555)
            ·
              refine ⟨62473665041251117127930333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41649110027500744751953555 62473665041251117127930333)
              ·
                refine ⟨23427624390469168922973875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62473665041251117127930333 23427624390469168922973875)
                ·
                  refine ⟨35141436585703753384460813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23427624390469168922973875 35141436585703753384460813)
                  ·
                    refine ⟨13178038719638907519172805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35141436585703753384460813 13178038719638907519172805)
                    ·
                      refine ⟨2470882259932295159844901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13178038719638907519172805 2470882259932295159844901)
                      ·
                        rfl

theorem cell23_4812026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_4812026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812026 prefixEnd_4812026 := by exact prefixLift 4812026
  have htrace : WordTrace (prefixWord ++ tailWord_4812026) baseStart_4812026 baseEnd_4812026 := by
    simpa [prefixWord, tailWord_4812026, baseEnd_4812026] using wordTrace_append hprefix tailTrace_4812026
  have hstable : (prefixWord ++ tailWord_4812026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812026).length < 2 ^ (prefixWord ++ tailWord_4812026).sum := by decide
  have hdescent : baseEnd_4812026 < baseStart_4812026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812043 : List Nat := [1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 4]
def baseStart_4812043 : Nat := 118140960795 + 4812043 * 2 ^ 59
def prefixEnd_4812043 : Nat := 4983230072969 + 3 ^ 40 * 4812043 * 2
def baseEnd_4812043 : Nat := 2470890989103421593332323

theorem tailTrace_4812043 : CollatzResearch.WordTrace tailWord_4812043 prefixEnd_4812043 2470890989103421593332323 := by
  unfold tailWord_4812043
  simp only [CollatzResearch.WordTrace]
  refine ⟨175509626905797517360160783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117006417937198344906773855 175509626905797517360160783)
  ·
    refine ⟨263264440358696276040241175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175509626905797517360160783 263264440358696276040241175)
    ·
      refine ⟨394896660538044414060361763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263264440358696276040241175 394896660538044414060361763)
      ·
        refine ⟨592344990807066621090542645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394896660538044414060361763 592344990807066621090542645)
        ·
          refine ⟨55532342888162495727238373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 592344990807066621090542645 55532342888162495727238373)
          ·
            refine ⟨10412314291530467948857195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55532342888162495727238373 10412314291530467948857195)
            ·
              refine ⟨15618471437295701923285793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10412314291530467948857195 15618471437295701923285793)
              ·
                refine ⟨11713853577971776442464345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15618471437295701923285793 11713853577971776442464345)
                ·
                  refine ⟨8785390183478832331848259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11713853577971776442464345 8785390183478832331848259)
                  ·
                    refine ⟨13178085275218248497772389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8785390183478832331848259 13178085275218248497772389)
                    ·
                      refine ⟨2470890989103421593332323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13178085275218248497772389 2470890989103421593332323)
                      ·
                        rfl

theorem cell23_4812043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 4].length) (baseStart_4812043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812043 prefixEnd_4812043 := by exact prefixLift 4812043
  have htrace : WordTrace (prefixWord ++ tailWord_4812043) baseStart_4812043 baseEnd_4812043 := by
    simpa [prefixWord, tailWord_4812043, baseEnd_4812043] using wordTrace_append hprefix tailTrace_4812043
  have hstable : (prefixWord ++ tailWord_4812043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812043).length < 2 ^ (prefixWord ++ tailWord_4812043).sum := by decide
  have hdescent : baseEnd_4812043 < baseStart_4812043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812077 : List Nat := [1, 5, 3, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_4812077 : Nat := 118140960795 + 4812077 * 2 ^ 59
def prefixEnd_4812077 : Nat := 4983230072969 + 3 ^ 40 * 4812077 * 2
def baseEnd_4812077 : Nat := 2470908447445674460307167

theorem tailTrace_4812077 : CollatzResearch.WordTrace tailWord_4812077 prefixEnd_4812077 2470908447445674460307167 := by
  unfold tailWord_4812077
  simp only [CollatzResearch.WordTrace]
  refine ⟨175510866987674341166898485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117007244658449560777932323 175510866987674341166898485)
  ·
    refine ⟨16454143780094469484396733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 175510866987674341166898485 16454143780094469484396733)
    ·
      refine ⟨6170303917535426056648775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16454143780094469484396733 6170303917535426056648775)
      ·
        refine ⟨9255455876303139084973163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6170303917535426056648775 9255455876303139084973163)
        ·
          refine ⟨13883183814454708627459745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9255455876303139084973163 13883183814454708627459745)
          ·
            refine ⟨10412387860841031470594809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13883183814454708627459745 10412387860841031470594809)
            ·
              refine ⟨7809290895630773602946107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10412387860841031470594809 7809290895630773602946107)
              ·
                refine ⟨11713936343446160404419161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7809290895630773602946107 11713936343446160404419161)
                ·
                  refine ⟨8785452257584620303314371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11713936343446160404419161 8785452257584620303314371)
                  ·
                    refine ⟨13178178386376930454971557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8785452257584620303314371 13178178386376930454971557)
                    ·
                      refine ⟨2470908447445674460307167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13178178386376930454971557 2470908447445674460307167)
                      ·
                        rfl

theorem cell23_4812077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_4812077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812077 prefixEnd_4812077 := by exact prefixLift 4812077
  have htrace : WordTrace (prefixWord ++ tailWord_4812077) baseStart_4812077 baseEnd_4812077 := by
    simpa [prefixWord, tailWord_4812077, baseEnd_4812077] using wordTrace_append hprefix tailTrace_4812077
  have hstable : (prefixWord ++ tailWord_4812077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812077).length < 2 ^ (prefixWord ++ tailWord_4812077).sum := by decide
  have hdescent : baseEnd_4812077 < baseStart_4812077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812100 : List Nat := [2, 3, 4, 1, 1, 1, 1, 4, 6]
def baseStart_4812100 : Nat := 118140960795 + 4812100 * 2 ^ 59
def prefixEnd_4812100 : Nat := 4983230072969 + 3 ^ 40 * 4812100 * 2
def baseEnd_4812100 : Nat := 274546695277858652257729

theorem tailTrace_4812100 : CollatzResearch.WordTrace tailWord_4812100 prefixEnd_4812100 274546695277858652257729 := by
  unfold tailWord_4812100
  simp only [CollatzResearch.WordTrace]
  refine ⟨87755852933295508047492877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117007803911060677396657169 87755852933295508047492877)
  ·
    refine ⟨32908444849985815517809829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87755852933295508047492877 32908444849985815517809829)
    ·
      refine ⟨6170333409372340409589343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32908444849985815517809829 6170333409372340409589343)
      ·
        refine ⟨9255500114058510614384015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6170333409372340409589343 9255500114058510614384015)
        ·
          refine ⟨13883250171087765921576023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9255500114058510614384015 13883250171087765921576023)
          ·
            refine ⟨20824875256631648882364035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13883250171087765921576023 20824875256631648882364035)
            ·
              refine ⟨31237312884947473323546053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20824875256631648882364035 31237312884947473323546053)
              ·
                refine ⟨5856996165927651248164885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31237312884947473323546053 5856996165927651248164885)
                ·
                  refine ⟨274546695277858652257729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5856996165927651248164885 274546695277858652257729)
                  ·
                    rfl

theorem cell23_4812100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_4812100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812100 prefixEnd_4812100 := by exact prefixLift 4812100
  have htrace : WordTrace (prefixWord ++ tailWord_4812100) baseStart_4812100 baseEnd_4812100 := by
    simpa [prefixWord, tailWord_4812100, baseEnd_4812100] using wordTrace_append hprefix tailTrace_4812100
  have hstable : (prefixWord ++ tailWord_4812100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812100).length < 2 ^ (prefixWord ++ tailWord_4812100).sum := by decide
  have hdescent : baseEnd_4812100 < baseStart_4812100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812106 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 2, 4, 5]
def baseStart_4812106 : Nat := 118140960795 + 4812106 * 2 ^ 59
def prefixEnd_4812106 : Nat := 4983230072969 + 3 ^ 40 * 4812106 * 2
def baseEnd_4812106 : Nat := 2470923338384654846844533

theorem tailTrace_4812106 : CollatzResearch.WordTrace tailWord_4812106 prefixEnd_4812106 2470923338384654846844533 := by
  unfold tailWord_4812106
  simp only [CollatzResearch.WordTrace]
  refine ⟨43877981176142319779926043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117007949803046186079802781 43877981176142319779926043)
  ·
    refine ⟨65816971764213479669889065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43877981176142319779926043 65816971764213479669889065)
    ·
      refine ⟨49362728823160109752416799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65816971764213479669889065 49362728823160109752416799)
      ·
        refine ⟨74044093234740164628625199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49362728823160109752416799 74044093234740164628625199)
        ·
          refine ⟨111066139852110246942937799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74044093234740164628625199 111066139852110246942937799)
          ·
            refine ⟨166599209778165370414406699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111066139852110246942937799 166599209778165370414406699)
            ·
              refine ⟨249898814667248055621610049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166599209778165370414406699 249898814667248055621610049)
              ·
                refine ⟨187424111000436041716207537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249898814667248055621610049 187424111000436041716207537)
                ·
                  refine ⟨140568083250327031287155653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187424111000436041716207537 140568083250327031287155653)
                  ·
                    refine ⟨26356515609436318366341685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 140568083250327031287155653 26356515609436318366341685)
                    ·
                      refine ⟨2470923338384654846844533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26356515609436318366341685 2470923338384654846844533)
                      ·
                        rfl

theorem cell23_4812106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_4812106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812106 prefixEnd_4812106 := by exact prefixLift 4812106
  have htrace : WordTrace (prefixWord ++ tailWord_4812106) baseStart_4812106 baseEnd_4812106 := by
    simpa [prefixWord, tailWord_4812106, baseEnd_4812106] using wordTrace_append hprefix tailTrace_4812106
  have hstable : (prefixWord ++ tailWord_4812106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812106).length < 2 ^ (prefixWord ++ tailWord_4812106).sum := by decide
  have hdescent : baseEnd_4812106 < baseStart_4812106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812110 : List Nat := [4, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3]
def baseStart_4812110 : Nat := 118140960795 + 4812110 * 2 ^ 59
def prefixEnd_4812110 : Nat := 4983230072969 + 3 ^ 40 * 4812110 * 2
def baseEnd_4812110 : Nat := 2470925392307272831194515

theorem tailTrace_4812110 : CollatzResearch.WordTrace tailWord_4812110 prefixEnd_4812110 2470925392307272831194515 := by
  unfold tailWord_4812110
  simp only [CollatzResearch.WordTrace]
  refine ⟨21939008824569348475356223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117008047064369858535233189 21939008824569348475356223)
  ·
    refine ⟨32908513236854022713034335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21939008824569348475356223 32908513236854022713034335)
    ·
      refine ⟨49362769855281034069551503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32908513236854022713034335 49362769855281034069551503)
      ·
        refine ⟨74044154782921551104327255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49362769855281034069551503 74044154782921551104327255)
        ·
          refine ⟨111066232174382326656490883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74044154782921551104327255 111066232174382326656490883)
          ·
            refine ⟨166599348261573489984736325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111066232174382326656490883 166599348261573489984736325)
            ·
              refine ⟨31237377799045029372138061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 166599348261573489984736325 31237377799045029372138061)
              ·
                refine ⟨11714016674641886014551773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31237377799045029372138061 11714016674641886014551773)
                ·
                  refine ⟨4392756252990707255456915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11714016674641886014551773 4392756252990707255456915)
                  ·
                    refine ⟨6589134379486060883185373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4392756252990707255456915 6589134379486060883185373)
                    ·
                      refine ⟨2470925392307272831194515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6589134379486060883185373 2470925392307272831194515)
                      ·
                        rfl

theorem cell23_4812110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_4812110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812110 prefixEnd_4812110 := by exact prefixLift 4812110
  have htrace : WordTrace (prefixWord ++ tailWord_4812110) baseStart_4812110 baseEnd_4812110 := by
    simpa [prefixWord, tailWord_4812110, baseEnd_4812110] using wordTrace_append hprefix tailTrace_4812110
  have hstable : (prefixWord ++ tailWord_4812110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812110).length < 2 ^ (prefixWord ++ tailWord_4812110).sum := by decide
  have hdescent : baseEnd_4812110 < baseStart_4812110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812130 : List Nat := [3, 3, 2, 1, 1, 1, 2, 4, 1, 5]
def baseStart_4812130 : Nat := 118140960795 + 4812130 * 2 ^ 59
def prefixEnd_4812130 : Nat := 4983230072969 + 3 ^ 40 * 4812130 * 2
def baseEnd_4812130 : Nat := 823645220640120917648141

theorem tailTrace_4812130 : CollatzResearch.WordTrace tailWord_4812130 prefixEnd_4812130 823645220640120917648141 := by
  unfold tailWord_4812130
  simp only [CollatzResearch.WordTrace]
  refine ⟨43878200014120582804644461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117008533370988220812385229 43878200014120582804644461)
  ·
    refine ⟨16454325005295218551741673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43878200014120582804644461 16454325005295218551741673)
    ·
      refine ⟨12340743753971413913806255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16454325005295218551741673 12340743753971413913806255)
      ·
        refine ⟨18511115630957120870709383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12340743753971413913806255 18511115630957120870709383)
        ·
          refine ⟨27766673446435681306064075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18511115630957120870709383 27766673446435681306064075)
          ·
            refine ⟨41650010169653521959096113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27766673446435681306064075 41650010169653521959096113)
            ·
              refine ⟨31237507627240141469322085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41650010169653521959096113 31237507627240141469322085)
              ·
                refine ⟨5857032680107526525497891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31237507627240141469322085 5857032680107526525497891)
                ·
                  refine ⟨8785549020161289788246837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5857032680107526525497891 8785549020161289788246837)
                  ·
                    refine ⟨823645220640120917648141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8785549020161289788246837 823645220640120917648141)
                    ·
                      rfl

theorem cell23_4812130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_4812130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812130 prefixEnd_4812130 := by exact prefixLift 4812130
  have htrace : WordTrace (prefixWord ++ tailWord_4812130) baseStart_4812130 baseEnd_4812130 := by
    simpa [prefixWord, tailWord_4812130, baseEnd_4812130] using wordTrace_append hprefix tailTrace_4812130
  have hstable : (prefixWord ++ tailWord_4812130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812130).length < 2 ^ (prefixWord ++ tailWord_4812130).sum := by decide
  have hdescent : baseEnd_4812130 < baseStart_4812130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812133 : List Nat := [1, 3, 1, 3, 1, 2, 1, 3, 3, 1, 4]
def baseStart_4812133 : Nat := 118140960795 + 4812133 * 2 ^ 59
def prefixEnd_4812133 : Nat := 4983230072969 + 3 ^ 40 * 4812133 * 2
def baseEnd_4812133 : Nat := 2470937202362326241206909

theorem tailTrace_4812133 : CollatzResearch.WordTrace tailWord_4812133 prefixEnd_4812133 2470937202362326241206909 := by
  unfold tailWord_4812133
  simp only [CollatzResearch.WordTrace]
  refine ⟨175512909475471462730937053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117008606316980975153958035 175512909475471462730937053)
  ·
    refine ⟨65817341053301798524101395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175512909475471462730937053 65817341053301798524101395)
    ·
      refine ⟨98726011579952697786152093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65817341053301798524101395 98726011579952697786152093)
      ·
        refine ⟨37022254342482261669807035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98726011579952697786152093 37022254342482261669807035)
        ·
          refine ⟨55533381513723392504710553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37022254342482261669807035 55533381513723392504710553)
          ·
            refine ⟨41650036135292544378532915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55533381513723392504710553 41650036135292544378532915)
            ·
              refine ⟨62475054202938816567799373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41650036135292544378532915 62475054202938816567799373)
              ·
                refine ⟨23428145326102056212924765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62475054202938816567799373 23428145326102056212924765)
                ·
                  refine ⟨8785554497288271079846787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23428145326102056212924765 8785554497288271079846787)
                  ·
                    refine ⟨13178331745932406619770181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8785554497288271079846787 13178331745932406619770181)
                    ·
                      refine ⟨2470937202362326241206909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13178331745932406619770181 2470937202362326241206909)
                      ·
                        rfl

theorem cell23_4812133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_4812133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812133 prefixEnd_4812133 := by exact prefixLift 4812133
  have htrace : WordTrace (prefixWord ++ tailWord_4812133) baseStart_4812133 baseEnd_4812133 := by
    simpa [prefixWord, tailWord_4812133, baseEnd_4812133] using wordTrace_append hprefix tailTrace_4812133
  have hstable : (prefixWord ++ tailWord_4812133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812133).length < 2 ^ (prefixWord ++ tailWord_4812133).sum := by decide
  have hdescent : baseEnd_4812133 < baseStart_4812133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812143 : List Nat := [1, 1, 2, 1, 3, 1, 4, 2, 4, 4]
def baseStart_4812143 : Nat := 118140960795 + 4812143 * 2 ^ 59
def prefixEnd_4812143 : Nat := 4983230072969 + 3 ^ 40 * 4812143 * 2
def baseEnd_4812143 : Nat := 823647445722957067360621

theorem tailTrace_4812143 : CollatzResearch.WordTrace tailWord_4812143 prefixEnd_4812143 823647445722957067360621 := by
  unfold tailWord_4812143
  simp only [CollatzResearch.WordTrace]
  refine ⟨175513274205435234438801083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117008849470290156292534055 175513274205435234438801083)
  ·
    refine ⟨263269911308152851658201625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175513274205435234438801083 263269911308152851658201625)
    ·
      refine ⟨197452433481114638743651219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263269911308152851658201625 197452433481114638743651219)
      ·
        refine ⟨296178650221671958115476829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197452433481114638743651219 296178650221671958115476829)
        ·
          refine ⟨111066993833126984293303811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 296178650221671958115476829 111066993833126984293303811)
          ·
            refine ⟨166600490749690476439955717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111066993833126984293303811 166600490749690476439955717)
            ·
              refine ⟨31237592015566964332491697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 166600490749690476439955717 31237592015566964332491697)
              ·
                refine ⟨23428194011675223249368773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31237592015566964332491697 23428194011675223249368773)
                ·
                  refine ⟨4392786377189104359256645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23428194011675223249368773 4392786377189104359256645)
                  ·
                    refine ⟨823647445722957067360621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4392786377189104359256645 823647445722957067360621)
                    ·
                      rfl

theorem cell23_4812143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 4].length) (baseStart_4812143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812143 prefixEnd_4812143 := by exact prefixLift 4812143
  have htrace : WordTrace (prefixWord ++ tailWord_4812143) baseStart_4812143 baseEnd_4812143 := by
    simpa [prefixWord, tailWord_4812143, baseEnd_4812143] using wordTrace_append hprefix tailTrace_4812143
  have hstable : (prefixWord ++ tailWord_4812143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812143).length < 2 ^ (prefixWord ++ tailWord_4812143).sum := by decide
  have hdescent : baseEnd_4812143 < baseStart_4812143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812156 : List Nat := [2, 2, 2, 1, 1, 1, 14]
def baseStart_4812156 : Nat := 118140960795 + 4812156 * 2 ^ 59
def prefixEnd_4812156 : Nat := 4983230072969 + 3 ^ 40 * 4812156 * 2
def baseEnd_4812156 : Nat := 30505543363177526558263

theorem tailTrace_4812156 : CollatzResearch.WordTrace tailWord_4812156 prefixEnd_4812156 30505543363177526558263 := by
  unfold tailWord_4812156
  simp only [CollatzResearch.WordTrace]
  refine ⟨87756874177194068829512161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117009165569592091772682881 87756874177194068829512161)
  ·
    refine ⟨65817655632895551622134121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87756874177194068829512161 65817655632895551622134121)
    ·
      refine ⟨49363241724671663716600591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65817655632895551622134121 49363241724671663716600591)
      ·
        refine ⟨74044862587007495574900887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49363241724671663716600591 74044862587007495574900887)
        ·
          refine ⟨111067293880511243362351331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74044862587007495574900887 111067293880511243362351331)
          ·
            refine ⟨166600940820766865043526997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111067293880511243362351331 166600940820766865043526997)
            ·
              refine ⟨30505543363177526558263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 166600940820766865043526997 30505543363177526558263)
              ·
                rfl

theorem cell23_4812156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 14].length) (baseStart_4812156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812156 prefixEnd_4812156 := by exact prefixLift 4812156
  have htrace : WordTrace (prefixWord ++ tailWord_4812156) baseStart_4812156 baseEnd_4812156 := by
    simpa [prefixWord, tailWord_4812156, baseEnd_4812156] using wordTrace_append hprefix tailTrace_4812156
  have hstable : (prefixWord ++ tailWord_4812156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812156).length < 2 ^ (prefixWord ++ tailWord_4812156).sum := by decide
  have hdescent : baseEnd_4812156 < baseStart_4812156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812167 : List Nat := [1, 1, 4, 2, 2, 2, 1, 3, 3, 2, 2]
def baseStart_4812167 : Nat := 118140960795 + 4812167 * 2 ^ 59
def prefixEnd_4812167 : Nat := 4983230072969 + 3 ^ 40 * 4812167 * 2
def baseEnd_4812167 : Nat := 2470954660704579108181753

theorem tailTrace_4812167 : CollatzResearch.WordTrace tailWord_4812167 prefixEnd_4812167 2470954660704579108181753 := by
  unfold tailWord_4812167
  simp only [CollatzResearch.WordTrace]
  refine ⟨175514149557348286537674755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117009433038232191025116503 175514149557348286537674755)
  ·
    refine ⟨263271224336022429806512133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175514149557348286537674755 263271224336022429806512133)
    ·
      refine ⟨49363354563004205588721025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 263271224336022429806512133 49363354563004205588721025)
      ·
        refine ⟨37022515922253154191540769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49363354563004205588721025 37022515922253154191540769)
        ·
          refine ⟨27766886941689865643655577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37022515922253154191540769 27766886941689865643655577)
          ·
            refine ⟨20825165206267399232741683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27766886941689865643655577 20825165206267399232741683)
            ·
              refine ⟨31237747809401098849112525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20825165206267399232741683 31237747809401098849112525)
              ·
                refine ⟨11714155428525412068417197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31237747809401098849112525 11714155428525412068417197)
                ·
                  refine ⟨4392808285697029525656449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11714155428525412068417197 4392808285697029525656449)
                  ·
                    refine ⟨3294606214272772144242337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4392808285697029525656449 3294606214272772144242337)
                    ·
                      refine ⟨2470954660704579108181753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3294606214272772144242337 2470954660704579108181753)
                      ·
                        rfl

theorem cell23_4812167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_4812167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812167 prefixEnd_4812167 := by exact prefixLift 4812167
  have htrace : WordTrace (prefixWord ++ tailWord_4812167) baseStart_4812167 baseEnd_4812167 := by
    simpa [prefixWord, tailWord_4812167, baseEnd_4812167] using wordTrace_append hprefix tailTrace_4812167
  have hstable : (prefixWord ++ tailWord_4812167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812167).length < 2 ^ (prefixWord ++ tailWord_4812167).sum := by decide
  have hdescent : baseEnd_4812167 < baseStart_4812167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812180 : List Nat := [2, 4, 2, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_4812180 : Nat := 118140960795 + 4812180 * 2 ^ 59
def prefixEnd_4812180 : Nat := 4983230072969 + 3 ^ 40 * 4812180 * 2
def baseEnd_4812180 : Nat := 2470961335953087557319193

theorem tailTrace_4812180 : CollatzResearch.WordTrace tailWord_4812180 prefixEnd_4812180 2470961335953087557319193 := by
  unfold tailWord_4812180
  simp only [CollatzResearch.WordTrace]
  refine ⟨87757311853150594878948997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117009749137534126505265329 87757311853150594878948997)
  ·
    refine ⟨16454495972465736539802937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87757311853150594878948997 16454495972465736539802937)
    ·
      refine ⟨12340871979349302404852203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16454495972465736539802937 12340871979349302404852203)
      ·
        refine ⟨18511307969023953607278305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12340871979349302404852203 18511307969023953607278305)
        ·
          refine ⟨13883480976767965205458729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18511307969023953607278305 13883480976767965205458729)
          ·
            refine ⟨10412610732575973904094047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13883480976767965205458729 10412610732575973904094047)
            ·
              refine ⟨15618916098863960856141071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10412610732575973904094047 15618916098863960856141071)
              ·
                refine ⟨23428374148295941284211607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15618916098863960856141071 23428374148295941284211607)
                ·
                  refine ⟨35142561222443911926317411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23428374148295941284211607 35142561222443911926317411)
                  ·
                    refine ⟨52713841833665867889476117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35142561222443911926317411 52713841833665867889476117)
                    ·
                      refine ⟨2470961335953087557319193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52713841833665867889476117 2470961335953087557319193)
                      ·
                        rfl

theorem cell23_4812180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_4812180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812180 prefixEnd_4812180 := by exact prefixLift 4812180
  have htrace : WordTrace (prefixWord ++ tailWord_4812180) baseStart_4812180 baseEnd_4812180 := by
    simpa [prefixWord, tailWord_4812180, baseEnd_4812180] using wordTrace_append hprefix tailTrace_4812180
  have hstable : (prefixWord ++ tailWord_4812180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812180).length < 2 ^ (prefixWord ++ tailWord_4812180).sum := by decide
  have hdescent : baseEnd_4812180 < baseStart_4812180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812234 : List Nat := [3, 1, 2, 1, 2, 3, 4, 1, 2, 1, 3]
def baseStart_4812234 : Nat := 118140960795 + 4812234 * 2 ^ 59
def prefixEnd_4812234 : Nat := 4983230072969 + 3 ^ 40 * 4812234 * 2
def baseEnd_4812234 : Nat := 2470989063908430346043945

theorem tailTrace_4812234 : CollatzResearch.WordTrace tailWord_4812234 prefixEnd_4812234 2470989063908430346043945 := by
  unfold tailWord_4812234
  simp only [CollatzResearch.WordTrace]
  refine ⟨43879148312026389245090939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117011062165403704653575837 43879148312026389245090939)
  ·
    refine ⟨65818722468039583867636409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43879148312026389245090939 65818722468039583867636409)
    ·
      refine ⟨49364041851029687900727307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65818722468039583867636409 49364041851029687900727307)
      ·
        refine ⟨74046062776544531851090961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49364041851029687900727307 74046062776544531851090961)
        ·
          refine ⟨55534547082408398888318221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74046062776544531851090961 55534547082408398888318221)
          ·
            refine ⟨20825455155903149583119333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55534547082408398888318221 20825455155903149583119333)
            ·
              refine ⟨3904772841731840546834875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20825455155903149583119333 3904772841731840546834875)
              ·
                refine ⟨5857159262597760820252313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3904772841731840546834875 5857159262597760820252313)
                ·
                  refine ⟨4392869446948320615189235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5857159262597760820252313 4392869446948320615189235)
                  ·
                    refine ⟨6589304170422480922783853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4392869446948320615189235 6589304170422480922783853)
                    ·
                      refine ⟨2470989063908430346043945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6589304170422480922783853 2470989063908430346043945)
                      ·
                        rfl

theorem cell23_4812234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 2, 1, 3].length) (baseStart_4812234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812234 prefixEnd_4812234 := by exact prefixLift 4812234
  have htrace : WordTrace (prefixWord ++ tailWord_4812234) baseStart_4812234 baseEnd_4812234 := by
    simpa [prefixWord, tailWord_4812234, baseEnd_4812234] using wordTrace_append hprefix tailTrace_4812234
  have hstable : (prefixWord ++ tailWord_4812234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812234).length < 2 ^ (prefixWord ++ tailWord_4812234).sum := by decide
  have hdescent : baseEnd_4812234 < baseStart_4812234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812244 : List Nat := [2, 4, 1, 2, 3, 1, 1, 1, 3, 3, 2]
def baseStart_4812244 : Nat := 118140960795 + 4812244 * 2 ^ 59
def prefixEnd_4812244 : Nat := 4983230072969 + 3 ^ 40 * 4812244 * 2
def baseEnd_4812244 : Nat := 2470994198714975306918899

theorem tailTrace_4812244 : CollatzResearch.WordTrace tailWord_4812244 prefixEnd_4812244 2470994198714975306918899 := by
  unfold tailWord_4812244
  simp only [CollatzResearch.WordTrace]
  refine ⟨87758478989034664344113893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117011305318712885792151857 87758478989034664344113893)
  ·
    refine ⟨16454714810443999564521355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87758478989034664344113893 16454714810443999564521355)
    ·
      refine ⟨24682072215665999346782033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16454714810443999564521355 24682072215665999346782033)
      ·
        refine ⟨18511554161749499510086525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24682072215665999346782033 18511554161749499510086525)
        ·
          refine ⟨6941832810656062316282447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18511554161749499510086525 6941832810656062316282447)
          ·
            refine ⟨10412749215984093474423671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6941832810656062316282447 10412749215984093474423671)
            ·
              refine ⟨15619123823976140211635507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10412749215984093474423671 15619123823976140211635507)
              ·
                refine ⟨23428685735964210317453261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15619123823976140211635507 23428685735964210317453261)
                ·
                  refine ⟨8785757150986578869044973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23428685735964210317453261 8785757150986578869044973)
                  ·
                    refine ⟨3294658931619967075891865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8785757150986578869044973 3294658931619967075891865)
                    ·
                      refine ⟨2470994198714975306918899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3294658931619967075891865 2470994198714975306918899)
                      ·
                        rfl

theorem cell23_4812244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_4812244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812244 prefixEnd_4812244 := by exact prefixLift 4812244
  have htrace : WordTrace (prefixWord ++ tailWord_4812244) baseStart_4812244 baseEnd_4812244 := by
    simpa [prefixWord, tailWord_4812244, baseEnd_4812244] using wordTrace_append hprefix tailTrace_4812244
  have hstable : (prefixWord ++ tailWord_4812244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812244).length < 2 ^ (prefixWord ++ tailWord_4812244).sum := by decide
  have hdescent : baseEnd_4812244 < baseStart_4812244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812257 : List Nat := [1, 2, 3, 1, 2, 4, 1, 2, 1, 4, 2]
def baseStart_4812257 : Nat := 118140960795 + 4812257 * 2 ^ 59
def prefixEnd_4812257 : Nat := 4983230072969 + 3 ^ 40 * 4812257 * 2
def baseEnd_4812257 : Nat := 2471000873963483756056339

theorem tailTrace_4812257 : CollatzResearch.WordTrace tailWord_4812257 prefixEnd_4812257 2471000873963483756056339 := by
  unfold tailWord_4812257
  simp only [CollatzResearch.WordTrace]
  refine ⟨175517432127022231908451025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117011621418014821272300683 175517432127022231908451025)
  ·
    refine ⟨131638074095266673931338269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175517432127022231908451025 131638074095266673931338269)
    ·
      refine ⟨49364277785725002724251851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131638074095266673931338269 49364277785725002724251851)
      ·
        refine ⟨74046416678587504086377777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49364277785725002724251851 74046416678587504086377777)
        ·
          refine ⟨55534812508940628064783333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74046416678587504086377777 55534812508940628064783333)
          ·
            refine ⟨10412777345426367762146875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55534812508940628064783333 10412777345426367762146875)
            ·
              refine ⟨15619166018139551643220313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10412777345426367762146875 15619166018139551643220313)
              ·
                refine ⟨11714374513604663732415235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15619166018139551643220313 11714374513604663732415235)
                ·
                  refine ⟨17571561770406995598622853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11714374513604663732415235 17571561770406995598622853)
                  ·
                    refine ⟨3294667831951311674741785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17571561770406995598622853 3294667831951311674741785)
                    ·
                      refine ⟨2471000873963483756056339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3294667831951311674741785 2471000873963483756056339)
                      ·
                        rfl

theorem cell23_4812257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 4, 2].length) (baseStart_4812257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812257 prefixEnd_4812257 := by exact prefixLift 4812257
  have htrace : WordTrace (prefixWord ++ tailWord_4812257) baseStart_4812257 baseEnd_4812257 := by
    simpa [prefixWord, tailWord_4812257, baseEnd_4812257] using wordTrace_append hprefix tailTrace_4812257
  have hstable : (prefixWord ++ tailWord_4812257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812257).length < 2 ^ (prefixWord ++ tailWord_4812257).sum := by decide
  have hdescent : baseEnd_4812257 < baseStart_4812257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812261 : List Nat := [1, 3, 1, 5, 1, 2, 3, 1, 1, 3, 2]
def baseStart_4812261 : Nat := 118140960795 + 4812261 * 2 ^ 59
def prefixEnd_4812261 : Nat := 4983230072969 + 3 ^ 40 * 4812261 * 2
def baseEnd_4812261 : Nat := 2471002927886101740406321

theorem tailTrace_4812261 : CollatzResearch.WordTrace tailWord_4812261 prefixEnd_4812261 2471002927886101740406321 := by
  unfold tailWord_4812261
  simp only [CollatzResearch.WordTrace]
  refine ⟨175517578019007740591596637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117011718679338493727731091 175517578019007740591596637)
  ·
    refine ⟨65819091757127902721848739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175517578019007740591596637 65819091757127902721848739)
    ·
      refine ⟨98728637635691854082773109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65819091757127902721848739 98728637635691854082773109)
      ·
        refine ⟨9255809778346111320259979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98728637635691854082773109 9255809778346111320259979)
        ·
          refine ⟨13883714667519166980389969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9255809778346111320259979 13883714667519166980389969)
          ·
            refine ⟨10412786000639375235292477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13883714667519166980389969 10412786000639375235292477)
            ·
              refine ⟨3904794750239765713234679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10412786000639375235292477 3904794750239765713234679)
              ·
                refine ⟨5857192125359648569852019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3904794750239765713234679 5857192125359648569852019)
                ·
                  refine ⟨8785788188039472854778029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5857192125359648569852019 8785788188039472854778029)
                  ·
                    refine ⟨3294670570514802320541761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8785788188039472854778029 3294670570514802320541761)
                    ·
                      refine ⟨2471002927886101740406321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3294670570514802320541761 2471002927886101740406321)
                      ·
                        rfl

theorem cell23_4812261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_4812261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812261 prefixEnd_4812261 := by exact prefixLift 4812261
  have htrace : WordTrace (prefixWord ++ tailWord_4812261) baseStart_4812261 baseEnd_4812261 := by
    simpa [prefixWord, tailWord_4812261, baseEnd_4812261] using wordTrace_append hprefix tailTrace_4812261
  have hstable : (prefixWord ++ tailWord_4812261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812261).length < 2 ^ (prefixWord ++ tailWord_4812261).sum := by decide
  have hdescent : baseEnd_4812261 < baseStart_4812261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812270 : List Nat := [4, 1, 2, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_4812270 : Nat := 118140960795 + 4812270 * 2 ^ 59
def prefixEnd_4812270 : Nat := 4983230072969 + 3 ^ 40 * 4812270 * 2
def baseEnd_4812270 : Nat := 2471007549211992205193779

theorem tailTrace_4812270 : CollatzResearch.WordTrace tailWord_4812270 prefixEnd_4812270 2471007549211992205193779 := by
  unfold tailWord_4812270
  simp only [CollatzResearch.WordTrace]
  refine ⟨21939738284496891891084283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117011937517316756752449509 21939738284496891891084283)
  ·
    refine ⟨32909607426745337836626425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21939738284496891891084283 32909607426745337836626425)
    ·
      refine ⟨24682205570059003377469819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32909607426745337836626425 24682205570059003377469819)
      ·
        refine ⟨37023308355088505066204729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24682205570059003377469819 37023308355088505066204729)
        ·
          refine ⟨27767481266316378799653547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37023308355088505066204729 27767481266316378799653547)
          ·
            refine ⟨41651221899474568199480321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27767481266316378799653547 41651221899474568199480321)
            ·
              refine ⟨31238416424605926149610241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41651221899474568199480321 31238416424605926149610241)
              ·
                refine ⟨23428812318454444612207681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31238416424605926149610241 23428812318454444612207681)
                ·
                  refine ⟨17571609238840833459155761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23428812318454444612207681 17571609238840833459155761)
                  ·
                    refine ⟨13178706929130625094366821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17571609238840833459155761 13178706929130625094366821)
                    ·
                      refine ⟨2471007549211992205193779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13178706929130625094366821 2471007549211992205193779)
                      ·
                        rfl

theorem cell23_4812270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_4812270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812270 prefixEnd_4812270 := by exact prefixLift 4812270
  have htrace : WordTrace (prefixWord ++ tailWord_4812270) baseStart_4812270 baseEnd_4812270 := by
    simpa [prefixWord, tailWord_4812270, baseEnd_4812270] using wordTrace_append hprefix tailTrace_4812270
  have hstable : (prefixWord ++ tailWord_4812270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812270).length < 2 ^ (prefixWord ++ tailWord_4812270).sum := by decide
  have hdescent : baseEnd_4812270 < baseStart_4812270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812277 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_4812277 : Nat := 118140960795 + 4812277 * 2 ^ 59
def prefixEnd_4812277 : Nat := 4983230072969 + 3 ^ 40 * 4812277 * 2
def baseEnd_4812277 : Nat := 2471011143576573677806247

theorem tailTrace_4812277 : CollatzResearch.WordTrace tailWord_4812277 prefixEnd_4812277 2471011143576573677806247 := by
  unfold tailWord_4812277
  simp only [CollatzResearch.WordTrace]
  refine ⟨175518161586949775324179085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117012107724633183549452723 175518161586949775324179085)
  ·
    refine ⟨65819310595106165746567157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175518161586949775324179085 65819310595106165746567157)
    ·
      refine ⟨6170560368291203038740671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65819310595106165746567157 6170560368291203038740671)
      ·
        refine ⟨9255840552436804558111007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6170560368291203038740671 9255840552436804558111007)
        ·
          refine ⟨13883760828655206837166511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9255840552436804558111007 13883760828655206837166511)
          ·
            refine ⟨20825641242982810255749767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13883760828655206837166511 20825641242982810255749767)
            ·
              refine ⟨31238461864474215383624651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20825641242982810255749767 31238461864474215383624651)
              ·
                refine ⟨46857692796711323075436977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31238461864474215383624651 46857692796711323075436977)
                ·
                  refine ⟨35143269597533492306577733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46857692796711323075436977 35143269597533492306577733)
                  ·
                    refine ⟨6589363049537529807483325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35143269597533492306577733 6589363049537529807483325)
                    ·
                      refine ⟨2471011143576573677806247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6589363049537529807483325 2471011143576573677806247)
                      ·
                        rfl

theorem cell23_4812277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_4812277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812277 prefixEnd_4812277 := by exact prefixLift 4812277
  have htrace : WordTrace (prefixWord ++ tailWord_4812277) baseStart_4812277 baseEnd_4812277 := by
    simpa [prefixWord, tailWord_4812277, baseEnd_4812277] using wordTrace_append hprefix tailTrace_4812277
  have hstable : (prefixWord ++ tailWord_4812277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812277).length < 2 ^ (prefixWord ++ tailWord_4812277).sum := by decide
  have hdescent : baseEnd_4812277 < baseStart_4812277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812293 : List Nat := [1, 3, 1, 1, 2, 2, 1, 4, 1, 7]
def baseStart_4812293 : Nat := 118140960795 + 4812293 * 2 ^ 59
def prefixEnd_4812293 : Nat := 4983230072969 + 3 ^ 40 * 4812293 * 2
def baseEnd_4812293 : Nat := 823673119755681871735391

theorem tailTrace_4812293 : CollatzResearch.WordTrace tailWord_4812293 prefixEnd_4812293 823673119755681871735391 := by
  unfold tailWord_4812293
  simp only [CollatzResearch.WordTrace]
  refine ⟨175518745154891810056761533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117012496769927873371174355 175518745154891810056761533)
  ·
    refine ⟨65819529433084428771285575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175518745154891810056761533 65819529433084428771285575)
    ·
      refine ⟨98729294149626643156928363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65819529433084428771285575 98729294149626643156928363)
      ·
        refine ⟨148093941224439964735392545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98729294149626643156928363 148093941224439964735392545)
        ·
          refine ⟨111070455918329973551544409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148093941224439964735392545 111070455918329973551544409)
          ·
            refine ⟨83302841938747480163658307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111070455918329973551544409 83302841938747480163658307)
            ·
              refine ⟨124954262908121220245487461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83302841938747480163658307 124954262908121220245487461)
              ·
                refine ⟨23428924295272728796028899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124954262908121220245487461 23428924295272728796028899)
                ·
                  refine ⟨35143386442909093194043349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23428924295272728796028899 35143386442909093194043349)
                  ·
                    refine ⟨823673119755681871735391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35143386442909093194043349 823673119755681871735391)
                    ·
                      rfl

theorem cell23_4812293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_4812293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812293 prefixEnd_4812293 := by exact prefixLift 4812293
  have htrace : WordTrace (prefixWord ++ tailWord_4812293) baseStart_4812293 baseEnd_4812293 := by
    simpa [prefixWord, tailWord_4812293, baseEnd_4812293] using wordTrace_append hprefix tailTrace_4812293
  have hstable : (prefixWord ++ tailWord_4812293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812293).length < 2 ^ (prefixWord ++ tailWord_4812293).sum := by decide
  have hdescent : baseEnd_4812293 < baseStart_4812293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812370 : List Nat := [3, 2, 2, 1, 2, 2, 1, 2, 8]
def baseStart_4812370 : Nat := 118140960795 + 4812370 * 2 ^ 59
def prefixEnd_4812370 : Nat := 4983230072969 + 3 ^ 40 * 4812370 * 2
def baseEnd_4812370 : Nat := 274562099697493534882591

theorem tailTrace_4812370 : CollatzResearch.WordTrace tailWord_4812370 prefixEnd_4812370 274562099697493534882591 := by
  unfold tailWord_4812370
  simp only [CollatzResearch.WordTrace]
  refine ⟨43880388393903213051828641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117014369050408568138209709 43880388393903213051828641)
  ·
    refine ⟨32910291295427409788871481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43880388393903213051828641 32910291295427409788871481)
    ·
      refine ⟨24682718471570557341653611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32910291295427409788871481 24682718471570557341653611)
      ·
        refine ⟨37024077707355836012480417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24682718471570557341653611 37024077707355836012480417)
        ·
          refine ⟨27768058280516877009360313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37024077707355836012480417 27768058280516877009360313)
          ·
            refine ⟨20826043710387657757020235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27768058280516877009360313 20826043710387657757020235)
            ·
              refine ⟨31239065565581486635530353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20826043710387657757020235 31239065565581486635530353)
              ·
                refine ⟨23429299174186114976647765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31239065565581486635530353 23429299174186114976647765)
                ·
                  refine ⟨274562099697493534882591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23429299174186114976647765 274562099697493534882591)
                  ·
                    rfl

theorem cell23_4812370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_4812370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812370 prefixEnd_4812370 := by exact prefixLift 4812370
  have htrace : WordTrace (prefixWord ++ tailWord_4812370) baseStart_4812370 baseEnd_4812370 := by
    simpa [prefixWord, tailWord_4812370, baseEnd_4812370] using wordTrace_append hprefix tailTrace_4812370
  have hstable : (prefixWord ++ tailWord_4812370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812370).length < 2 ^ (prefixWord ++ tailWord_4812370).sum := by decide
  have hdescent : baseEnd_4812370 < baseStart_4812370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812381 : List Nat := [1, 4, 4, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_4812381 : Nat := 118140960795 + 4812381 * 2 ^ 59
def prefixEnd_4812381 : Nat := 4983230072969 + 3 ^ 40 * 4812381 * 2
def baseEnd_4812381 : Nat := 2471064545564641270905769

theorem tailTrace_4812381 : CollatzResearch.WordTrace tailWord_4812381 prefixEnd_4812381 2471064545564641270905769 := by
  unfold tailWord_4812381
  simp only [CollatzResearch.WordTrace]
  refine ⟨175521954778573001085964997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117014636519048667390643331 175521954778573001085964997)
  ·
    refine ⟨32910366520982437703618437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175521954778573001085964997 32910366520982437703618437)
    ·
      refine ⟨6170693722684207069428457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32910366520982437703618437 6170693722684207069428457)
      ·
        refine ⟨4628020292013155302071343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6170693722684207069428457 4628020292013155302071343)
        ·
          refine ⟨6942030438019732953107015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4628020292013155302071343 6942030438019732953107015)
          ·
            refine ⟨10413045657029599429660523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6942030438019732953107015 10413045657029599429660523)
            ·
              refine ⟨15619568485544399144490785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10413045657029599429660523 15619568485544399144490785)
              ·
                refine ⟨11714676364158299358368089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15619568485544399144490785 11714676364158299358368089)
                ·
                  refine ⟨8786007273118724518776067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11714676364158299358368089 8786007273118724518776067)
                  ·
                    refine ⟨13179010909678086778164101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8786007273118724518776067 13179010909678086778164101)
                    ·
                      refine ⟨2471064545564641270905769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13179010909678086778164101 2471064545564641270905769)
                      ·
                        rfl

theorem cell23_4812381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_4812381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812381 prefixEnd_4812381 := by exact prefixLift 4812381
  have htrace : WordTrace (prefixWord ++ tailWord_4812381) baseStart_4812381 baseEnd_4812381 := by
    simpa [prefixWord, tailWord_4812381, baseEnd_4812381] using wordTrace_append hprefix tailTrace_4812381
  have hstable : (prefixWord ++ tailWord_4812381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812381).length < 2 ^ (prefixWord ++ tailWord_4812381).sum := by decide
  have hdescent : baseEnd_4812381 < baseStart_4812381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812407 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 6, 3, 2]
def baseStart_4812407 : Nat := 118140960795 + 4812407 * 2 ^ 59
def prefixEnd_4812407 : Nat := 4983230072969 + 3 ^ 40 * 4812407 * 2
def baseEnd_4812407 : Nat := 2471077896061658169180649

theorem tailTrace_4812407 : CollatzResearch.WordTrace tailWord_4812407 prefixEnd_4812407 2471077896061658169180649 := by
  unfold tailWord_4812407
  simp only [CollatzResearch.WordTrace]
  refine ⟨175522903076478807526411475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117015268717652538350940983 175522903076478807526411475)
  ·
    refine ⟨263284354614718211289617213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175522903076478807526411475 263284354614718211289617213)
    ·
      refine ⟨98731632980519329233606455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263284354614718211289617213 98731632980519329233606455)
      ·
        refine ⟨148097449470778993850409683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98731632980519329233606455 148097449470778993850409683)
        ·
          refine ⟨222146174206168490775614525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148097449470778993850409683 222146174206168490775614525)
          ·
            refine ⟨83304815327313184040855447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222146174206168490775614525 83304815327313184040855447)
            ·
              refine ⟨124957222990969776061283171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83304815327313184040855447 124957222990969776061283171)
              ·
                refine ⟨187435834486454664091924757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124957222990969776061283171 187435834486454664091924757)
                ·
                  refine ⟨8786054741552562379308973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 187435834486454664091924757 8786054741552562379308973)
                  ·
                    refine ⟨3294770528082210892240865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8786054741552562379308973 3294770528082210892240865)
                    ·
                      refine ⟨2471077896061658169180649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3294770528082210892240865 2471077896061658169180649)
                      ·
                        rfl

theorem cell23_4812407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 3, 2].length) (baseStart_4812407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812407 prefixEnd_4812407 := by exact prefixLift 4812407
  have htrace : WordTrace (prefixWord ++ tailWord_4812407) baseStart_4812407 baseEnd_4812407 := by
    simpa [prefixWord, tailWord_4812407, baseEnd_4812407] using wordTrace_append hprefix tailTrace_4812407
  have hstable : (prefixWord ++ tailWord_4812407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812407).length < 2 ^ (prefixWord ++ tailWord_4812407).sum := by decide
  have hdescent : baseEnd_4812407 < baseStart_4812407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812417 : List Nat := [1, 2, 4, 2, 1, 3, 1, 1, 3, 5]
def baseStart_4812417 : Nat := 118140960795 + 4812417 * 2 ^ 59
def prefixEnd_4812417 : Nat := 4983230072969 + 3 ^ 40 * 4812417 * 2
def baseEnd_4812417 : Nat := 823694343622734376685201

theorem tailTrace_4812417 : CollatzResearch.WordTrace tailWord_4812417 prefixEnd_4812417 823694343622734376685201 := by
  unfold tailWord_4812417
  simp only [CollatzResearch.WordTrace]
  refine ⟨175523267806442579234275505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117015511870961719489517003 175523267806442579234275505)
  ·
    refine ⟨131642450854831934425706629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175523267806442579234275505 131642450854831934425706629)
    ·
      refine ⟨24682959535280987704819993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131642450854831934425706629 24682959535280987704819993)
      ·
        refine ⟨18512219651460740778614995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24682959535280987704819993 18512219651460740778614995)
        ·
          refine ⟨27768329477191111167922493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18512219651460740778614995 27768329477191111167922493)
          ·
            refine ⟨10413123553946666687970935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27768329477191111167922493 10413123553946666687970935)
            ·
              refine ⟨15619685330920000031956403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10413123553946666687970935 15619685330920000031956403)
              ·
                refine ⟨23429527996380000047934605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15619685330920000031956403 23429527996380000047934605)
                ·
                  refine ⟨8786072998642500017975477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23429527996380000047934605 8786072998642500017975477)
                  ·
                    refine ⟨823694343622734376685201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8786072998642500017975477 823694343622734376685201)
                    ·
                      rfl

theorem cell23_4812417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_4812417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812417 prefixEnd_4812417 := by exact prefixLift 4812417
  have htrace : WordTrace (prefixWord ++ tailWord_4812417) baseStart_4812417 baseEnd_4812417 := by
    simpa [prefixWord, tailWord_4812417, baseEnd_4812417] using wordTrace_append hprefix tailTrace_4812417
  have hstable : (prefixWord ++ tailWord_4812417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812417).length < 2 ^ (prefixWord ++ tailWord_4812417).sum := by decide
  have hdescent : baseEnd_4812417 < baseStart_4812417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812437 : List Nat := [1, 3, 2, 1, 1, 1, 1, 7, 1, 1, 4]
def baseStart_4812437 : Nat := 118140960795 + 4812437 * 2 ^ 59
def prefixEnd_4812437 : Nat := 4983230072969 + 3 ^ 40 * 4812437 * 2
def baseEnd_4812437 : Nat := 2471093300481293051805511

theorem tailTrace_4812437 : CollatzResearch.WordTrace tailWord_4812437 prefixEnd_4812437 2471093300481293051805511 := by
  unfold tailWord_4812437
  simp only [CollatzResearch.WordTrace]
  refine ⟨175523997266370122650003565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117015998177580081766669043 175523997266370122650003565)
  ·
    refine ⟨65821498974888795993751337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175523997266370122650003565 65821498974888795993751337)
    ·
      refine ⟨49366124231166596995313503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65821498974888795993751337 49366124231166596995313503)
      ·
        refine ⟨74049186346749895492970255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49366124231166596995313503 74049186346749895492970255)
        ·
          refine ⟨111073779520124843239455383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74049186346749895492970255 111073779520124843239455383)
          ·
            refine ⟨166610669280187264859183075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111073779520124843239455383 166610669280187264859183075)
            ·
              refine ⟨249916003920280897288774613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166610669280187264859183075 249916003920280897288774613)
              ·
                refine ⟨5857406341881583530205655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 249916003920280897288774613 5857406341881583530205655)
                ·
                  refine ⟨8786109512822375295308483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5857406341881583530205655 8786109512822375295308483)
                  ·
                    refine ⟨13179164269233562942962725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8786109512822375295308483 13179164269233562942962725)
                    ·
                      refine ⟨2471093300481293051805511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13179164269233562942962725 2471093300481293051805511)
                      ·
                        rfl

theorem cell23_4812437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_4812437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812437 prefixEnd_4812437 := by exact prefixLift 4812437
  have htrace : WordTrace (prefixWord ++ tailWord_4812437) baseStart_4812437 baseEnd_4812437 := by
    simpa [prefixWord, tailWord_4812437, baseEnd_4812437] using wordTrace_append hprefix tailTrace_4812437
  have hstable : (prefixWord ++ tailWord_4812437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812437).length < 2 ^ (prefixWord ++ tailWord_4812437).sum := by decide
  have hdescent : baseEnd_4812437 < baseStart_4812437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812448 : List Nat := [2, 1, 1, 4, 3, 1, 4, 2, 1, 1, 3]
def baseStart_4812448 : Nat := 118140960795 + 4812448 * 2 ^ 59
def prefixEnd_4812448 : Nat := 4983230072969 + 3 ^ 40 * 4812448 * 2
def baseEnd_4812448 : Nat := 2471098948768492508767961

theorem tailTrace_4812448 : CollatzResearch.WordTrace tailWord_4812448 prefixEnd_4812448 2471098948768492508767961 := by
  unfold tailWord_4812448
  simp only [CollatzResearch.WordTrace]
  refine ⟨87762199234665135764326999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117016265646220181019102665 87762199234665135764326999)
  ·
    refine ⟨131643298851997703646490499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87762199234665135764326999 131643298851997703646490499)
    ·
      refine ⟨197464948277996555469735749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131643298851997703646490499 197464948277996555469735749)
      ·
        refine ⟨37024677802124354150575453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197464948277996555469735749 37024677802124354150575453)
        ·
          refine ⟨13884254175796632806465795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37024677802124354150575453 13884254175796632806465795)
          ·
            refine ⟨20826381263694949209698693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13884254175796632806465795 20826381263694949209698693)
            ·
              refine ⟨3904946486942802976818505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20826381263694949209698693 3904946486942802976818505)
              ·
                refine ⟨2928709865207102232613879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3904946486942802976818505 2928709865207102232613879)
                ·
                  refine ⟨4393064797810653348920819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2928709865207102232613879 4393064797810653348920819)
                  ·
                    refine ⟨6589597196715980023381229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4393064797810653348920819 6589597196715980023381229)
                    ·
                      refine ⟨2471098948768492508767961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6589597196715980023381229 2471098948768492508767961)
                      ·
                        rfl

theorem cell23_4812448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_4812448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812448 prefixEnd_4812448 := by exact prefixLift 4812448
  have htrace : WordTrace (prefixWord ++ tailWord_4812448) baseStart_4812448 baseEnd_4812448 := by
    simpa [prefixWord, tailWord_4812448, baseEnd_4812448] using wordTrace_append hprefix tailTrace_4812448
  have hstable : (prefixWord ++ tailWord_4812448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812448).length < 2 ^ (prefixWord ++ tailWord_4812448).sum := by decide
  have hdescent : baseEnd_4812448 < baseStart_4812448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812467 : List Nat := [1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 4]
def baseStart_4812467 : Nat := 118140960795 + 4812467 * 2 ^ 59
def prefixEnd_4812467 : Nat := 4983230072969 + 3 ^ 40 * 4812467 * 2
def baseEnd_4812467 : Nat := 2471108704900927934430373

theorem tailTrace_4812467 : CollatzResearch.WordTrace tailWord_4812467 prefixEnd_4812467 2471108704900927934430373 := by
  unfold tailWord_4812467
  simp only [CollatzResearch.WordTrace]
  refine ⟨175525091456261437773595655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117016727637507625182397103 175525091456261437773595655)
  ·
    refine ⟨263287637184392156660393483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175525091456261437773595655 263287637184392156660393483)
    ·
      refine ⟨394931455776588234990590225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263287637184392156660393483 394931455776588234990590225)
      ·
        refine ⟨296198591832441176242942669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 394931455776588234990590225 296198591832441176242942669)
        ·
          refine ⟨111074471937165441091103501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 296198591832441176242942669 111074471937165441091103501)
          ·
            refine ⟨41652926976437040409163813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111074471937165441091103501 41652926976437040409163813)
            ·
              refine ⟨7809923808081945076718215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41652926976437040409163813 7809923808081945076718215)
              ·
                refine ⟨11714885712122917615077323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7809923808081945076718215 11714885712122917615077323)
                ·
                  refine ⟨17572328568184376422615985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11714885712122917615077323 17572328568184376422615985)
                  ·
                    refine ⟨13179246426138282316961989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17572328568184376422615985 13179246426138282316961989)
                    ·
                      refine ⟨2471108704900927934430373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13179246426138282316961989 2471108704900927934430373)
                      ·
                        rfl

theorem cell23_4812467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 4].length) (baseStart_4812467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812467 prefixEnd_4812467 := by exact prefixLift 4812467
  have htrace : WordTrace (prefixWord ++ tailWord_4812467) baseStart_4812467 baseEnd_4812467 := by
    simpa [prefixWord, tailWord_4812467, baseEnd_4812467] using wordTrace_append hprefix tailTrace_4812467
  have hstable : (prefixWord ++ tailWord_4812467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812467).length < 2 ^ (prefixWord ++ tailWord_4812467).sum := by decide
  have hdescent : baseEnd_4812467 < baseStart_4812467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812471 : List Nat := [1, 1, 3, 1, 5, 2, 1, 2, 3, 2, 2]
def baseStart_4812471 : Nat := 118140960795 + 4812471 * 2 ^ 59
def prefixEnd_4812471 : Nat := 4983230072969 + 3 ^ 40 * 4812471 * 2
def baseEnd_4812471 : Nat := 2471110758823545918780355

theorem tailTrace_4812471 : CollatzResearch.WordTrace tailWord_4812471 prefixEnd_4812471 2471110758823545918780355 := by
  unfold tailWord_4812471
  simp only [CollatzResearch.WordTrace]
  refine ⟨175525237348246946456741267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117016824898831297637827511 175525237348246946456741267)
  ·
    refine ⟨263287856022370419685111901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175525237348246946456741267 263287856022370419685111901)
    ·
      refine ⟨98732946008388907381916963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263287856022370419685111901 98732946008388907381916963)
      ·
        refine ⟨148099419012583361072875445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98732946008388907381916963 148099419012583361072875445)
        ·
          refine ⟨13884320532429690100582073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 148099419012583361072875445 13884320532429690100582073)
          ·
            refine ⟨10413240399322267575436555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13884320532429690100582073 10413240399322267575436555)
            ·
              refine ⟨15619860598983401363154833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10413240399322267575436555 15619860598983401363154833)
              ·
                refine ⟨11714895449237551022366125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15619860598983401363154833 11714895449237551022366125)
                ·
                  refine ⟨4393085793464081633387297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11714895449237551022366125 4393085793464081633387297)
                  ·
                    refine ⟨3294814345098061225040473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4393085793464081633387297 3294814345098061225040473)
                    ·
                      refine ⟨2471110758823545918780355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3294814345098061225040473 2471110758823545918780355)
                      ·
                        rfl

theorem cell23_4812471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 2, 2].length) (baseStart_4812471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812471 prefixEnd_4812471 := by exact prefixLift 4812471
  have htrace : WordTrace (prefixWord ++ tailWord_4812471) baseStart_4812471 baseEnd_4812471 := by
    simpa [prefixWord, tailWord_4812471, baseEnd_4812471] using wordTrace_append hprefix tailTrace_4812471
  have hstable : (prefixWord ++ tailWord_4812471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812471).length < 2 ^ (prefixWord ++ tailWord_4812471).sum := by decide
  have hdescent : baseEnd_4812471 < baseStart_4812471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812477 : List Nat := [1, 4, 1, 2, 1, 2, 5, 7]
def baseStart_4812477 : Nat := 118140960795 + 4812477 * 2 ^ 59
def prefixEnd_4812477 : Nat := 4983230072969 + 3 ^ 40 * 4812477 * 2
def baseEnd_4812477 : Nat := 91522734803980477603901

theorem tailTrace_4812477 : CollatzResearch.WordTrace tailWord_4812477 prefixEnd_4812477 91522734803980477603901 := by
  unfold tailWord_4812477
  simp only [CollatzResearch.WordTrace]
  refine ⟨175525456186225209481459685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117016970790816806320973123 175525456186225209481459685)
  ·
    refine ⟨32911023034917226777773691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175525456186225209481459685 32911023034917226777773691)
    ·
      refine ⟨49366534552375840166660537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32911023034917226777773691 49366534552375840166660537)
      ·
        refine ⟨37024900914281880124995403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49366534552375840166660537 37024900914281880124995403)
        ·
          refine ⟨55537351371422820187493105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37024900914281880124995403 55537351371422820187493105)
          ·
            refine ⟨41653013528567115140619829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55537351371422820187493105 41653013528567115140619829)
            ·
              refine ⟨3904970018303167044433109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41653013528567115140619829 3904970018303167044433109)
              ·
                refine ⟨91522734803980477603901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3904970018303167044433109 91522734803980477603901)
                ·
                  rfl

theorem cell23_4812477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 7].length) (baseStart_4812477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812477 prefixEnd_4812477 := by exact prefixLift 4812477
  have htrace : WordTrace (prefixWord ++ tailWord_4812477) baseStart_4812477 baseEnd_4812477 := by
    simpa [prefixWord, tailWord_4812477, baseEnd_4812477] using wordTrace_append hprefix tailTrace_4812477
  have hstable : (prefixWord ++ tailWord_4812477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812477).length < 2 ^ (prefixWord ++ tailWord_4812477).sum := by decide
  have hdescent : baseEnd_4812477 < baseStart_4812477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812487 : List Nat := [1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 3]
def baseStart_4812487 : Nat := 118140960795 + 4812487 * 2 ^ 59
def prefixEnd_4812487 : Nat := 4983230072969 + 3 ^ 40 * 4812487 * 2
def baseEnd_4812487 : Nat := 2471118974514017856180281

theorem tailTrace_4812487 : CollatzResearch.WordTrace tailWord_4812487 prefixEnd_4812487 2471118974514017856180281 := by
  unfold tailWord_4812487
  simp only [CollatzResearch.WordTrace]
  refine ⟨175525820916188981189323715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117017213944125987459549143 175525820916188981189323715)
  ·
    refine ⟨263288731374283471783985573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175525820916188981189323715 263288731374283471783985573)
    ·
      refine ⟨49366637132678150959497295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 263288731374283471783985573 49366637132678150959497295)
      ·
        refine ⟨74049955699017226439245943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49366637132678150959497295 74049955699017226439245943)
        ·
          refine ⟨111074933548525839658868915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74049955699017226439245943 111074933548525839658868915)
          ·
            refine ⟨166612400322788759488303373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111074933548525839658868915 166612400322788759488303373)
            ·
              refine ⟨62479650121045784808113765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166612400322788759488303373 62479650121045784808113765)
              ·
                refine ⟨11714934397696084651521331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62479650121045784808113765 11714934397696084651521331)
                ·
                  refine ⟨17572401596544126977281997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11714934397696084651521331 17572401596544126977281997)
                  ·
                    refine ⟨6589650598704047616480749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17572401596544126977281997 6589650598704047616480749)
                    ·
                      refine ⟨2471118974514017856180281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6589650598704047616480749 2471118974514017856180281)
                      ·
                        rfl

theorem cell23_4812487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_4812487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812487 prefixEnd_4812487 := by exact prefixLift 4812487
  have htrace : WordTrace (prefixWord ++ tailWord_4812487) baseStart_4812487 baseEnd_4812487 := by
    simpa [prefixWord, tailWord_4812487, baseEnd_4812487] using wordTrace_append hprefix tailTrace_4812487
  have hstable : (prefixWord ++ tailWord_4812487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812487).length < 2 ^ (prefixWord ++ tailWord_4812487).sum := by decide
  have hdescent : baseEnd_4812487 < baseStart_4812487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812488 : List Nat := [2, 1, 3, 1, 2, 2, 4, 3, 1, 2, 2]
def baseStart_4812488 : Nat := 118140960795 + 4812488 * 2 ^ 59
def prefixEnd_4812488 : Nat := 4983230072969 + 3 ^ 40 * 4812488 * 2
def baseEnd_4812488 : Nat := 2471119487994672352267777

theorem tailTrace_4812488 : CollatzResearch.WordTrace tailWord_4812488 prefixEnd_4812488 2471119487994672352267777 := by
  unfold tailWord_4812488
  simp only [CollatzResearch.WordTrace]
  refine ⟨87762928694592679180055059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117017238259456905573406745 87762928694592679180055059)
  ·
    refine ⟨131644393041889018770082589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87762928694592679180055059 131644393041889018770082589)
    ·
      refine ⟨49366647390708382038780971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131644393041889018770082589 49366647390708382038780971)
      ·
        refine ⟨74049971086062573058171457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49366647390708382038780971 74049971086062573058171457)
        ·
          refine ⟨55537478314546929793628593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74049971086062573058171457 55537478314546929793628593)
          ·
            refine ⟨41653108735910197345221445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55537478314546929793628593 41653108735910197345221445)
            ·
              refine ⟨7809957887983162002229021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41653108735910197345221445 7809957887983162002229021)
              ·
                refine ⟨2928734207993685750835883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7809957887983162002229021 2928734207993685750835883)
                ·
                  refine ⟨4393101311990528626253825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2928734207993685750835883 4393101311990528626253825)
                  ·
                    refine ⟨3294825983992896469690369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4393101311990528626253825 3294825983992896469690369)
                    ·
                      refine ⟨2471119487994672352267777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3294825983992896469690369 2471119487994672352267777)
                      ·
                        rfl

theorem cell23_4812488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 1, 2, 2].length) (baseStart_4812488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812488 prefixEnd_4812488 := by exact prefixLift 4812488
  have htrace : WordTrace (prefixWord ++ tailWord_4812488) baseStart_4812488 baseEnd_4812488 := by
    simpa [prefixWord, tailWord_4812488, baseEnd_4812488] using wordTrace_append hprefix tailTrace_4812488
  have hstable : (prefixWord ++ tailWord_4812488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812488).length < 2 ^ (prefixWord ++ tailWord_4812488).sum := by decide
  have hdescent : baseEnd_4812488 < baseStart_4812488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812504 : List Nat := [2, 1, 2, 2, 3, 1, 3, 1, 4, 1, 3]
def baseStart_4812504 : Nat := 118140960795 + 4812504 * 2 ^ 59
def prefixEnd_4812504 : Nat := 4983230072969 + 3 ^ 40 * 4812504 * 2
def baseEnd_4812504 : Nat := 2471127703685144289667703

theorem tailTrace_4812504 : CollatzResearch.WordTrace tailWord_4812504 prefixEnd_4812504 2471127703685144289667703 := by
  unfold tailWord_4812504
  simp only [CollatzResearch.WordTrace]
  refine ⟨87763220478563696546346283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117017627304751595395128377 87763220478563696546346283)
  ·
    refine ⟨131644830717845544819519425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87763220478563696546346283 131644830717845544819519425)
    ·
      refine ⟨98733623038384158614639569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131644830717845544819519425 98733623038384158614639569)
      ·
        refine ⟨74050217278788118960979677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98733623038384158614639569 74050217278788118960979677)
        ·
          refine ⟨27768831479545544610367379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74050217278788118960979677 27768831479545544610367379)
          ·
            refine ⟨41653247219318316915551069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27768831479545544610367379 41653247219318316915551069)
            ·
              refine ⟨15619967707244368843331651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41653247219318316915551069 15619967707244368843331651)
              ·
                refine ⟨23429951560866553264997477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15619967707244368843331651 23429951560866553264997477)
                ·
                  refine ⟨4393115917662478737187027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23429951560866553264997477 4393115917662478737187027)
                  ·
                    refine ⟨6589673876493718105780541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4393115917662478737187027 6589673876493718105780541)
                    ·
                      refine ⟨2471127703685144289667703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6589673876493718105780541 2471127703685144289667703)
                      ·
                        rfl

theorem cell23_4812504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_4812504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812504 prefixEnd_4812504 := by exact prefixLift 4812504
  have htrace : WordTrace (prefixWord ++ tailWord_4812504) baseStart_4812504 baseEnd_4812504 := by
    simpa [prefixWord, tailWord_4812504, baseEnd_4812504] using wordTrace_append hprefix tailTrace_4812504
  have hstable : (prefixWord ++ tailWord_4812504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812504).length < 2 ^ (prefixWord ++ tailWord_4812504).sum := by decide
  have hdescent : baseEnd_4812504 < baseStart_4812504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812561 : List Nat := [1, 2, 2, 1, 1, 3, 1, 6, 2, 2, 2]
def baseStart_4812561 : Nat := 118140960795 + 4812561 * 2 ^ 59
def prefixEnd_4812561 : Nat := 4983230072969 + 3 ^ 40 * 4812561 * 2
def baseEnd_4812561 : Nat := 2471156972082450566654941

theorem tailTrace_4812561 : CollatzResearch.WordTrace tailWord_4812561 prefixEnd_4812561 2471156972082450566654941 := by
  unfold tailWord_4812561
  simp only [CollatzResearch.WordTrace]
  refine ⟨175528519917920891827517537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117019013278613927885011691 175528519917920891827517537)
  ·
    refine ⟨131646389938440668870638153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175528519917920891827517537 131646389938440668870638153)
    ·
      refine ⟨98734792453830501652978615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131646389938440668870638153 98734792453830501652978615)
      ·
        refine ⟨148102188680745752479467923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98734792453830501652978615 148102188680745752479467923)
        ·
          refine ⟨222153283021118628719201885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148102188680745752479467923 222153283021118628719201885)
          ·
            refine ⟨83307481132919485769700707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222153283021118628719201885 83307481132919485769700707)
            ·
              refine ⟨124961221699379228654551061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83307481132919485769700707 124961221699379228654551061)
              ·
                refine ⟨5857557267158401343182081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 124961221699379228654551061 5857557267158401343182081)
                ·
                  refine ⟨4393167950368801007386561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5857557267158401343182081 4393167950368801007386561)
                  ·
                    refine ⟨3294875962776600755539921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4393167950368801007386561 3294875962776600755539921)
                    ·
                      refine ⟨2471156972082450566654941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3294875962776600755539921 2471156972082450566654941)
                      ·
                        rfl

theorem cell23_4812561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 2, 2].length) (baseStart_4812561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812561 prefixEnd_4812561 := by exact prefixLift 4812561
  have htrace : WordTrace (prefixWord ++ tailWord_4812561) baseStart_4812561 baseEnd_4812561 := by
    simpa [prefixWord, tailWord_4812561, baseEnd_4812561] using wordTrace_append hprefix tailTrace_4812561
  have hstable : (prefixWord ++ tailWord_4812561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812561).length < 2 ^ (prefixWord ++ tailWord_4812561).sum := by decide
  have hdescent : baseEnd_4812561 < baseStart_4812561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812578 : List Nat := [3, 3, 1, 1, 2, 1, 3, 3, 2, 2, 2]
def baseStart_4812578 : Nat := 118140960795 + 4812578 * 2 ^ 59
def prefixEnd_4812578 : Nat := 4983230072969 + 3 ^ 40 * 4812578 * 2
def baseEnd_4812578 : Nat := 2471165701253577000142363

theorem tailTrace_4812578 : CollatzResearch.WordTrace tailWord_4812578 prefixEnd_4812578 2471165701253577000142363 := by
  unfold tailWord_4812578
  simp only [CollatzResearch.WordTrace]
  refine ⟨43882284989714825932721597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117019426639239535820590925 43882284989714825932721597)
  ·
    refine ⟨16455856871143059724770599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43882284989714825932721597 16455856871143059724770599)
    ·
      refine ⟨24683785306714589587155899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16455856871143059724770599 24683785306714589587155899)
      ·
        refine ⟨37025677960071884380733849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24683785306714589587155899 37025677960071884380733849)
        ·
          refine ⟨27769258470053913285550387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37025677960071884380733849 27769258470053913285550387)
          ·
            refine ⟨41653887705080869928325581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27769258470053913285550387 41653887705080869928325581)
            ·
              refine ⟨15620207889405326223122093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41653887705080869928325581 15620207889405326223122093)
              ·
                refine ⟨5857577958526997333670785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15620207889405326223122093 5857577958526997333670785)
                ·
                  refine ⟨4393183468895248000253089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5857577958526997333670785 4393183468895248000253089)
                  ·
                    refine ⟨3294887601671436000189817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4393183468895248000253089 3294887601671436000189817)
                    ·
                      refine ⟨2471165701253577000142363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3294887601671436000189817 2471165701253577000142363)
                      ·
                        rfl

theorem cell23_4812578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_4812578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812578 prefixEnd_4812578 := by exact prefixLift 4812578
  have htrace : WordTrace (prefixWord ++ tailWord_4812578) baseStart_4812578 baseEnd_4812578 := by
    simpa [prefixWord, tailWord_4812578, baseEnd_4812578] using wordTrace_append hprefix tailTrace_4812578
  have hstable : (prefixWord ++ tailWord_4812578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812578).length < 2 ^ (prefixWord ++ tailWord_4812578).sum := by decide
  have hdescent : baseEnd_4812578 < baseStart_4812578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812657 : List Nat := [1, 2, 2, 2, 1, 3, 2, 2, 8]
def baseStart_4812657 : Nat := 118140960795 + 4812657 * 2 ^ 59
def prefixEnd_4812657 : Nat := 4983230072969 + 3 ^ 40 * 4812657 * 2
def baseEnd_4812657 : Nat := 274578474025031354561611

theorem tailTrace_4812657 : CollatzResearch.WordTrace tailWord_4812657 prefixEnd_4812657 274578474025031354561611 := by
  unfold tailWord_4812657
  simp only [CollatzResearch.WordTrace]
  refine ⟨175532021325573100223012225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117021347550382066815341483 175532021325573100223012225)
  ·
    refine ⟨131649015994179825167259169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175532021325573100223012225 131649015994179825167259169)
    ·
      refine ⟨98736761995634868875444377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131649015994179825167259169 98736761995634868875444377)
      ·
        refine ⟨74052571496726151656583283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98736761995634868875444377 74052571496726151656583283)
        ·
          refine ⟨111078857245089227484874925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74052571496726151656583283 111078857245089227484874925)
          ·
            refine ⟨41654571466908460306828097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111078857245089227484874925 41654571466908460306828097)
            ·
              refine ⟨31240928600181345230121073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41654571466908460306828097 31240928600181345230121073)
              ·
                refine ⟨23430696450136008922590805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31240928600181345230121073 23430696450136008922590805)
                ·
                  refine ⟨274578474025031354561611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23430696450136008922590805 274578474025031354561611)
                  ·
                    rfl

theorem cell23_4812657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 8].length) (baseStart_4812657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812657 prefixEnd_4812657 := by exact prefixLift 4812657
  have htrace : WordTrace (prefixWord ++ tailWord_4812657) baseStart_4812657 baseEnd_4812657 := by
    simpa [prefixWord, tailWord_4812657, baseEnd_4812657] using wordTrace_append hprefix tailTrace_4812657
  have hstable : (prefixWord ++ tailWord_4812657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812657).length < 2 ^ (prefixWord ++ tailWord_4812657).sum := by decide
  have hdescent : baseEnd_4812657 < baseStart_4812657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812677 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 1, 1, 8]
def baseStart_4812677 : Nat := 118140960795 + 4812677 * 2 ^ 59
def prefixEnd_4812677 : Nat := 4983230072969 + 3 ^ 40 * 4812677 * 2
def baseEnd_4812677 : Nat := 2471216535838372112804407

theorem tailTrace_4812677 : CollatzResearch.WordTrace tailWord_4812677 prefixEnd_4812677 2471216535838372112804407 := by
  unfold tailWord_4812677
  simp only [CollatzResearch.WordTrace]
  refine ⟨175532750785500643638740285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117021833857000429092493523 175532750785500643638740285)
  ·
    refine ⟨65824781544562741364527607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175532750785500643638740285 65824781544562741364527607)
    ·
      refine ⟨98737172316844112046791411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65824781544562741364527607 98737172316844112046791411)
      ·
        refine ⟨148105758475266168070187117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98737172316844112046791411 148105758475266168070187117)
        ·
          refine ⟨55539659428224813026320169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148105758475266168070187117 55539659428224813026320169)
          ·
            refine ⟨41654744571168609769740127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55539659428224813026320169 41654744571168609769740127)
            ·
              refine ⟨62482116856752914654610191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41654744571168609769740127 62482116856752914654610191)
              ·
                refine ⟨93723175285129371981915287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62482116856752914654610191 93723175285129371981915287)
                ·
                  refine ⟨140584762927694057972872931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93723175285129371981915287 140584762927694057972872931)
                  ·
                    refine ⟨210877144391541086959309397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 140584762927694057972872931 210877144391541086959309397)
                    ·
                      refine ⟨2471216535838372112804407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 210877144391541086959309397 2471216535838372112804407)
                      ·
                        rfl

theorem cell23_4812677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_4812677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812677 prefixEnd_4812677 := by exact prefixLift 4812677
  have htrace : WordTrace (prefixWord ++ tailWord_4812677) baseStart_4812677 baseEnd_4812677 := by
    simpa [prefixWord, tailWord_4812677, baseEnd_4812677] using wordTrace_append hprefix tailTrace_4812677
  have hstable : (prefixWord ++ tailWord_4812677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812677).length < 2 ^ (prefixWord ++ tailWord_4812677).sum := by decide
  have hdescent : baseEnd_4812677 < baseStart_4812677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812697 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 7]
def baseStart_4812697 : Nat := 118140960795 + 4812697 * 2 ^ 59
def prefixEnd_4812697 : Nat := 4983230072969 + 3 ^ 40 * 4812697 * 2
def baseEnd_4812697 : Nat := 2471226805451462034554315

theorem tailTrace_4812697 : CollatzResearch.WordTrace tailWord_4812697 prefixEnd_4812697 2471226805451462034554315 := by
  unfold tailWord_4812697
  simp only [CollatzResearch.WordTrace]
  refine ⟨175533480245428187054468345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117022320163618791369645563 175533480245428187054468345)
  ·
    refine ⟨131650110184071140290851259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175533480245428187054468345 131650110184071140290851259)
    ·
      refine ⟨197475165276106710436276889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131650110184071140290851259 197475165276106710436276889)
      ·
        refine ⟨148106373957080032827207667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197475165276106710436276889 148106373957080032827207667)
        ·
          refine ⟨222159560935620049240811501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148106373957080032827207667 222159560935620049240811501)
          ·
            refine ⟨83309835350857518465304313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222159560935620049240811501 83309835350857518465304313)
            ·
              refine ⟨62482376513143138848978235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83309835350857518465304313 62482376513143138848978235)
              ·
                refine ⟨93723564769714708273467353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62482376513143138848978235 93723564769714708273467353)
                ·
                  refine ⟨70292673577286031205100515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93723564769714708273467353 70292673577286031205100515)
                  ·
                    refine ⟨105439010365929046807650773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70292673577286031205100515 105439010365929046807650773)
                    ·
                      refine ⟨2471226805451462034554315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 105439010365929046807650773 2471226805451462034554315)
                      ·
                        rfl

theorem cell23_4812697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_4812697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812697 prefixEnd_4812697 := by exact prefixLift 4812697
  have htrace : WordTrace (prefixWord ++ tailWord_4812697) baseStart_4812697 baseEnd_4812697 := by
    simpa [prefixWord, tailWord_4812697, baseEnd_4812697] using wordTrace_append hprefix tailTrace_4812697
  have hstable : (prefixWord ++ tailWord_4812697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812697).length < 2 ^ (prefixWord ++ tailWord_4812697).sum := by decide
  have hdescent : baseEnd_4812697 < baseStart_4812697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812721 : List Nat := [1, 2, 2, 4, 2, 1, 2, 3, 1, 5]
def baseStart_4812721 : Nat := 118140960795 + 4812721 * 2 ^ 59
def prefixEnd_4812721 : Nat := 4983230072969 + 3 ^ 40 * 4812721 * 2
def baseEnd_4812721 : Nat := 823746376329056646884735

theorem tailTrace_4812721 : CollatzResearch.WordTrace tailWord_4812721 prefixEnd_4812721 823746376329056646884735 := by
  unfold tailWord_4812721
  simp only [CollatzResearch.WordTrace]
  refine ⟨175534355597341239153342017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117022903731560826102228011 175534355597341239153342017)
  ·
    refine ⟨131650766698005929365006513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175534355597341239153342017 131650766698005929365006513)
    ·
      refine ⟨98738075023504447023754885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131650766698005929365006513 98738075023504447023754885)
      ·
        refine ⟨18513389066907083816954041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98738075023504447023754885 18513389066907083816954041)
        ·
          refine ⟨13885041800180312862715531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18513389066907083816954041 13885041800180312862715531)
          ·
            refine ⟨20827562700270469294073297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13885041800180312862715531 20827562700270469294073297)
            ·
              refine ⟨15620672025202851970554973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20827562700270469294073297 15620672025202851970554973)
              ·
                refine ⟨5857752009451069488958115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15620672025202851970554973 5857752009451069488958115)
                ·
                  refine ⟨8786628014176604233437173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5857752009451069488958115 8786628014176604233437173)
                  ·
                    refine ⟨823746376329056646884735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8786628014176604233437173 823746376329056646884735)
                    ·
                      rfl

theorem cell23_4812721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 5].length) (baseStart_4812721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812721 prefixEnd_4812721 := by exact prefixLift 4812721
  have htrace : WordTrace (prefixWord ++ tailWord_4812721) baseStart_4812721 baseEnd_4812721 := by
    simpa [prefixWord, tailWord_4812721, baseEnd_4812721] using wordTrace_append hprefix tailTrace_4812721
  have hstable : (prefixWord ++ tailWord_4812721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812721).length < 2 ^ (prefixWord ++ tailWord_4812721).sum := by decide
  have hdescent : baseEnd_4812721 < baseStart_4812721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812735 : List Nat := [1, 1, 2, 2, 2, 1, 7, 2, 1, 1, 3]
def baseStart_4812735 : Nat := 118140960795 + 4812735 * 2 ^ 59
def prefixEnd_4812735 : Nat := 4983230072969 + 3 ^ 40 * 4812735 * 2
def baseEnd_4812735 : Nat := 2471246317716332885879141

theorem tailTrace_4812735 : CollatzResearch.WordTrace tailWord_4812735 prefixEnd_4812735 2471246317716332885879141 := by
  unfold tailWord_4812735
  simp only [CollatzResearch.WordTrace]
  refine ⟨175534866219290519544351659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117023244146193679696234439 175534866219290519544351659)
  ·
    refine ⟨263302299328935779316527489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175534866219290519544351659 263302299328935779316527489)
    ·
      refine ⟨197476724496701834487395617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263302299328935779316527489 197476724496701834487395617)
      ·
        refine ⟨148107543372526375865546713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197476724496701834487395617 148107543372526375865546713)
        ·
          refine ⟨111080657529394781899160035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148107543372526375865546713 111080657529394781899160035)
          ·
            refine ⟨166620986294092172848740053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111080657529394781899160035 166620986294092172848740053)
            ·
              refine ⟨3905179366267785301142345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 166620986294092172848740053 3905179366267785301142345)
              ·
                refine ⟨2928884524700838975856759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3905179366267785301142345 2928884524700838975856759)
                ·
                  refine ⟨4393326787051258463785139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2928884524700838975856759 4393326787051258463785139)
                  ·
                    refine ⟨6589990180576887695677709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4393326787051258463785139 6589990180576887695677709)
                    ·
                      refine ⟨2471246317716332885879141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6589990180576887695677709 2471246317716332885879141)
                      ·
                        rfl

theorem cell23_4812735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 1, 1, 3].length) (baseStart_4812735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812735 prefixEnd_4812735 := by exact prefixLift 4812735
  have htrace : WordTrace (prefixWord ++ tailWord_4812735) baseStart_4812735 baseEnd_4812735 := by
    simpa [prefixWord, tailWord_4812735, baseEnd_4812735] using wordTrace_append hprefix tailTrace_4812735
  have hstable : (prefixWord ++ tailWord_4812735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812735).length < 2 ^ (prefixWord ++ tailWord_4812735).sum := by decide
  have hdescent : baseEnd_4812735 < baseStart_4812735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812751 : List Nat := [1, 1, 2, 1, 1, 5, 3, 3, 2, 4]
def baseStart_4812751 : Nat := 118140960795 + 4812751 * 2 ^ 59
def prefixEnd_4812751 : Nat := 4983230072969 + 3 ^ 40 * 4812751 * 2
def baseEnd_4812751 : Nat := 823751511135601607759689

theorem tailTrace_4812751 : CollatzResearch.WordTrace tailWord_4812751 prefixEnd_4812751 823751511135601607759689 := by
  unfold tailWord_4812751
  simp only [CollatzResearch.WordTrace]
  refine ⟨175535449787232554276934107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117023633191488369517956071 175535449787232554276934107)
  ·
    refine ⟨263303174680848831415401161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175535449787232554276934107 263303174680848831415401161)
    ·
      refine ⟨197477381010636623561550871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263303174680848831415401161 197477381010636623561550871)
      ·
        refine ⟨296216071515954935342326307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197477381010636623561550871 296216071515954935342326307)
        ·
          refine ⟨444324107273932403013489461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296216071515954935342326307 444324107273932403013489461)
          ·
            refine ⟨41655385056931162782514637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 444324107273932403013489461 41655385056931162782514637)
            ·
              refine ⟨15620769396349186043442989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41655385056931162782514637 15620769396349186043442989)
              ·
                refine ⟨5857788523630944766291121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15620769396349186043442989 5857788523630944766291121)
                ·
                  refine ⟨4393341392723208574718341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5857788523630944766291121 4393341392723208574718341)
                  ·
                    refine ⟨823751511135601607759689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4393341392723208574718341 823751511135601607759689)
                    ·
                      rfl

theorem cell23_4812751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 4].length) (baseStart_4812751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812751 prefixEnd_4812751 := by exact prefixLift 4812751
  have htrace : WordTrace (prefixWord ++ tailWord_4812751) baseStart_4812751 baseEnd_4812751 := by
    simpa [prefixWord, tailWord_4812751, baseEnd_4812751] using wordTrace_append hprefix tailTrace_4812751
  have hstable : (prefixWord ++ tailWord_4812751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812751).length < 2 ^ (prefixWord ++ tailWord_4812751).sum := by decide
  have hdescent : baseEnd_4812751 < baseStart_4812751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812771 : List Nat := [1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 4]
def baseStart_4812771 : Nat := 118140960795 + 4812771 * 2 ^ 59
def prefixEnd_4812771 : Nat := 4983230072969 + 3 ^ 40 * 4812771 * 2
def baseEnd_4812771 : Nat := 2471264803019894745028975

theorem tailTrace_4812771 : CollatzResearch.WordTrace tailWord_4812771 prefixEnd_4812771 2471264803019894745028975 := by
  unfold tailWord_4812771
  simp only [CollatzResearch.WordTrace]
  refine ⟨175536179247160097692662167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117024119498106731795108111 175536179247160097692662167)
  ·
    refine ⟨263304268870740146538993251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175536179247160097692662167 263304268870740146538993251)
    ·
      refine ⟨394956403306110219808489877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263304268870740146538993251 394956403306110219808489877)
      ·
        refine ⟨18513581404973916553522963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 394956403306110219808489877 18513581404973916553522963)
        ·
          refine ⟨27770372107460874830284445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18513581404973916553522963 27770372107460874830284445)
          ·
            refine ⟨10413889540297828061356667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27770372107460874830284445 10413889540297828061356667)
            ·
              refine ⟨15620834310446742092035001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10413889540297828061356667 15620834310446742092035001)
              ·
                refine ⟨11715625732835056569026251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15620834310446742092035001 11715625732835056569026251)
                ·
                  refine ⟨17573438599252584853539377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11715625732835056569026251 17573438599252584853539377)
                  ·
                    refine ⟨13180078949439438640154533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17573438599252584853539377 13180078949439438640154533)
                    ·
                      refine ⟨2471264803019894745028975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13180078949439438640154533 2471264803019894745028975)
                      ·
                        rfl

theorem cell23_4812771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_4812771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812771 prefixEnd_4812771 := by exact prefixLift 4812771
  have htrace : WordTrace (prefixWord ++ tailWord_4812771) baseStart_4812771 baseEnd_4812771 := by
    simpa [prefixWord, tailWord_4812771, baseEnd_4812771] using wordTrace_append hprefix tailTrace_4812771
  have hstable : (prefixWord ++ tailWord_4812771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812771).length < 2 ^ (prefixWord ++ tailWord_4812771).sum := by decide
  have hdescent : baseEnd_4812771 < baseStart_4812771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812775 : List Nat := [1, 1, 5, 2, 3, 1, 3, 1, 1, 1, 4]
def baseStart_4812775 : Nat := 118140960795 + 4812775 * 2 ^ 59
def prefixEnd_4812775 : Nat := 4983230072969 + 3 ^ 40 * 4812775 * 2
def baseEnd_4812775 : Nat := 2471266856942512729378957

theorem tailTrace_4812775 : CollatzResearch.WordTrace tailWord_4812775 prefixEnd_4812775 2471266856942512729378957 := by
  unfold tailWord_4812775
  simp only [CollatzResearch.WordTrace]
  refine ⟨175536325139145606375807779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117024216759430404250538519 175536325139145606375807779)
  ·
    refine ⟨263304487708718409563711669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175536325139145606375807779 263304487708718409563711669)
    ·
      refine ⟨24684795722692350896597969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 263304487708718409563711669 24684795722692350896597969)
      ·
        refine ⟨18513596792019263172448477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24684795722692350896597969 18513596792019263172448477)
        ·
          refine ⟨6942598797007223689668179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18513596792019263172448477 6942598797007223689668179)
          ·
            refine ⟨10413898195510835534502269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6942598797007223689668179 10413898195510835534502269)
            ·
              refine ⟨3905211823316563325438351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10413898195510835534502269 3905211823316563325438351)
              ·
                refine ⟨5857817734974844988157527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3905211823316563325438351 5857817734974844988157527)
                ·
                  refine ⟨8786726602462267482236291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5857817734974844988157527 8786726602462267482236291)
                  ·
                    refine ⟨13180089903693401223354437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8786726602462267482236291 13180089903693401223354437)
                    ·
                      refine ⟨2471266856942512729378957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13180089903693401223354437 2471266856942512729378957)
                      ·
                        rfl

theorem cell23_4812775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_4812775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812775 prefixEnd_4812775 := by exact prefixLift 4812775
  have htrace : WordTrace (prefixWord ++ tailWord_4812775) baseStart_4812775 baseEnd_4812775 := by
    simpa [prefixWord, tailWord_4812775, baseEnd_4812775] using wordTrace_append hprefix tailTrace_4812775
  have hstable : (prefixWord ++ tailWord_4812775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812775).length < 2 ^ (prefixWord ++ tailWord_4812775).sum := by decide
  have hdescent : baseEnd_4812775 < baseStart_4812775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812781 : List Nat := [1, 5, 1, 4, 1, 11]
def baseStart_4812781 : Nat := 118140960795 + 4812781 * 2 ^ 59
def prefixEnd_4812781 : Nat := 4983230072969 + 3 ^ 40 * 4812781 * 2
def baseEnd_4812781 : Nat := 10169835135088229242403

theorem tailTrace_4812781 : CollatzResearch.WordTrace tailWord_4812781 prefixEnd_4812781 10169835135088229242403 := by
  unfold tailWord_4812781
  simp only [CollatzResearch.WordTrace]
  refine ⟨175536543977123869400526197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117024362651415912933684131 175536543977123869400526197)
  ·
    refine ⟨16456550997855362756299331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 175536543977123869400526197 16456550997855362756299331)
    ·
      refine ⟨24684826496783044134448997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16456550997855362756299331 24684826496783044134448997)
      ·
        refine ⟨4628404968146820775209187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24684826496783044134448997 4628404968146820775209187)
        ·
          refine ⟨6942607452220231162813781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4628404968146820775209187 6942607452220231162813781)
          ·
            refine ⟨10169835135088229242403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6942607452220231162813781 10169835135088229242403)
            ·
              rfl

theorem cell23_4812781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 11].length) (baseStart_4812781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812781 prefixEnd_4812781 := by exact prefixLift 4812781
  have htrace : WordTrace (prefixWord ++ tailWord_4812781) baseStart_4812781 baseEnd_4812781 := by
    simpa [prefixWord, tailWord_4812781, baseEnd_4812781] using wordTrace_append hprefix tailTrace_4812781
  have hstable : (prefixWord ++ tailWord_4812781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812781).length < 2 ^ (prefixWord ++ tailWord_4812781).sum := by decide
  have hdescent : baseEnd_4812781 < baseStart_4812781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812792 : List Nat := [2, 1, 2, 1, 1, 3, 6, 2, 1, 2, 2]
def baseStart_4812792 : Nat := 118140960795 + 4812792 * 2 ^ 59
def prefixEnd_4812792 : Nat := 4983230072969 + 3 ^ 40 * 4812792 * 2
def baseEnd_4812792 : Nat := 2471275586113639162866379

theorem tailTrace_4812792 : CollatzResearch.WordTrace tailWord_4812792 prefixEnd_4812792 2471275586113639162866379 := by
  unfold tailWord_4812792
  simp only [CollatzResearch.WordTrace]
  refine ⟨87768472590042009139588315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117024630120056012186117753 87768472590042009139588315)
  ·
    refine ⟨131652708885063013709382473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87768472590042009139588315 131652708885063013709382473)
    ·
      refine ⟨98739531663797260282036855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131652708885063013709382473 98739531663797260282036855)
      ·
        refine ⟨148109297495695890423055283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98739531663797260282036855 148109297495695890423055283)
        ·
          refine ⟨222163946243543835634582925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148109297495695890423055283 222163946243543835634582925)
          ·
            refine ⟨83311479841328938362968597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222163946243543835634582925 83311479841328938362968597)
            ·
              refine ⟨3905225617562293985764153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83311479841328938362968597 3905225617562293985764153)
              ·
                refine ⟨2928919213171720489323115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3905225617562293985764153 2928919213171720489323115)
                ·
                  refine ⟨4393378819757580733984673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2928919213171720489323115 4393378819757580733984673)
                  ·
                    refine ⟨3295034114818185550488505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4393378819757580733984673 3295034114818185550488505)
                    ·
                      refine ⟨2471275586113639162866379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3295034114818185550488505 2471275586113639162866379)
                      ·
                        rfl

theorem cell23_4812792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 1, 2, 2].length) (baseStart_4812792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812792 prefixEnd_4812792 := by exact prefixLift 4812792
  have htrace : WordTrace (prefixWord ++ tailWord_4812792) baseStart_4812792 baseEnd_4812792 := by
    simpa [prefixWord, tailWord_4812792, baseEnd_4812792] using wordTrace_append hprefix tailTrace_4812792
  have hstable : (prefixWord ++ tailWord_4812792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812792).length < 2 ^ (prefixWord ++ tailWord_4812792).sum := by decide
  have hdescent : baseEnd_4812792 < baseStart_4812792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812798 : List Nat := [4, 2, 2, 2, 1, 3, 1, 8]
def baseStart_4812798 : Nat := 118140960795 + 4812798 * 2 ^ 59
def prefixEnd_4812798 : Nat := 4983230072969 + 3 ^ 40 * 4812798 * 2
def baseEnd_4812798 : Nat := 91528839518428375533013

theorem tailTrace_4812798 : CollatzResearch.WordTrace tailWord_4812798 prefixEnd_4812798 91528839518428375533013 := by
  unfold tailWord_4812798
  simp only [CollatzResearch.WordTrace]
  refine ⟨21942145502257785162986881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117024776012041520869263365 21942145502257785162986881)
  ·
    refine ⟨16456609126693338872240161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21942145502257785162986881 16456609126693338872240161)
    ·
      refine ⟨12342456845020004154180121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16456609126693338872240161 12342456845020004154180121)
      ·
        refine ⟨9256842633765003115635091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12342456845020004154180121 9256842633765003115635091)
        ·
          refine ⟨13885263950647504673452637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9256842633765003115635091 13885263950647504673452637)
          ·
            refine ⟨5206973981492814252544739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13885263950647504673452637 5206973981492814252544739)
            ·
              refine ⟨7810460972239221378817109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5206973981492814252544739 7810460972239221378817109)
              ·
                refine ⟨91528839518428375533013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7810460972239221378817109 91528839518428375533013)
                ·
                  rfl

theorem cell23_4812798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 8].length) (baseStart_4812798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812798 prefixEnd_4812798 := by exact prefixLift 4812798
  have htrace : WordTrace (prefixWord ++ tailWord_4812798) baseStart_4812798 baseEnd_4812798 := by
    simpa [prefixWord, tailWord_4812798, baseEnd_4812798] using wordTrace_append hprefix tailTrace_4812798
  have hstable : (prefixWord ++ tailWord_4812798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812798).length < 2 ^ (prefixWord ++ tailWord_4812798).sum := by decide
  have hdescent : baseEnd_4812798 < baseStart_4812798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812808 : List Nat := [2, 1, 3, 2, 1, 2, 1, 5, 2, 1, 3]
def baseStart_4812808 : Nat := 118140960795 + 4812808 * 2 ^ 59
def prefixEnd_4812808 : Nat := 4983230072969 + 3 ^ 40 * 4812808 * 2
def baseEnd_4812808 : Nat := 2471283801804111100266305

theorem tailTrace_4812808 : CollatzResearch.WordTrace tailWord_4812808 prefixEnd_4812808 2471283801804111100266305 := by
  unfold tailWord_4812808
  simp only [CollatzResearch.WordTrace]
  refine ⟨87768764374013026505879539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117025019165350702007839385 87768764374013026505879539)
  ·
    refine ⟨131653146561019539758819309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87768764374013026505879539 131653146561019539758819309)
    ·
      refine ⟨49369929960382327409557241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131653146561019539758819309 49369929960382327409557241)
      ·
        refine ⟨37027447470286745557167931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49369929960382327409557241 37027447470286745557167931)
        ·
          refine ⟨55541171205430118335751897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37027447470286745557167931 55541171205430118335751897)
          ·
            refine ⟨41655878404072588751813923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55541171205430118335751897 41655878404072588751813923)
            ·
              refine ⟨62483817606108883127720885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41655878404072588751813923 62483817606108883127720885)
              ·
                refine ⟨5857857900572707793223833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62483817606108883127720885 5857857900572707793223833)
                ·
                  refine ⟨4393393425429530844917875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5857857900572707793223833 4393393425429530844917875)
                  ·
                    refine ⟨6590090138144296267376813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4393393425429530844917875 6590090138144296267376813)
                    ·
                      refine ⟨2471283801804111100266305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6590090138144296267376813 2471283801804111100266305)
                      ·
                        rfl

theorem cell23_4812808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_4812808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812808 prefixEnd_4812808 := by exact prefixLift 4812808
  have htrace : WordTrace (prefixWord ++ tailWord_4812808) baseStart_4812808 baseEnd_4812808 := by
    simpa [prefixWord, tailWord_4812808, baseEnd_4812808] using wordTrace_append hprefix tailTrace_4812808
  have hstable : (prefixWord ++ tailWord_4812808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812808).length < 2 ^ (prefixWord ++ tailWord_4812808).sum := by decide
  have hdescent : baseEnd_4812808 < baseStart_4812808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812824 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 1, 8]
def baseStart_4812824 : Nat := 118140960795 + 4812824 * 2 ^ 59
def prefixEnd_4812824 : Nat := 4983230072969 + 3 ^ 40 * 4812824 * 2
def baseEnd_4812824 : Nat := 823764005831527679222077

theorem tailTrace_4812824 : CollatzResearch.WordTrace tailWord_4812824 prefixEnd_4812824 823764005831527679222077 := by
  unfold tailWord_4812824
  simp only [CollatzResearch.WordTrace]
  refine ⟨87769056157984043872170763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117025408210645391829561017 87769056157984043872170763)
  ·
    refine ⟨131653584236976065808256145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87769056157984043872170763 131653584236976065808256145)
    ·
      refine ⟨98740188177732049356192109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131653584236976065808256145 98740188177732049356192109)
      ·
        refine ⟨37027570566649518508572041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98740188177732049356192109 37027570566649518508572041)
        ·
          refine ⟨27770677924987138881429031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37027570566649518508572041 27770677924987138881429031)
          ·
            refine ⟨41656016887480708322143547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27770677924987138881429031 41656016887480708322143547)
            ·
              refine ⟨62484025331221062483215321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41656016887480708322143547 62484025331221062483215321)
              ·
                refine ⟨46863018998415796862411491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62484025331221062483215321 46863018998415796862411491)
                ·
                  refine ⟨70294528497623695293617237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46863018998415796862411491 70294528497623695293617237)
                  ·
                    refine ⟨823764005831527679222077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70294528497623695293617237 823764005831527679222077)
                    ·
                      rfl

theorem cell23_4812824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_4812824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812824 prefixEnd_4812824 := by exact prefixLift 4812824
  have htrace : WordTrace (prefixWord ++ tailWord_4812824) baseStart_4812824 baseEnd_4812824 := by
    simpa [prefixWord, tailWord_4812824, baseEnd_4812824] using wordTrace_append hprefix tailTrace_4812824
  have hstable : (prefixWord ++ tailWord_4812824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812824).length < 2 ^ (prefixWord ++ tailWord_4812824).sum := by decide
  have hdescent : baseEnd_4812824 < baseStart_4812824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812842 : List Nat := [3, 1, 4, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_4812842 : Nat := 118140960795 + 4812842 * 2 ^ 59
def prefixEnd_4812842 : Nat := 4983230072969 + 3 ^ 40 * 4812842 * 2
def baseEnd_4812842 : Nat := 2471301260146363967241149

theorem tailTrace_4812842 : CollatzResearch.WordTrace tailWord_4812842 prefixEnd_4812842 2471301260146363967241149 := by
  unfold tailWord_4812842
  simp only [CollatzResearch.WordTrace]
  refine ⟨43884692207475719204624195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117025845886601917878997853 43884692207475719204624195)
  ·
    refine ⟨65827038311213578806936293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43884692207475719204624195 65827038311213578806936293)
    ·
      refine ⟨12342569683352546026300555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65827038311213578806936293 12342569683352546026300555)
      ·
        refine ⟨18513854525028819039450833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12342569683352546026300555 18513854525028819039450833)
        ·
          refine ⟨13885390893771614279588125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18513854525028819039450833 13885390893771614279588125)
          ·
            refine ⟨5207021585164355354845547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13885390893771614279588125 5207021585164355354845547)
            ·
              refine ⟨7810532377746533032268321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5207021585164355354845547 7810532377746533032268321)
              ·
                refine ⟨5857899283309899774201241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7810532377746533032268321 5857899283309899774201241)
                ·
                  refine ⟨4393424462482424830650931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5857899283309899774201241 4393424462482424830650931)
                  ·
                    refine ⟨6590136693723637245976397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4393424462482424830650931 6590136693723637245976397)
                    ·
                      refine ⟨2471301260146363967241149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6590136693723637245976397 2471301260146363967241149)
                      ·
                        rfl

theorem cell23_4812842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_4812842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812842 prefixEnd_4812842 := by exact prefixLift 4812842
  have htrace : WordTrace (prefixWord ++ tailWord_4812842) baseStart_4812842 baseEnd_4812842 := by
    simpa [prefixWord, tailWord_4812842, baseEnd_4812842] using wordTrace_append hprefix tailTrace_4812842
  have hstable : (prefixWord ++ tailWord_4812842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812842).length < 2 ^ (prefixWord ++ tailWord_4812842).sum := by decide
  have hdescent : baseEnd_4812842 < baseStart_4812842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812861 : List Nat := [1, 4, 1, 3, 1, 1, 1, 3, 2, 2, 4]
def baseStart_4812861 : Nat := 118140960795 + 4812861 * 2 ^ 59
def prefixEnd_4812861 : Nat := 4983230072969 + 3 ^ 40 * 4812861 * 2
def baseEnd_4812861 : Nat := 2471311016278799392903561

theorem tailTrace_4812861 : CollatzResearch.WordTrace tailWord_4812861 prefixEnd_4812861 2471311016278799392903561 := by
  unfold tailWord_4812861
  simp only [CollatzResearch.WordTrace]
  refine ⟨175539461816834043063438437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117026307877889362042292291 175539461816834043063438437)
  ·
    refine ⟨32913649090656383074394707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175539461816834043063438437 32913649090656383074394707)
    ·
      refine ⟨49370473635984574611592061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32913649090656383074394707 49370473635984574611592061)
      ·
        refine ⟨18513927613494215479347023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49370473635984574611592061 18513927613494215479347023)
        ·
          refine ⟨27770891420241323219020535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18513927613494215479347023 27770891420241323219020535)
          ·
            refine ⟨41656337130361984828530803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27770891420241323219020535 41656337130361984828530803)
            ·
              refine ⟨62484505695542977242796205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41656337130361984828530803 62484505695542977242796205)
              ·
                refine ⟨23431689635828616466048577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62484505695542977242796205 23431689635828616466048577)
                ·
                  refine ⟨17573767226871462349536433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23431689635828616466048577 17573767226871462349536433)
                  ·
                    refine ⟨13180325420153596762152325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17573767226871462349536433 13180325420153596762152325)
                    ·
                      refine ⟨2471311016278799392903561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13180325420153596762152325 2471311016278799392903561)
                      ·
                        rfl

theorem cell23_4812861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_4812861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812861 prefixEnd_4812861 := by exact prefixLift 4812861
  have htrace : WordTrace (prefixWord ++ tailWord_4812861) baseStart_4812861 baseEnd_4812861 := by
    simpa [prefixWord, tailWord_4812861, baseEnd_4812861] using wordTrace_append hprefix tailTrace_4812861
  have hstable : (prefixWord ++ tailWord_4812861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812861).length < 2 ^ (prefixWord ++ tailWord_4812861).sum := by decide
  have hdescent : baseEnd_4812861 < baseStart_4812861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812865 : List Nat := [1, 2, 5, 1, 2, 1, 3, 1, 1, 4, 2]
def baseStart_4812865 : Nat := 118140960795 + 4812865 * 2 ^ 59
def prefixEnd_4812865 : Nat := 4983230072969 + 3 ^ 40 * 4812865 * 2
def baseEnd_4812865 : Nat := 2471313070201417377253543

theorem tailTrace_4812865 : CollatzResearch.WordTrace tailWord_4812865 prefixEnd_4812865 2471313070201417377253543 := by
  unfold tailWord_4812865
  simp only [CollatzResearch.WordTrace]
  refine ⟨175539607708819551746584049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117026405139213034497722699 175539607708819551746584049)
  ·
    refine ⟨131654705781614663809938037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175539607708819551746584049 131654705781614663809938037)
    ·
      refine ⟨12342628667026374732181691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131654705781614663809938037 12342628667026374732181691)
      ·
        refine ⟨18513943000539562098272537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12342628667026374732181691 18513943000539562098272537)
        ·
          refine ⟨13885457250404671573704403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18513943000539562098272537 13885457250404671573704403)
          ·
            refine ⟨20828185875607007360556605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13885457250404671573704403 20828185875607007360556605)
            ·
              refine ⟨7810569703352627760208727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20828185875607007360556605 7810569703352627760208727)
              ·
                refine ⟨11715854555028941640313091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7810569703352627760208727 11715854555028941640313091)
                ·
                  refine ⟨17573781832543412460469637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11715854555028941640313091 17573781832543412460469637)
                  ·
                    refine ⟨3295084093601889836338057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17573781832543412460469637 3295084093601889836338057)
                    ·
                      refine ⟨2471313070201417377253543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3295084093601889836338057 2471313070201417377253543)
                      ·
                        rfl

theorem cell23_4812865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_4812865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812865 prefixEnd_4812865 := by exact prefixLift 4812865
  have htrace : WordTrace (prefixWord ++ tailWord_4812865) baseStart_4812865 baseEnd_4812865 := by
    simpa [prefixWord, tailWord_4812865, baseEnd_4812865] using wordTrace_append hprefix tailTrace_4812865
  have hstable : (prefixWord ++ tailWord_4812865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812865).length < 2 ^ (prefixWord ++ tailWord_4812865).sum := by decide
  have hdescent : baseEnd_4812865 < baseStart_4812865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812888 : List Nat := [2, 1, 2, 2, 1, 4, 3, 3, 5]
def baseStart_4812888 : Nat := 118140960795 + 4812888 * 2 ^ 59
def prefixEnd_4812888 : Nat := 4983230072969 + 3 ^ 40 * 4812888 * 2
def baseEnd_4812888 : Nat := 274591653361830087473993

theorem tailTrace_4812888 : CollatzResearch.WordTrace tailWord_4812888 prefixEnd_4812888 274591653361830087473993 := by
  unfold tailWord_4812888
  simp only [CollatzResearch.WordTrace]
  refine ⟨87770223293868113337335659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117026964391824151116447545 87770223293868113337335659)
  ·
    refine ⟨131655334940802170006003489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87770223293868113337335659 131655334940802170006003489)
    ·
      refine ⟨98741501205601627504502617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131655334940802170006003489 98741501205601627504502617)
      ·
        refine ⟨74056125904201220628376963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98741501205601627504502617 74056125904201220628376963)
        ·
          refine ⟨111084188856301830942565445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74056125904201220628376963 111084188856301830942565445)
          ·
            refine ⟨20828285410556593301731021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111084188856301830942565445 20828285410556593301731021)
            ·
              refine ⟨7810607028958722488149133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20828285410556593301731021 7810607028958722488149133)
              ·
                refine ⟨2928977635859520933055925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7810607028958722488149133 2928977635859520933055925)
                ·
                  refine ⟨274591653361830087473993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2928977635859520933055925 274591653361830087473993)
                  ·
                    rfl

theorem cell23_4812888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 5].length) (baseStart_4812888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812888 prefixEnd_4812888 := by exact prefixLift 4812888
  have htrace : WordTrace (prefixWord ++ tailWord_4812888) baseStart_4812888 baseEnd_4812888 := by
    simpa [prefixWord, tailWord_4812888, baseEnd_4812888] using wordTrace_append hprefix tailTrace_4812888
  have hstable : (prefixWord ++ tailWord_4812888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812888).length < 2 ^ (prefixWord ++ tailWord_4812888).sum := by decide
  have hdescent : baseEnd_4812888 < baseStart_4812888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812901 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 4, 5]
def baseStart_4812901 : Nat := 118140960795 + 4812901 * 2 ^ 59
def prefixEnd_4812901 : Nat := 4983230072969 + 3 ^ 40 * 4812901 * 2
def baseEnd_4812901 : Nat := 823777185168326412134459

theorem tailTrace_4812901 : CollatzResearch.WordTrace tailWord_4812901 prefixEnd_4812901 823777185168326412134459 := by
  unfold tailWord_4812901
  simp only [CollatzResearch.WordTrace]
  refine ⟨175540920736689129894894557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117027280491126086596596371 175540920736689129894894557)
  ·
    refine ⟨65827845276258423710585459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175540920736689129894894557 65827845276258423710585459)
    ·
      refine ⟨98741767914387635565878189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65827845276258423710585459 98741767914387635565878189)
      ·
        refine ⟨37028162967895363337204321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98741767914387635565878189 37028162967895363337204321)
        ·
          refine ⟨27771122225921522502903241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37028162967895363337204321 27771122225921522502903241)
          ·
            refine ⟨20828341669441141877177431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27771122225921522502903241 20828341669441141877177431)
            ·
              refine ⟨31242512504161712815766147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20828341669441141877177431 31242512504161712815766147)
              ·
                refine ⟨46863768756242569223649221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31242512504161712815766147 46863768756242569223649221)
                ·
                  refine ⟨8786956641795481729434229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46863768756242569223649221 8786956641795481729434229)
                  ·
                    refine ⟨823777185168326412134459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8786956641795481729434229 823777185168326412134459)
                    ·
                      rfl

theorem cell23_4812901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 5].length) (baseStart_4812901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812901 prefixEnd_4812901 := by exact prefixLift 4812901
  have htrace : WordTrace (prefixWord ++ tailWord_4812901) baseStart_4812901 baseEnd_4812901 := by
    simpa [prefixWord, tailWord_4812901, baseEnd_4812901] using wordTrace_append hprefix tailTrace_4812901
  have hstable : (prefixWord ++ tailWord_4812901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812901).length < 2 ^ (prefixWord ++ tailWord_4812901).sum := by decide
  have hdescent : baseEnd_4812901 < baseStart_4812901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812911 : List Nat := [1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 5]
def baseStart_4812911 : Nat := 118140960795 + 4812911 * 2 ^ 59
def prefixEnd_4812911 : Nat := 4983230072969 + 3 ^ 40 * 4812911 * 2
def baseEnd_4812911 : Nat := 2471336690311524197278331

theorem tailTrace_4812911 : CollatzResearch.WordTrace tailWord_4812911 prefixEnd_4812911 2471336690311524197278331 := by
  unfold tailWord_4812911
  simp only [CollatzResearch.WordTrace]
  refine ⟨175541285466652901602758587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117027523644435267735172391 175541285466652901602758587)
  ·
    refine ⟨263311928199979352404137881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175541285466652901602758587 263311928199979352404137881)
    ·
      refine ⟨197483946149984514303103411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263311928199979352404137881 197483946149984514303103411)
      ·
        refine ⟨296225919224976771454655117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197483946149984514303103411 296225919224976771454655117)
        ·
          refine ⟨111084719709366289295495669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 296225919224976771454655117 111084719709366289295495669)
          ·
            refine ⟨10414192472753089621452719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111084719709366289295495669 10414192472753089621452719)
            ·
              refine ⟨15621288709129634432179079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10414192472753089621452719 15621288709129634432179079)
              ·
                refine ⟨23431933063694451648268619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15621288709129634432179079 23431933063694451648268619)
                ·
                  refine ⟨35147899595541677472402929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23431933063694451648268619 35147899595541677472402929)
                  ·
                    refine ⟨26360924696656258104302197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35147899595541677472402929 26360924696656258104302197)
                    ·
                      refine ⟨2471336690311524197278331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26360924696656258104302197 2471336690311524197278331)
                      ·
                        rfl

theorem cell23_4812911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 5].length) (baseStart_4812911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812911 prefixEnd_4812911 := by exact prefixLift 4812911
  have htrace : WordTrace (prefixWord ++ tailWord_4812911) baseStart_4812911 baseEnd_4812911 := by
    simpa [prefixWord, tailWord_4812911, baseEnd_4812911] using wordTrace_append hprefix tailTrace_4812911
  have hstable : (prefixWord ++ tailWord_4812911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812911).length < 2 ^ (prefixWord ++ tailWord_4812911).sum := by decide
  have hdescent : baseEnd_4812911 < baseStart_4812911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812938 : List Nat := [3, 1, 2, 3, 1, 2, 1, 3, 2, 1, 4]
def baseStart_4812938 : Nat := 118140960795 + 4812938 * 2 ^ 59
def prefixEnd_4812938 : Nat := 4983230072969 + 3 ^ 40 * 4812938 * 2
def baseEnd_4812938 : Nat := 2471350554289195591640707

theorem tailTrace_4812938 : CollatzResearch.WordTrace tailWord_4812938 prefixEnd_4812938 2471350554289195591640707 := by
  unfold tailWord_4812938
  simp only [CollatzResearch.WordTrace]
  refine ⟨43885567559388771303497867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117028180158370056809327645 43885567559388771303497867)
  ·
    refine ⟨65828351339083156955246801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43885567559388771303497867 65828351339083156955246801)
    ·
      refine ⟨49371263504312367716435101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65828351339083156955246801 49371263504312367716435101)
      ·
        refine ⟨18514223814117137893663163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49371263504312367716435101 18514223814117137893663163)
        ·
          refine ⟨27771335721175706840494745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18514223814117137893663163 27771335721175706840494745)
          ·
            refine ⟨20828501790881780130371059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27771335721175706840494745 20828501790881780130371059)
            ·
              refine ⟨31242752686322670195556589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20828501790881780130371059 31242752686322670195556589)
              ·
                refine ⟨11716032257371001323333721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31242752686322670195556589 11716032257371001323333721)
                ·
                  refine ⟨8787024193028250992500291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11716032257371001323333721 8787024193028250992500291)
                  ·
                    refine ⟨13180536289542376488750437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8787024193028250992500291 13180536289542376488750437)
                    ·
                      refine ⟨2471350554289195591640707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13180536289542376488750437 2471350554289195591640707)
                      ·
                        rfl

theorem cell23_4812938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_4812938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812938 prefixEnd_4812938 := by exact prefixLift 4812938
  have htrace : WordTrace (prefixWord ++ tailWord_4812938) baseStart_4812938 baseEnd_4812938 := by
    simpa [prefixWord, tailWord_4812938, baseEnd_4812938] using wordTrace_append hprefix tailTrace_4812938
  have hstable : (prefixWord ++ tailWord_4812938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812938).length < 2 ^ (prefixWord ++ tailWord_4812938).sum := by decide
  have hdescent : baseEnd_4812938 < baseStart_4812938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812950 : List Nat := [5, 3, 2, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_4812950 : Nat := 118140960795 + 4812950 * 2 ^ 59
def prefixEnd_4812950 : Nat := 4983230072969 + 3 ^ 40 * 4812950 * 2
def baseEnd_4812950 : Nat := 2471356716057049544690653

theorem tailTrace_4812950 : CollatzResearch.WordTrace tailWord_4812950 prefixEnd_4812950 2471356716057049544690653 := by
  unfold tailWord_4812950
  simp only [CollatzResearch.WordTrace]
  refine ⟨10971419244594475703964269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117028471942341074175618869 10971419244594475703964269)
  ·
    refine ⟨4114282216722928388986601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10971419244594475703964269 4114282216722928388986601)
    ·
      refine ⟨3085711662542196291739951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4114282216722928388986601 3085711662542196291739951)
      ·
        refine ⟨4628567493813294437609927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3085711662542196291739951 4628567493813294437609927)
        ·
          refine ⟨6942851240719941656414891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4628567493813294437609927 6942851240719941656414891)
          ·
            refine ⟨10414276861079912484622337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6942851240719941656414891 10414276861079912484622337)
            ·
              refine ⟨7810707645809934363466753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10414276861079912484622337 7810707645809934363466753)
              ·
                refine ⟨5858030734357450772600065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7810707645809934363466753 5858030734357450772600065)
                ·
                  refine ⟨4393523050768088079450049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5858030734357450772600065 4393523050768088079450049)
                  ·
                    refine ⟨3295142288076066059587537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4393523050768088079450049 3295142288076066059587537)
                    ·
                      refine ⟨2471356716057049544690653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3295142288076066059587537 2471356716057049544690653)
                      ·
                        rfl

theorem cell23_4812950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_4812950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812950 prefixEnd_4812950 := by exact prefixLift 4812950
  have htrace : WordTrace (prefixWord ++ tailWord_4812950) baseStart_4812950 baseEnd_4812950 := by
    simpa [prefixWord, tailWord_4812950, baseEnd_4812950] using wordTrace_append hprefix tailTrace_4812950
  have hstable : (prefixWord ++ tailWord_4812950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812950).length < 2 ^ (prefixWord ++ tailWord_4812950).sum := by decide
  have hdescent : baseEnd_4812950 < baseStart_4812950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4812965 : List Nat := [1, 3, 1, 2, 1, 3, 3, 4, 1, 4]
def baseStart_4812965 : Nat := 118140960795 + 4812965 * 2 ^ 59
def prefixEnd_4812965 : Nat := 4983230072969 + 3 ^ 40 * 4812965 * 2
def baseEnd_4812965 : Nat := 823788139422288995334361

theorem tailTrace_4812965 : CollatzResearch.WordTrace tailWord_4812965 prefixEnd_4812965 823788139422288995334361 := by
  unfold tailWord_4812965
  simp only [CollatzResearch.WordTrace]
  refine ⟨175543255008457268825224349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117028836672304845883482899 175543255008457268825224349)
  ·
    refine ⟨65828720628171475809459131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175543255008457268825224349 65828720628171475809459131)
    ·
      refine ⟨98743080942257213714188697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65828720628171475809459131 98743080942257213714188697)
      ·
        refine ⟨74057310706692910285641523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98743080942257213714188697 74057310706692910285641523)
        ·
          refine ⟨111085966060039365428462285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74057310706692910285641523 111085966060039365428462285)
          ·
            refine ⟨41657237272514762035673357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111085966060039365428462285 41657237272514762035673357)
            ·
              refine ⟨15621463977193035763377509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41657237272514762035673357 15621463977193035763377509)
              ·
                refine ⟨2929024495723694205633283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15621463977193035763377509 2929024495723694205633283)
                ·
                  refine ⟨4393536743585541308449925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2929024495723694205633283 4393536743585541308449925)
                  ·
                    refine ⟨823788139422288995334361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4393536743585541308449925 823788139422288995334361)
                    ·
                      rfl

theorem cell23_4812965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 1, 4].length) (baseStart_4812965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4812965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4812965 prefixEnd_4812965 := by exact prefixLift 4812965
  have htrace : WordTrace (prefixWord ++ tailWord_4812965) baseStart_4812965 baseEnd_4812965 := by
    simpa [prefixWord, tailWord_4812965, baseEnd_4812965] using wordTrace_append hprefix tailTrace_4812965
  have hstable : (prefixWord ++ tailWord_4812965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4812965).length < 2 ^ (prefixWord ++ tailWord_4812965).sum := by decide
  have hdescent : baseEnd_4812965 < baseStart_4812965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4812965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813048 : List Nat := [2, 1, 2, 1, 1, 2, 1, 5, 3, 2, 3]
def baseStart_4813048 : Nat := 118140960795 + 4813048 * 2 ^ 59
def prefixEnd_4813048 : Nat := 4983230072969 + 3 ^ 40 * 4813048 * 2
def baseEnd_4813048 : Nat := 2471407037161190161265201

theorem tailTrace_4813048 : CollatzResearch.WordTrace tailWord_4813048 prefixEnd_4813048 2471407037161190161265201 := by
  unfold tailWord_4813048
  simp only [CollatzResearch.WordTrace]
  refine ⟨87773141133578287000247899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117030854844771049333663865 87773141133578287000247899)
  ·
    refine ⟨131659711700367430500371849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87773141133578287000247899 131659711700367430500371849)
    ·
      refine ⟨98744783775275572875278887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131659711700367430500371849 98744783775275572875278887)
      ·
        refine ⟨148117175662913359312918331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98744783775275572875278887 148117175662913359312918331)
        ·
          refine ⟨222175763494370038969377497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148117175662913359312918331 222175763494370038969377497)
          ·
            refine ⟨166631822620777529227033123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222175763494370038969377497 166631822620777529227033123)
            ·
              refine ⟨249947733931166293840549685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166631822620777529227033123 249947733931166293840549685)
              ·
                refine ⟨23432600056046840047551533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 249947733931166293840549685 23432600056046840047551533)
                ·
                  refine ⟨8787225021017565017831825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23432600056046840047551533 8787225021017565017831825)
                  ·
                    refine ⟨6590418765763173763373869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8787225021017565017831825 6590418765763173763373869)
                    ·
                      refine ⟨2471407037161190161265201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6590418765763173763373869 2471407037161190161265201)
                      ·
                        rfl

theorem cell23_4813048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 3, 2, 3].length) (baseStart_4813048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813048 prefixEnd_4813048 := by exact prefixLift 4813048
  have htrace : WordTrace (prefixWord ++ tailWord_4813048) baseStart_4813048 baseEnd_4813048 := by
    simpa [prefixWord, tailWord_4813048, baseEnd_4813048] using wordTrace_append hprefix tailTrace_4813048
  have hstable : (prefixWord ++ tailWord_4813048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813048).length < 2 ^ (prefixWord ++ tailWord_4813048).sum := by decide
  have hdescent : baseEnd_4813048 < baseStart_4813048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813065 : List Nat := [1, 2, 1, 1, 3, 4, 2, 3, 1, 2, 3]
def baseStart_4813065 : Nat := 118140960795 + 4813065 * 2 ^ 59
def prefixEnd_4813065 : Nat := 4983230072969 + 3 ^ 40 * 4813065 * 2
def baseEnd_4813065 : Nat := 2471415766332316594752623

theorem tailTrace_4813065 : CollatzResearch.WordTrace tailWord_4813065 prefixEnd_4813065 2471415766332316594752623 := by
  unfold tailWord_4813065
  simp only [CollatzResearch.WordTrace]
  refine ⟨175546902308094985903864649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117031268205396657269243099 175546902308094985903864649)
  ·
    refine ⟨131660176731071239427898487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175546902308094985903864649 131660176731071239427898487)
    ·
      refine ⟨197490265096606859141847731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131660176731071239427898487 197490265096606859141847731)
      ·
        refine ⟨296235397644910288712771597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197490265096606859141847731 296235397644910288712771597)
        ·
          refine ⟨111088274116841358267289349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 296235397644910288712771597 111088274116841358267289349)
          ·
            refine ⟨20829051396907754675116753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111088274116841358267289349 20829051396907754675116753)
            ·
              refine ⟨15621788547680816006337565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20829051396907754675116753 15621788547680816006337565)
              ·
                refine ⟨5858170705380306002376587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15621788547680816006337565 5858170705380306002376587)
                ·
                  refine ⟨8787256058070459003564881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5858170705380306002376587 8787256058070459003564881)
                  ·
                    refine ⟨6590442043552844252673661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8787256058070459003564881 6590442043552844252673661)
                    ·
                      refine ⟨2471415766332316594752623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6590442043552844252673661 2471415766332316594752623)
                      ·
                        rfl

theorem cell23_4813065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 2, 3].length) (baseStart_4813065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813065 prefixEnd_4813065 := by exact prefixLift 4813065
  have htrace : WordTrace (prefixWord ++ tailWord_4813065) baseStart_4813065 baseEnd_4813065 := by
    simpa [prefixWord, tailWord_4813065, baseEnd_4813065] using wordTrace_append hprefix tailTrace_4813065
  have hstable : (prefixWord ++ tailWord_4813065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813065).length < 2 ^ (prefixWord ++ tailWord_4813065).sum := by decide
  have hdescent : baseEnd_4813065 < baseStart_4813065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813079 : List Nat := [1, 1, 3, 4, 1, 4, 1, 1, 3, 2, 2]
def baseStart_4813079 : Nat := 118140960795 + 4813079 * 2 ^ 59
def prefixEnd_4813079 : Nat := 4983230072969 + 3 ^ 40 * 4813079 * 2
def baseEnd_4813079 : Nat := 2471422955061479539977559

theorem tailTrace_4813079 : CollatzResearch.WordTrace tailWord_4813079 prefixEnd_4813079 2471422955061479539977559 := by
  unfold tailWord_4813079
  simp only [CollatzResearch.WordTrace]
  refine ⟨175547412930044266294874291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117031608620029510863249527 175547412930044266294874291)
  ·
    refine ⟨263321119395066399442311437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175547412930044266294874291 263321119395066399442311437)
    ·
      refine ⟨98745419773149899790866789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263321119395066399442311437 98745419773149899790866789)
      ·
        refine ⟨18514766207465606210787523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98745419773149899790866789 18514766207465606210787523)
        ·
          refine ⟨27772149311198409316181285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18514766207465606210787523 27772149311198409316181285)
          ·
            refine ⟨5207277995849701746783991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27772149311198409316181285 5207277995849701746783991)
            ·
              refine ⟨7810916993774552620175987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5207277995849701746783991 7810916993774552620175987)
              ·
                refine ⟨11716375490661828930263981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7810916993774552620175987 11716375490661828930263981)
                ·
                  refine ⟨4393640808998185848848993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11716375490661828930263981 4393640808998185848848993)
                  ·
                    refine ⟨3295230606748639386636745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4393640808998185848848993 3295230606748639386636745)
                    ·
                      refine ⟨2471422955061479539977559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3295230606748639386636745 2471422955061479539977559)
                      ·
                        rfl

theorem cell23_4813079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_4813079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813079 prefixEnd_4813079 := by exact prefixLift 4813079
  have htrace : WordTrace (prefixWord ++ tailWord_4813079) baseStart_4813079 baseEnd_4813079 := by
    simpa [prefixWord, tailWord_4813079, baseEnd_4813079] using wordTrace_append hprefix tailTrace_4813079
  have hstable : (prefixWord ++ tailWord_4813079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813079).length < 2 ^ (prefixWord ++ tailWord_4813079).sum := by decide
  have hdescent : baseEnd_4813079 < baseStart_4813079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813085 : List Nat := [1, 4, 2, 3, 2, 1, 2, 8]
def baseStart_4813085 : Nat := 118140960795 + 4813085 * 2 ^ 59
def prefixEnd_4813085 : Nat := 4983230072969 + 3 ^ 40 * 4813085 * 2
def baseEnd_4813085 : Nat := 91534297627607648759353

theorem tailTrace_4813085 : CollatzResearch.WordTrace tailWord_4813085 prefixEnd_4813085 91534297627607648759353 := by
  unfold tailWord_4813085
  simp only [CollatzResearch.WordTrace]
  refine ⟨175547631768022529319592709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117031754512015019546395139 175547631768022529319592709)
  ·
    refine ⟨32915180956504224247423633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175547631768022529319592709 32915180956504224247423633)
    ·
      refine ⟨24686385717378168185567725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32915180956504224247423633 24686385717378168185567725)
      ·
        refine ⟨9257394644016813069587897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24686385717378168185567725 9257394644016813069587897)
        ·
          refine ⟨6943045983012609802190923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9257394644016813069587897 6943045983012609802190923)
          ·
            refine ⟨10414568974518914703286385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6943045983012609802190923 10414568974518914703286385)
            ·
              refine ⟨7810926730889186027464789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10414568974518914703286385 7810926730889186027464789)
              ·
                refine ⟨91534297627607648759353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7810926730889186027464789 91534297627607648759353)
                ·
                  rfl

theorem cell23_4813085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 8].length) (baseStart_4813085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813085 prefixEnd_4813085 := by exact prefixLift 4813085
  have htrace : WordTrace (prefixWord ++ tailWord_4813085) baseStart_4813085 baseEnd_4813085 := by
    simpa [prefixWord, tailWord_4813085, baseEnd_4813085] using wordTrace_append hprefix tailTrace_4813085
  have hstable : (prefixWord ++ tailWord_4813085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813085).length < 2 ^ (prefixWord ++ tailWord_4813085).sum := by decide
  have hdescent : baseEnd_4813085 < baseStart_4813085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813138 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_4813138 : Nat := 118140960795 + 4813138 * 2 ^ 59
def prefixEnd_4813138 : Nat := 4983230072969 + 3 ^ 40 * 4813138 * 2
def baseEnd_4813138 : Nat := 2471453250420094809139787

theorem tailTrace_4813138 : CollatzResearch.WordTrace tailWord_4813138 prefixEnd_4813138 2471453250420094809139787 := by
  unfold tailWord_4813138
  simp only [CollatzResearch.WordTrace]
  refine ⟨43887391209207629842818017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117033043224553679580848045 43887391209207629842818017)
  ·
    refine ⟨32915543406905722382113513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43887391209207629842818017 32915543406905722382113513)
    ·
      refine ⟨24686657555179291786585135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32915543406905722382113513 24686657555179291786585135)
      ·
        refine ⟨37029986332768937679877703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24686657555179291786585135 37029986332768937679877703)
        ·
          refine ⟨55544979499153406519816555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37029986332768937679877703 55544979499153406519816555)
          ·
            refine ⟨83317469248730109779724833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55544979499153406519816555 83317469248730109779724833)
            ·
              refine ⟨62488101936547582334793625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83317469248730109779724833 62488101936547582334793625)
              ·
                refine ⟨46866076452410686751095219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62488101936547582334793625 46866076452410686751095219)
                ·
                  refine ⟨70299114678616030126642829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46866076452410686751095219 70299114678616030126642829)
                  ·
                    refine ⟨26362168004481011297491061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70299114678616030126642829 26362168004481011297491061)
                    ·
                      refine ⟨2471453250420094809139787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26362168004481011297491061 2471453250420094809139787)
                      ·
                        rfl

theorem cell23_4813138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_4813138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813138 prefixEnd_4813138 := by exact prefixLift 4813138
  have htrace : WordTrace (prefixWord ++ tailWord_4813138) baseStart_4813138 baseEnd_4813138 := by
    simpa [prefixWord, tailWord_4813138, baseEnd_4813138] using wordTrace_append hprefix tailTrace_4813138
  have hstable : (prefixWord ++ tailWord_4813138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813138).length < 2 ^ (prefixWord ++ tailWord_4813138).sum := by decide
  have hdescent : baseEnd_4813138 < baseStart_4813138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813225 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 1, 6, 2]
def baseStart_4813225 : Nat := 118140960795 + 4813225 * 2 ^ 59
def prefixEnd_4813225 : Nat := 4983230072969 + 3 ^ 40 * 4813225 * 2
def baseEnd_4813225 : Nat := 2471497923237035968751887

theorem tailTrace_4813225 : CollatzResearch.WordTrace tailWord_4813225 prefixEnd_4813225 2471497923237035968751887 := by
  unfold tailWord_4813225
  simp only [CollatzResearch.WordTrace]
  refine ⟨175552737987515333229689129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117035158658343555486459419 175552737987515333229689129)
  ·
    refine ⟨131664553490636499922266847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175552737987515333229689129 131664553490636499922266847)
    ·
      refine ⟨197496830235954749883400271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131664553490636499922266847 197496830235954749883400271)
      ·
        refine ⟨296245245353932124825100407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197496830235954749883400271 296245245353932124825100407)
        ·
          refine ⟨444367868030898187237650611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296245245353932124825100407 444367868030898187237650611)
          ·
            refine ⟨666551802046347280856475917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444367868030898187237650611 666551802046347280856475917)
            ·
              refine ⟨249956925767380230321178469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 666551802046347280856475917 249956925767380230321178469)
              ·
                refine ⟨46866923581383793185220963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 249956925767380230321178469 46866923581383793185220963)
                ·
                  refine ⟨70300385372075689777831445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46866923581383793185220963 70300385372075689777831445)
                  ·
                    refine ⟨3295330564316047958335849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70300385372075689777831445 3295330564316047958335849)
                    ·
                      refine ⟨2471497923237035968751887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3295330564316047958335849 2471497923237035968751887)
                      ·
                        rfl

theorem cell23_4813225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 6, 2].length) (baseStart_4813225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813225 prefixEnd_4813225 := by exact prefixLift 4813225
  have htrace : WordTrace (prefixWord ++ tailWord_4813225) baseStart_4813225 baseEnd_4813225 := by
    simpa [prefixWord, tailWord_4813225, baseEnd_4813225] using wordTrace_append hprefix tailTrace_4813225
  have hstable : (prefixWord ++ tailWord_4813225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813225).length < 2 ^ (prefixWord ++ tailWord_4813225).sum := by decide
  have hdescent : baseEnd_4813225 < baseStart_4813225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813228 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 5]
def baseStart_4813228 : Nat := 118140960795 + 4813228 * 2 ^ 59
def prefixEnd_4813228 : Nat := 4983230072969 + 3 ^ 40 * 4813228 * 2
def baseEnd_4813228 : Nat := 2471499463678999457014373

theorem tailTrace_4813228 : CollatzResearch.WordTrace tailWord_4813228 prefixEnd_4813228 2471499463678999457014373 := by
  unfold tailWord_4813228
  simp only [CollatzResearch.WordTrace]
  refine ⟨87776423703252232371024169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117035231604336309828032225 87776423703252232371024169)
  ·
    refine ⟨65832317777439174278268127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87776423703252232371024169 65832317777439174278268127)
    ·
      refine ⟨98748476666158761417402191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65832317777439174278268127 98748476666158761417402191)
      ·
        refine ⟨148122714999238142126103287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98748476666158761417402191 148122714999238142126103287)
        ·
          refine ⟨222184072498857213189154931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148122714999238142126103287 222184072498857213189154931)
          ·
            refine ⟨333276108748285819783732397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222184072498857213189154931 333276108748285819783732397)
            ·
              refine ⟨124978540780607182418899649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 333276108748285819783732397 124978540780607182418899649)
              ·
                refine ⟨93733905585455386814174737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124978540780607182418899649 93733905585455386814174737)
                ·
                  refine ⟨70300429189091540110631053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93733905585455386814174737 70300429189091540110631053)
                  ·
                    refine ⟨26362660945909327541486645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70300429189091540110631053 26362660945909327541486645)
                    ·
                      refine ⟨2471499463678999457014373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26362660945909327541486645 2471499463678999457014373)
                      ·
                        rfl

theorem cell23_4813228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_4813228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813228 prefixEnd_4813228 := by exact prefixLift 4813228
  have htrace : WordTrace (prefixWord ++ tailWord_4813228) baseStart_4813228 baseEnd_4813228 := by
    simpa [prefixWord, tailWord_4813228, baseEnd_4813228] using wordTrace_append hprefix tailTrace_4813228
  have hstable : (prefixWord ++ tailWord_4813228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813228).length < 2 ^ (prefixWord ++ tailWord_4813228).sum := by decide
  have hdescent : baseEnd_4813228 < baseStart_4813228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813315 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 4]
def baseStart_4813315 : Nat := 118140960795 + 4813315 * 2 ^ 59
def prefixEnd_4813315 : Nat := 4983230072969 + 3 ^ 40 * 4813315 * 2
def baseEnd_4813315 : Nat := 2471544136495940616626473

theorem tailTrace_4813315 : CollatzResearch.WordTrace tailWord_4813315 prefixEnd_4813315 2471544136495940616626473 := by
  unfold tailWord_4813315
  simp only [CollatzResearch.WordTrace]
  refine ⟨175556020557189278600465399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117037347038126185733643599 175556020557189278600465399)
  ·
    refine ⟨263334030835783917900698099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175556020557189278600465399 263334030835783917900698099)
    ·
      refine ⟨395001046253675876851047149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263334030835783917900698099 395001046253675876851047149)
      ·
        refine ⟨148125392345128453819142681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 395001046253675876851047149 148125392345128453819142681)
        ·
          refine ⟨111094044258846340364357011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148125392345128453819142681 111094044258846340364357011)
          ·
            refine ⟨166641066388269510546535517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111094044258846340364357011 166641066388269510546535517)
            ·
              refine ⟨62490399895601066454950819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166641066388269510546535517 62490399895601066454950819)
              ·
                refine ⟨93735599843401599682426229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62490399895601066454950819 93735599843401599682426229)
                ·
                  refine ⟨8787712485318899970227459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93735599843401599682426229 8787712485318899970227459)
                  ·
                    refine ⟨13181568727978349955341189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8787712485318899970227459 13181568727978349955341189)
                    ·
                      refine ⟨2471544136495940616626473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13181568727978349955341189 2471544136495940616626473)
                      ·
                        rfl

theorem cell23_4813315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_4813315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813315 prefixEnd_4813315 := by exact prefixLift 4813315
  have htrace : WordTrace (prefixWord ++ tailWord_4813315) baseStart_4813315 baseEnd_4813315 := by
    simpa [prefixWord, tailWord_4813315, baseEnd_4813315] using wordTrace_append hprefix tailTrace_4813315
  have hstable : (prefixWord ++ tailWord_4813315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813315).length < 2 ^ (prefixWord ++ tailWord_4813315).sum := by decide
  have hdescent : baseEnd_4813315 < baseStart_4813315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813336 : List Nat := [2, 1, 2, 3, 3, 3, 1, 1, 2, 3, 2]
def baseStart_4813336 : Nat := 118140960795 + 4813336 * 2 ^ 59
def prefixEnd_4813336 : Nat := 4983230072969 + 3 ^ 40 * 4813336 * 2
def baseEnd_4813336 : Nat := 2471554919589685034463877

theorem tailTrace_4813336 : CollatzResearch.WordTrace tailWord_4813336 prefixEnd_4813336 2471554919589685034463877 := by
  unfold tailWord_4813336
  simp only [CollatzResearch.WordTrace]
  refine ⟨87778393245056599593489931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117037857660075466124653241 87778393245056599593489931)
  ·
    refine ⟨131667589867584899390234897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87778393245056599593489931 131667589867584899390234897)
    ·
      refine ⟨98750692400688674542676173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131667589867584899390234897 98750692400688674542676173)
      ·
        refine ⟨37031509650258252953503565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98750692400688674542676173 37031509650258252953503565)
        ·
          refine ⟨13886816118846844857563837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37031509650258252953503565 13886816118846844857563837)
          ·
            refine ⟨5207556044567566821586439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13886816118846844857563837 5207556044567566821586439)
            ·
              refine ⟨7811334066851350232379659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5207556044567566821586439 7811334066851350232379659)
              ·
                refine ⟨11717001100277025348569489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7811334066851350232379659 11717001100277025348569489)
                ·
                  refine ⟨8787750825207769011427117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11717001100277025348569489 8787750825207769011427117)
                  ·
                    refine ⟨3295406559452913379285169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8787750825207769011427117 3295406559452913379285169)
                    ·
                      refine ⟨2471554919589685034463877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3295406559452913379285169 2471554919589685034463877)
                      ·
                        rfl

theorem cell23_4813336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_4813336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813336 prefixEnd_4813336 := by exact prefixLift 4813336
  have htrace : WordTrace (prefixWord ++ tailWord_4813336) baseStart_4813336 baseEnd_4813336 := by
    simpa [prefixWord, tailWord_4813336, baseEnd_4813336] using wordTrace_append hprefix tailTrace_4813336
  have hstable : (prefixWord ++ tailWord_4813336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813336).length < 2 ^ (prefixWord ++ tailWord_4813336).sum := by decide
  have hdescent : baseEnd_4813336 < baseStart_4813336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813349 : List Nat := [1, 3, 1, 2, 2, 1, 6, 1, 1, 1, 4]
def baseStart_4813349 : Nat := 118140960795 + 4813349 * 2 ^ 59
def prefixEnd_4813349 : Nat := 4983230072969 + 3 ^ 40 * 4813349 * 2
def baseEnd_4813349 : Nat := 2471561594838193483601317

theorem tailTrace_4813349 : CollatzResearch.WordTrace tailWord_4813349 prefixEnd_4813349 2471561594838193483601317 := by
  unfold tailWord_4813349
  simp only [CollatzResearch.WordTrace]
  refine ⟨175557260639066102407203101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117038173759377401604802067 175557260639066102407203101)
  ·
    refine ⟨65833972739649788402701163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175557260639066102407203101 65833972739649788402701163)
    ·
      refine ⟨98750959109474682604051745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65833972739649788402701163 98750959109474682604051745)
      ·
        refine ⟨74063219332106011953038809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98750959109474682604051745 74063219332106011953038809)
        ·
          refine ⟨55547414499079508964779107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74063219332106011953038809 55547414499079508964779107)
          ·
            refine ⟨83321121748619263447168661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55547414499079508964779107 83321121748619263447168661)
            ·
              refine ⟨3905677581966527974086031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83321121748619263447168661 3905677581966527974086031)
              ·
                refine ⟨5858516372949791961129047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3905677581966527974086031 5858516372949791961129047)
                ·
                  refine ⟨8787774559424687941693571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5858516372949791961129047 8787774559424687941693571)
                  ·
                    refine ⟨13181661839137031912540357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8787774559424687941693571 13181661839137031912540357)
                    ·
                      refine ⟨2471561594838193483601317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13181661839137031912540357 2471561594838193483601317)
                      ·
                        rfl

theorem cell23_4813349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 1, 1, 4].length) (baseStart_4813349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813349 prefixEnd_4813349 := by exact prefixLift 4813349
  have htrace : WordTrace (prefixWord ++ tailWord_4813349) baseStart_4813349 baseEnd_4813349 := by
    simpa [prefixWord, tailWord_4813349, baseEnd_4813349] using wordTrace_append hprefix tailTrace_4813349
  have hstable : (prefixWord ++ tailWord_4813349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813349).length < 2 ^ (prefixWord ++ tailWord_4813349).sum := by decide
  have hdescent : baseEnd_4813349 < baseStart_4813349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813389 : List Nat := [1, 6, 1, 1, 2, 1, 4, 7]
def baseStart_4813389 : Nat := 118140960795 + 4813389 * 2 ^ 59
def prefixEnd_4813389 : Nat := 4983230072969 + 3 ^ 40 * 4813389 * 2
def baseEnd_4813389 : Nat := 91540079039421234337079

theorem tailTrace_4813389 : CollatzResearch.WordTrace tailWord_4813389 prefixEnd_4813389 91540079039421234337079 := by
  unfold tailWord_4813389
  simp only [CollatzResearch.WordTrace]
  refine ⟨175558719558921189238659221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117039146372614126159106147 175558719558921189238659221)
  ·
    refine ⟨8229314979324430745562151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 175558719558921189238659221 8229314979324430745562151)
    ·
      refine ⟨12343972468986646118343227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8229314979324430745562151 12343972468986646118343227)
      ·
        refine ⟨18515958703479969177514841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12343972468986646118343227 18515958703479969177514841)
        ·
          refine ⟨13886969027609976883136131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18515958703479969177514841 13886969027609976883136131)
          ·
            refine ⟨20830453541414965324704197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13886969027609976883136131 20830453541414965324704197)
            ·
              refine ⟨3905710039015305998382037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20830453541414965324704197 3905710039015305998382037)
              ·
                refine ⟨91540079039421234337079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3905710039015305998382037 91540079039421234337079)
                ·
                  rfl

theorem cell23_4813389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 7].length) (baseStart_4813389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813389 prefixEnd_4813389 := by exact prefixLift 4813389
  have htrace : WordTrace (prefixWord ++ tailWord_4813389) baseStart_4813389 baseEnd_4813389 := by
    simpa [prefixWord, tailWord_4813389, baseEnd_4813389] using wordTrace_append hprefix tailTrace_4813389
  have hstable : (prefixWord ++ tailWord_4813389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813389).length < 2 ^ (prefixWord ++ tailWord_4813389).sum := by decide
  have hdescent : baseEnd_4813389 < baseStart_4813389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813433 : List Nat := [1, 2, 1, 3, 3, 4, 2, 1, 2, 1, 3]
def baseStart_4813433 : Nat := 118140960795 + 4813433 * 2 ^ 59
def prefixEnd_4813433 : Nat := 4983230072969 + 3 ^ 40 * 4813433 * 2
def baseEnd_4813433 : Nat := 2471604727213171154950931

theorem tailTrace_4813433 : CollatzResearch.WordTrace tailWord_4813433 prefixEnd_4813433 2471604727213171154950931 := by
  unfold tailWord_4813433
  simp only [CollatzResearch.WordTrace]
  refine ⟨175560324370761784753260953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117040216247174523168840635 175560324370761784753260953)
  ·
    refine ⟨131670243278071338564945715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175560324370761784753260953 131670243278071338564945715)
    ·
      refine ⟨197505364917107007847418573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131670243278071338564945715 197505364917107007847418573)
      ·
        refine ⟨74064511843915127942781965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197505364917107007847418573 74064511843915127942781965)
        ·
          refine ⟨27774191941468172978543237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74064511843915127942781965 27774191941468172978543237)
          ·
            refine ⟨5207660989025282433476857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27774191941468172978543237 5207660989025282433476857)
            ·
              refine ⟨3905745741768961825107643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5207660989025282433476857 3905745741768961825107643)
              ·
                refine ⟨5858618612653442737661465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3905745741768961825107643 5858618612653442737661465)
                ·
                  refine ⟨4393963959490082053246099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5858618612653442737661465 4393963959490082053246099)
                  ·
                    refine ⟨6590945939235123079869149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4393963959490082053246099 6590945939235123079869149)
                    ·
                      refine ⟨2471604727213171154950931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6590945939235123079869149 2471604727213171154950931)
                      ·
                        rfl

theorem cell23_4813433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 2, 1, 3].length) (baseStart_4813433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813433 prefixEnd_4813433 := by exact prefixLift 4813433
  have htrace : WordTrace (prefixWord ++ tailWord_4813433) baseStart_4813433 baseEnd_4813433 := by
    simpa [prefixWord, tailWord_4813433, baseEnd_4813433] using wordTrace_append hprefix tailTrace_4813433
  have hstable : (prefixWord ++ tailWord_4813433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813433).length < 2 ^ (prefixWord ++ tailWord_4813433).sum := by decide
  have hdescent : baseEnd_4813433 < baseStart_4813433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813439 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 6, 2, 2]
def baseStart_4813439 : Nat := 118140960795 + 4813439 * 2 ^ 59
def prefixEnd_4813439 : Nat := 4983230072969 + 3 ^ 40 * 4813439 * 2
def baseEnd_4813439 : Nat := 2471607808097098131475903

theorem tailTrace_4813439 : CollatzResearch.WordTrace tailWord_4813439 prefixEnd_4813439 2471607808097098131475903 := by
  unfold tailWord_4813439
  simp only [CollatzResearch.WordTrace]
  refine ⟨175560543208740047777979371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117040362139160031851986247 175560543208740047777979371)
  ·
    refine ⟨263340814813110071666969057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175560543208740047777979371 263340814813110071666969057)
    ·
      refine ⟨197505611109832553750226793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263340814813110071666969057 197505611109832553750226793)
      ·
        refine ⟨148129208332374415312670095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197505611109832553750226793 148129208332374415312670095)
        ·
          refine ⟨222193812498561622969005143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148129208332374415312670095 222193812498561622969005143)
          ·
            refine ⟨333290718747842434453507715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222193812498561622969005143 333290718747842434453507715)
            ·
              refine ⟨499936078121763651680261573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333290718747842434453507715 499936078121763651680261573)
              ·
                refine ⟨93738014647830684690049045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 499936078121763651680261573 93738014647830684690049045)
                ·
                  refine ⟨4393969436617063344846049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 93738014647830684690049045 4393969436617063344846049)
                  ·
                    refine ⟨3295477077462797508634537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4393969436617063344846049 3295477077462797508634537)
                    ·
                      refine ⟨2471607808097098131475903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3295477077462797508634537 2471607808097098131475903)
                      ·
                        rfl

theorem cell23_4813439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 2, 2].length) (baseStart_4813439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813439 prefixEnd_4813439 := by exact prefixLift 4813439
  have htrace : WordTrace (prefixWord ++ tailWord_4813439) baseStart_4813439 baseEnd_4813439 := by
    simpa [prefixWord, tailWord_4813439, baseEnd_4813439] using wordTrace_append hprefix tailTrace_4813439
  have hstable : (prefixWord ++ tailWord_4813439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813439).length < 2 ^ (prefixWord ++ tailWord_4813439).sum := by decide
  have hdescent : baseEnd_4813439 < baseStart_4813439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813460 : List Nat := [2, 4, 2, 2, 1, 2, 3, 1, 1, 3, 2]
def baseStart_4813460 : Nat := 118140960795 + 4813460 * 2 ^ 59
def prefixEnd_4813460 : Nat := 4983230072969 + 3 ^ 40 * 4813460 * 2
def baseEnd_4813460 : Nat := 2471618591190842549313307

theorem tailTrace_4813460 : CollatzResearch.WordTrace tailWord_4813460 prefixEnd_4813460 2471618591190842549313307 := by
  unfold tailWord_4813460
  simp only [CollatzResearch.WordTrace]
  refine ⟨87780654570831984182246917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117040872761109312242995889 87780654570831984182246917)
  ·
    refine ⟨16458872732030997034171297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87780654570831984182246917 16458872732030997034171297)
    ·
      refine ⟨12344154549023247775628473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16458872732030997034171297 12344154549023247775628473)
      ·
        refine ⟨9258115911767435831721355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12344154549023247775628473 9258115911767435831721355)
        ·
          refine ⟨13887173867651153747582033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9258115911767435831721355 13887173867651153747582033)
          ·
            refine ⟨10415380400738365310686525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13887173867651153747582033 10415380400738365310686525)
            ·
              refine ⟨3905767650276886991507447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10415380400738365310686525 3905767650276886991507447)
              ·
                refine ⟨5858651475415330487261171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3905767650276886991507447 5858651475415330487261171)
                ·
                  refine ⟨8787977213122995730891757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5858651475415330487261171 8787977213122995730891757)
                  ·
                    refine ⟨3295491454921123399084409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8787977213122995730891757 3295491454921123399084409)
                    ·
                      refine ⟨2471618591190842549313307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3295491454921123399084409 2471618591190842549313307)
                      ·
                        rfl

theorem cell23_4813460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_4813460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813460 prefixEnd_4813460 := by exact prefixLift 4813460
  have htrace : WordTrace (prefixWord ++ tailWord_4813460) baseStart_4813460 baseEnd_4813460 := by
    simpa [prefixWord, tailWord_4813460, baseEnd_4813460] using wordTrace_append hprefix tailTrace_4813460
  have hstable : (prefixWord ++ tailWord_4813460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813460).length < 2 ^ (prefixWord ++ tailWord_4813460).sum := by decide
  have hdescent : baseEnd_4813460 < baseStart_4813460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813486 : List Nat := [4, 1, 4, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_4813486 : Nat := 118140960795 + 4813486 * 2 ^ 59
def prefixEnd_4813486 : Nat := 4983230072969 + 3 ^ 40 * 4813486 * 2
def baseEnd_4813486 : Nat := 2471631941687859447588187

theorem tailTrace_4813486 : CollatzResearch.WordTrace tailWord_4813486 prefixEnd_4813486 2471631941687859447588187 := by
  unfold tailWord_4813486
  simp only [CollatzResearch.WordTrace]
  refine ⟨21945282179946221850617539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117041504959713183203293541 21945282179946221850617539)
  ·
    refine ⟨32917923269919332775926309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21945282179946221850617539 32917923269919332775926309)
    ·
      refine ⟨6172110613109874895486183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32917923269919332775926309 6172110613109874895486183)
      ·
        refine ⟨9258165919664812343229275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6172110613109874895486183 9258165919664812343229275)
        ·
          refine ⟨13887248879497218514843913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9258165919664812343229275 13887248879497218514843913)
          ·
            refine ⟨10415436659622913886132935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13887248879497218514843913 10415436659622913886132935)
            ·
              refine ⟨15623154989434370829199403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10415436659622913886132935 15623154989434370829199403)
              ·
                refine ⟨23434732484151556243799105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15623154989434370829199403 23434732484151556243799105)
                ·
                  refine ⟨17576049363113667182849329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23434732484151556243799105 17576049363113667182849329)
                  ·
                    refine ⟨13182037022335250387136997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17576049363113667182849329 13182037022335250387136997)
                    ·
                      refine ⟨2471631941687859447588187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13182037022335250387136997 2471631941687859447588187)
                      ·
                        rfl

theorem cell23_4813486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_4813486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813486 prefixEnd_4813486 := by exact prefixLift 4813486
  have htrace : WordTrace (prefixWord ++ tailWord_4813486) baseStart_4813486 baseEnd_4813486 := by
    simpa [prefixWord, tailWord_4813486, baseEnd_4813486] using wordTrace_append hprefix tailTrace_4813486
  have hstable : (prefixWord ++ tailWord_4813486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813486).length < 2 ^ (prefixWord ++ tailWord_4813486).sum := by decide
  have hdescent : baseEnd_4813486 < baseStart_4813486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813529 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 4, 4, 2]
def baseStart_4813529 : Nat := 118140960795 + 4813529 * 2 ^ 59
def prefixEnd_4813529 : Nat := 4983230072969 + 3 ^ 40 * 4813529 * 2
def baseEnd_4813529 : Nat := 2471654021356002779350489

theorem tailTrace_4813529 : CollatzResearch.WordTrace tailWord_4813529 prefixEnd_4813529 2471654021356002779350489 := by
  unfold tailWord_4813529
  simp only [CollatzResearch.WordTrace]
  refine ⟨175563825778413993148755641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117042550518942662099170427 175563825778413993148755641)
  ·
    refine ⟨131672869333810494861566731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175563825778413993148755641 131672869333810494861566731)
    ·
      refine ⟨197509304000715742292350097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131672869333810494861566731 197509304000715742292350097)
      ·
        refine ⟨148131978000536806719262573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197509304000715742292350097 148131978000536806719262573)
        ·
          refine ⟨55549491750201302519723465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148131978000536806719262573 55549491750201302519723465)
          ·
            refine ⟨41662118812650976889792599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55549491750201302519723465 41662118812650976889792599)
            ·
              refine ⟨62493178218976465334688899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41662118812650976889792599 62493178218976465334688899)
              ·
                refine ⟨93739767328464698002033349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62493178218976465334688899 93739767328464698002033349)
                ·
                  refine ⟨17576206374087130875381253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93739767328464698002033349 17576206374087130875381253)
                  ·
                    refine ⟨3295538695141337039133985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17576206374087130875381253 3295538695141337039133985)
                    ·
                      refine ⟨2471654021356002779350489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3295538695141337039133985 2471654021356002779350489)
                      ·
                        rfl

theorem cell23_4813529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 4, 2].length) (baseStart_4813529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813529 prefixEnd_4813529 := by exact prefixLift 4813529
  have htrace : WordTrace (prefixWord ++ tailWord_4813529) baseStart_4813529 baseEnd_4813529 := by
    simpa [prefixWord, tailWord_4813529, baseEnd_4813529] using wordTrace_append hprefix tailTrace_4813529
  have hstable : (prefixWord ++ tailWord_4813529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813529).length < 2 ^ (prefixWord ++ tailWord_4813529).sum := by decide
  have hdescent : baseEnd_4813529 < baseStart_4813529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813549 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 3, 4, 3]
def baseStart_4813549 : Nat := 118140960795 + 4813549 * 2 ^ 59
def prefixEnd_4813549 : Nat := 4983230072969 + 3 ^ 40 * 4813549 * 2
def baseEnd_4813549 : Nat := 2471664290969092701100397

theorem tailTrace_4813549 : CollatzResearch.WordTrace tailWord_4813549 prefixEnd_4813549 2471664290969092701100397 := by
  unfold tailWord_4813549
  simp only [CollatzResearch.WordTrace]
  refine ⟨175564555238341536564483701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117043036825561024376322467 175564555238341536564483701)
  ·
    refine ⟨16459177053594519052920347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 175564555238341536564483701 16459177053594519052920347)
    ·
      refine ⟨24688765580391778579380521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16459177053594519052920347 24688765580391778579380521)
      ·
        refine ⟨18516574185293833934535391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24688765580391778579380521 18516574185293833934535391)
        ·
          refine ⟨27774861277940750901803087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18516574185293833934535391 27774861277940750901803087)
          ·
            refine ⟨41662291916911126352704631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27774861277940750901803087 41662291916911126352704631)
            ·
              refine ⟨62493437875366689529056947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41662291916911126352704631 62493437875366689529056947)
              ·
                refine ⟨93740156813050034293585421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62493437875366689529056947 93740156813050034293585421)
                ·
                  refine ⟨35152558804893762860094533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93740156813050034293585421 35152558804893762860094533)
                  ·
                    refine ⟨6591104775917580536267725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35152558804893762860094533 6591104775917580536267725)
                    ·
                      refine ⟨2471664290969092701100397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6591104775917580536267725 2471664290969092701100397)
                      ·
                        rfl

theorem cell23_4813549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_4813549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813549 prefixEnd_4813549 := by exact prefixLift 4813549
  have htrace : WordTrace (prefixWord ++ tailWord_4813549) baseStart_4813549 baseEnd_4813549 := by
    simpa [prefixWord, tailWord_4813549, baseEnd_4813549] using wordTrace_append hprefix tailTrace_4813549
  have hstable : (prefixWord ++ tailWord_4813549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813549).length < 2 ^ (prefixWord ++ tailWord_4813549).sum := by decide
  have hdescent : baseEnd_4813549 < baseStart_4813549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813566 : List Nat := [4, 2, 2, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_4813566 : Nat := 118140960795 + 4813566 * 2 ^ 59
def prefixEnd_4813566 : Nat := 4983230072969 + 3 ^ 40 * 4813566 * 2
def baseEnd_4813566 : Nat := 2471673020140219134587819

theorem tailTrace_4813566 : CollatzResearch.WordTrace tailWord_4813566 prefixEnd_4813566 2471673020140219134587819 := by
  unfold tailWord_4813566
  simp only [CollatzResearch.WordTrace]
  refine ⟨21945646909909993558481569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117043450186186632311901701 21945646909909993558481569)
  ·
    refine ⟨16459235182432495168861177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21945646909909993558481569 16459235182432495168861177)
    ·
      refine ⟨12344426386824371376645883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16459235182432495168861177 12344426386824371376645883)
      ·
        refine ⟨18516639580236557064968825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12344426386824371376645883 18516639580236557064968825)
        ·
          refine ⟨13887479685177417798726619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18516639580236557064968825 13887479685177417798726619)
          ·
            refine ⟨20831219527766126698089929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13887479685177417798726619 20831219527766126698089929)
            ·
              refine ⟨15623414645824595023567447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20831219527766126698089929 15623414645824595023567447)
              ·
                refine ⟨23435121968736892535351171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15623414645824595023567447 23435121968736892535351171)
                ·
                  refine ⟨35152682953105338803026757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23435121968736892535351171 35152682953105338803026757)
                  ·
                    refine ⟨6591128053707251025567517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35152682953105338803026757 6591128053707251025567517)
                    ·
                      refine ⟨2471673020140219134587819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6591128053707251025567517 2471673020140219134587819)
                      ·
                        rfl

theorem cell23_4813566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_4813566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813566 prefixEnd_4813566 := by exact prefixLift 4813566
  have htrace : WordTrace (prefixWord ++ tailWord_4813566) baseStart_4813566 baseEnd_4813566 := by
    simpa [prefixWord, tailWord_4813566, baseEnd_4813566] using wordTrace_append hprefix tailTrace_4813566
  have hstable : (prefixWord ++ tailWord_4813566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813566).length < 2 ^ (prefixWord ++ tailWord_4813566).sum := by decide
  have hdescent : baseEnd_4813566 < baseStart_4813566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813592 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 2, 1, 7]
def baseStart_4813592 : Nat := 118140960795 + 4813592 * 2 ^ 59
def prefixEnd_4813592 : Nat := 4983230072969 + 3 ^ 40 * 4813592 * 2
def baseEnd_4813592 : Nat := 2471686370637236032862699

theorem tailTrace_4813592 : CollatzResearch.WordTrace tailWord_4813592 prefixEnd_4813592 2471686370637236032862699 := by
  unfold tailWord_4813592
  simp only [CollatzResearch.WordTrace]
  refine ⟨87783061788592877454149515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117044082384790503272199353 87783061788592877454149515)
  ·
    refine ⟨131674592682889316181224273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87783061788592877454149515 131674592682889316181224273)
    ·
      refine ⟨98755944512166987135918205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131674592682889316181224273 98755944512166987135918205)
      ·
        refine ⟨37033479192062620175969327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98755944512166987135918205 37033479192062620175969327)
        ·
          refine ⟨55550218788093930263953991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37033479192062620175969327 55550218788093930263953991)
          ·
            refine ⟨83325328182140895395930987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55550218788093930263953991 83325328182140895395930987)
            ·
              refine ⟨124987992273211343093896481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83325328182140895395930987 124987992273211343093896481)
              ·
                refine ⟨93740994204908507320422361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124987992273211343093896481 93740994204908507320422361)
                ·
                  refine ⟨70305745653681380490316771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93740994204908507320422361 70305745653681380490316771)
                  ·
                    refine ⟨105458618480522070735475157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70305745653681380490316771 105458618480522070735475157)
                    ·
                      refine ⟨2471686370637236032862699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 105458618480522070735475157 2471686370637236032862699)
                      ·
                        rfl

theorem cell23_4813592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_4813592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813592 prefixEnd_4813592 := by exact prefixLift 4813592
  have htrace : WordTrace (prefixWord ++ tailWord_4813592) baseStart_4813592 baseEnd_4813592 := by
    simpa [prefixWord, tailWord_4813592, baseEnd_4813592] using wordTrace_append hprefix tailTrace_4813592
  have hstable : (prefixWord ++ tailWord_4813592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813592).length < 2 ^ (prefixWord ++ tailWord_4813592).sum := by decide
  have hdescent : baseEnd_4813592 < baseStart_4813592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813653 : List Nat := [1, 3, 2, 2, 2, 1, 2, 3, 3, 2, 2]
def baseStart_4813653 : Nat := 118140960795 + 4813653 * 2 ^ 59
def prefixEnd_4813653 : Nat := 4983230072969 + 3 ^ 40 * 4813653 * 2
def baseEnd_4813653 : Nat := 2471717692957160294199919

theorem tailTrace_4813653 : CollatzResearch.WordTrace tailWord_4813653 prefixEnd_4813653 2471717692957160294199919 := by
  unfold tailWord_4813653
  simp only [CollatzResearch.WordTrace]
  refine ⟨175568348429964762326269613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117045565619976508217513075 175568348429964762326269613)
  ·
    refine ⟨65838130661236785872351105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175568348429964762326269613 65838130661236785872351105)
    ·
      refine ⟨49378597995927589404263329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65838130661236785872351105 49378597995927589404263329)
      ·
        refine ⟨37033948496945692053197497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49378597995927589404263329 37033948496945692053197497)
        ·
          refine ⟨27775461372709269039898123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37033948496945692053197497 27775461372709269039898123)
          ·
            refine ⟨41663192059063903559847185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27775461372709269039898123 41663192059063903559847185)
            ·
              refine ⟨31247394044297927669885389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41663192059063903559847185 31247394044297927669885389)
              ·
                refine ⟨11717772766611722876207021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31247394044297927669885389 11717772766611722876207021)
                ·
                  refine ⟨4394164787479396078577633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11717772766611722876207021 4394164787479396078577633)
                  ·
                    refine ⟨3295623590609547058933225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4394164787479396078577633 3295623590609547058933225)
                    ·
                      refine ⟨2471717692957160294199919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3295623590609547058933225 2471717692957160294199919)
                      ·
                        rfl

theorem cell23_4813653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_4813653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813653 prefixEnd_4813653 := by exact prefixLift 4813653
  have htrace : WordTrace (prefixWord ++ tailWord_4813653) baseStart_4813653 baseEnd_4813653 := by
    simpa [prefixWord, tailWord_4813653, baseEnd_4813653] using wordTrace_append hprefix tailTrace_4813653
  have hstable : (prefixWord ++ tailWord_4813653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813653).length < 2 ^ (prefixWord ++ tailWord_4813653).sum := by decide
  have hdescent : baseEnd_4813653 < baseStart_4813653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813696 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 5, 3, 2]
def baseStart_4813696 : Nat := 118140960795 + 4813696 * 2 ^ 59
def prefixEnd_4813696 : Nat := 4983230072969 + 3 ^ 40 * 4813696 * 2
def baseEnd_4813696 : Nat := 2471739772625303625962221

theorem tailTrace_4813696 : CollatzResearch.WordTrace tailWord_4813696 prefixEnd_4813696 2471739772625303625962221 := by
  unfold tailWord_4813696
  simp only [CollatzResearch.WordTrace]
  refine ⟨87784958384404490335042471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117046611179205987113389961 87784958384404490335042471)
  ·
    refine ⟨131677437576606735502563707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87784958384404490335042471 131677437576606735502563707)
    ·
      refine ⟨197516156364910103253845561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131677437576606735502563707 197516156364910103253845561)
      ·
        refine ⟨148137117273682577440384171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197516156364910103253845561 148137117273682577440384171)
        ·
          refine ⟨222205675910523866160576257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148137117273682577440384171 222205675910523866160576257)
          ·
            refine ⟨166654256932892899620432193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222205675910523866160576257 166654256932892899620432193)
            ·
              refine ⟨124990692699669674715324145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166654256932892899620432193 124990692699669674715324145)
              ·
                refine ⟨93743019524752256036493109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124990692699669674715324145 93743019524752256036493109)
                ·
                  refine ⟨8788408080445524003421229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93743019524752256036493109 8788408080445524003421229)
                  ·
                    refine ⟨3295653030167071501282961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8788408080445524003421229 3295653030167071501282961)
                    ·
                      refine ⟨2471739772625303625962221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3295653030167071501282961 2471739772625303625962221)
                      ·
                        rfl

theorem cell23_4813696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 5, 3, 2].length) (baseStart_4813696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813696 prefixEnd_4813696 := by exact prefixLift 4813696
  have htrace : WordTrace (prefixWord ++ tailWord_4813696) baseStart_4813696 baseEnd_4813696 := by
    simpa [prefixWord, tailWord_4813696, baseEnd_4813696] using wordTrace_append hprefix tailTrace_4813696
  have hstable : (prefixWord ++ tailWord_4813696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813696).length < 2 ^ (prefixWord ++ tailWord_4813696).sum := by decide
  have hdescent : baseEnd_4813696 < baseStart_4813696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813703 : List Nat := [1, 1, 4, 2, 3, 2, 1, 1, 4, 1, 3]
def baseStart_4813703 : Nat := 118140960795 + 4813703 * 2 ^ 59
def prefixEnd_4813703 : Nat := 4983230072969 + 3 ^ 40 * 4813703 * 2
def baseEnd_4813703 : Nat := 2471743366989885098574689

theorem tailTrace_4813703 : CollatzResearch.WordTrace tailWord_4813703 prefixEnd_4813703 2471743366989885098574689 := by
  unfold tailWord_4813703
  simp only [CollatzResearch.WordTrace]
  refine ⟨175570172079783620865589763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117046781386522413910393175 175570172079783620865589763)
  ·
    refine ⟨263355258119675431298384645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175570172079783620865589763 263355258119675431298384645)
    ·
      refine ⟨49379110897439143368447121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 263355258119675431298384645 49379110897439143368447121)
      ·
        refine ⟨37034333173079357526335341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49379110897439143368447121 37034333173079357526335341)
        ·
          refine ⟨13887874939904759072375753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37034333173079357526335341 13887874939904759072375753)
          ·
            refine ⟨10415906204928569304281815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13887874939904759072375753 10415906204928569304281815)
            ·
              refine ⟨15623859307392853956422723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10415906204928569304281815 15623859307392853956422723)
              ·
                refine ⟨23435788961089280934634085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15623859307392853956422723 23435788961089280934634085)
                ·
                  refine ⟨4394210430204240175243891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23435788961089280934634085 4394210430204240175243891)
                  ·
                    refine ⟨6591315645306360262865837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4394210430204240175243891 6591315645306360262865837)
                    ·
                      refine ⟨2471743366989885098574689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6591315645306360262865837 2471743366989885098574689)
                      ·
                        rfl

theorem cell23_4813703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_4813703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813703 prefixEnd_4813703 := by exact prefixLift 4813703
  have htrace : WordTrace (prefixWord ++ tailWord_4813703) baseStart_4813703 baseEnd_4813703 := by
    simpa [prefixWord, tailWord_4813703, baseEnd_4813703] using wordTrace_append hprefix tailTrace_4813703
  have hstable : (prefixWord ++ tailWord_4813703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813703).length < 2 ^ (prefixWord ++ tailWord_4813703).sum := by decide
  have hdescent : baseEnd_4813703 < baseStart_4813703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813719 : List Nat := [1, 1, 3, 3, 1, 2, 1, 3, 2, 6]
def baseStart_4813719 : Nat := 118140960795 + 4813719 * 2 ^ 59
def prefixEnd_4813719 : Nat := 4983230072969 + 3 ^ 40 * 4813719 * 2
def baseEnd_4813719 : Nat := 823917194226785678658205

theorem tailTrace_4813719 : CollatzResearch.WordTrace tailWord_4813719 prefixEnd_4813719 823917194226785678658205 := by
  unfold tailWord_4813719
  simp only [CollatzResearch.WordTrace]
  refine ⟨175570755647725655598172211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117047170431817103732114807 175570755647725655598172211)
  ·
    refine ⟨263356133471588483397258317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175570755647725655598172211 263356133471588483397258317)
    ·
      refine ⟨98758550051845681273971869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263356133471588483397258317 98758550051845681273971869)
      ·
        refine ⟨37034456269442130477739451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98758550051845681273971869 37034456269442130477739451)
        ·
          refine ⟨55551684404163195716609177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37034456269442130477739451 55551684404163195716609177)
          ·
            refine ⟨41663763303122396787456883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55551684404163195716609177 41663763303122396787456883)
            ·
              refine ⟨62495644954683595181185325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41663763303122396787456883 62495644954683595181185325)
              ·
                refine ⟨23435866858006348192944497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62495644954683595181185325 23435866858006348192944497)
                ·
                  refine ⟨17576900143504761144708373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23435866858006348192944497 17576900143504761144708373)
                  ·
                    refine ⟨823917194226785678658205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17576900143504761144708373 823917194226785678658205)
                    ·
                      rfl

theorem cell23_4813719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_4813719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813719 prefixEnd_4813719 := by exact prefixLift 4813719
  have htrace : WordTrace (prefixWord ++ tailWord_4813719) baseStart_4813719 baseEnd_4813719 := by
    simpa [prefixWord, tailWord_4813719, baseEnd_4813719] using wordTrace_append hprefix tailTrace_4813719
  have hstable : (prefixWord ++ tailWord_4813719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813719).length < 2 ^ (prefixWord ++ tailWord_4813719).sum := by decide
  have hdescent : baseEnd_4813719 < baseStart_4813719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813730 : List Nat := [3, 3, 1, 2, 2, 1, 1, 4, 1, 3, 2]
def baseStart_4813730 : Nat := 118140960795 + 4813730 * 2 ^ 59
def prefixEnd_4813730 : Nat := 4983230072969 + 3 ^ 40 * 4813730 * 2
def baseEnd_4813730 : Nat := 2471757230967556492937065

theorem tailTrace_4813730 : CollatzResearch.WordTrace tailWord_4813730 prefixEnd_4813730 2471757230967556492937065 := by
  unfold tailWord_4813730
  simp only [CollatzResearch.WordTrace]
  refine ⟨43892789212671451119205661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117047437900457202984548429 43892789212671451119205661)
  ·
    refine ⟨16459795954751794169702123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43892789212671451119205661 16459795954751794169702123)
    ·
      refine ⟨24689693932127691254553185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16459795954751794169702123 24689693932127691254553185)
      ·
        refine ⟨18517270449095768440914889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24689693932127691254553185 18517270449095768440914889)
        ·
          refine ⟨13887952836821826330686167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18517270449095768440914889 13887952836821826330686167)
          ·
            refine ⟨20831929255232739496029251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13887952836821826330686167 20831929255232739496029251)
            ·
              refine ⟨31247893882849109244043877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20831929255232739496029251 31247893882849109244043877)
              ·
                refine ⟨5858980103034207983258227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31247893882849109244043877 5858980103034207983258227)
                ·
                  refine ⟨8788470154551311974887341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5858980103034207983258227 8788470154551311974887341)
                  ·
                    refine ⟨3295676307956741990582753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8788470154551311974887341 3295676307956741990582753)
                    ·
                      refine ⟨2471757230967556492937065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3295676307956741990582753 2471757230967556492937065)
                      ·
                        rfl

theorem cell23_4813730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_4813730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813730 prefixEnd_4813730 := by exact prefixLift 4813730
  have htrace : WordTrace (prefixWord ++ tailWord_4813730) baseStart_4813730 baseEnd_4813730 := by
    simpa [prefixWord, tailWord_4813730, baseEnd_4813730] using wordTrace_append hprefix tailTrace_4813730
  have hstable : (prefixWord ++ tailWord_4813730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813730).length < 2 ^ (prefixWord ++ tailWord_4813730).sum := by decide
  have hdescent : baseEnd_4813730 < baseStart_4813730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813819 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 5]
def baseStart_4813819 : Nat := 118140960795 + 4813819 * 2 ^ 59
def prefixEnd_4813819 : Nat := 4983230072969 + 3 ^ 40 * 4813819 * 2
def baseEnd_4813819 : Nat := 2471802930745806644724155

theorem tailTrace_4813819 : CollatzResearch.WordTrace tailWord_4813819 prefixEnd_4813819 2471802930745806644724155 := by
  unfold tailWord_4813819
  simp only [CollatzResearch.WordTrace]
  refine ⟨175574402947363372676812511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117049601964908915117875007 175574402947363372676812511)
  ·
    refine ⟨263361604421045059015218767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175574402947363372676812511 263361604421045059015218767)
    ·
      refine ⟨395042406631567588522828151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263361604421045059015218767 395042406631567588522828151)
      ·
        refine ⟨592563609947351382784242227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395042406631567588522828151 592563609947351382784242227)
        ·
          refine ⟨888845414921027074176363341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 592563609947351382784242227 888845414921027074176363341)
          ·
            refine ⟨333317030595385152816136253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 888845414921027074176363341 333317030595385152816136253)
            ·
              refine ⟨124993886473269432306051095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 333317030595385152816136253 124993886473269432306051095)
              ·
                refine ⟨187490829709904148459076643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124993886473269432306051095 187490829709904148459076643)
                ·
                  refine ⟨281236244564856222688614965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187490829709904148459076643 281236244564856222688614965)
                  ·
                    refine ⟨26365897927955270877057653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 281236244564856222688614965 26365897927955270877057653)
                    ·
                      refine ⟨2471802930745806644724155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26365897927955270877057653 2471802930745806644724155)
                      ·
                        rfl

theorem cell23_4813819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 5].length) (baseStart_4813819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813819 prefixEnd_4813819 := by exact prefixLift 4813819
  have htrace : WordTrace (prefixWord ++ tailWord_4813819) baseStart_4813819 baseEnd_4813819 := by
    simpa [prefixWord, tailWord_4813819, baseEnd_4813819] using wordTrace_append hprefix tailTrace_4813819
  have hstable : (prefixWord ++ tailWord_4813819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813819).length < 2 ^ (prefixWord ++ tailWord_4813819).sum := by decide
  have hdescent : baseEnd_4813819 < baseStart_4813819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813863 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_4813863 : Nat := 118140960795 + 4813863 * 2 ^ 59
def prefixEnd_4813863 : Nat := 4983230072969 + 3 ^ 40 * 4813863 * 2
def baseEnd_4813863 : Nat := 2471825523894604472573953

theorem tailTrace_4813863 : CollatzResearch.WordTrace tailWord_4813863 prefixEnd_4813863 2471825523894604472573953 := by
  unfold tailWord_4813863
  simp only [CollatzResearch.WordTrace]
  refine ⟨175576007759203968191414243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117050671839469312127609495 175576007759203968191414243)
  ·
    refine ⟨263364011638805952287121365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175576007759203968191414243 263364011638805952287121365)
    ·
      refine ⟨6172594022784514506729407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 263364011638805952287121365 6172594022784514506729407)
      ·
        refine ⟨9258891034176771760094111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6172594022784514506729407 9258891034176771760094111)
        ·
          refine ⟨13888336551265157640141167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9258891034176771760094111 13888336551265157640141167)
          ·
            refine ⟨20832504826897736460211751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13888336551265157640141167 20832504826897736460211751)
            ·
              refine ⟨31248757240346604690317627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20832504826897736460211751 31248757240346604690317627)
              ·
                refine ⟨46873135860519907035476441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31248757240346604690317627 46873135860519907035476441)
                ·
                  refine ⟨35154851895389930276607331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46873135860519907035476441 35154851895389930276607331)
                  ·
                    refine ⟨52732277843084895414910997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35154851895389930276607331 52732277843084895414910997)
                    ·
                      refine ⟨2471825523894604472573953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52732277843084895414910997 2471825523894604472573953)
                      ·
                        rfl

theorem cell23_4813863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_4813863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813863 prefixEnd_4813863 := by exact prefixLift 4813863
  have htrace : WordTrace (prefixWord ++ tailWord_4813863) baseStart_4813863 baseEnd_4813863 := by
    simpa [prefixWord, tailWord_4813863, baseEnd_4813863] using wordTrace_append hprefix tailTrace_4813863
  have hstable : (prefixWord ++ tailWord_4813863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813863).length < 2 ^ (prefixWord ++ tailWord_4813863).sum := by decide
  have hdescent : baseEnd_4813863 < baseStart_4813863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813893 : List Nat := [1, 3, 1, 1, 1, 3, 3, 2, 1, 5, 2]
def baseStart_4813893 : Nat := 118140960795 + 4813893 * 2 ^ 59
def prefixEnd_4813893 : Nat := 4983230072969 + 3 ^ 40 * 4813893 * 2
def baseEnd_4813893 : Nat := 2471840928314239355198815

theorem tailTrace_4813893 : CollatzResearch.WordTrace tailWord_4813893 prefixEnd_4813893 2471840928314239355198815 := by
  unfold tailWord_4813893
  simp only [CollatzResearch.WordTrace]
  refine ⟨175577101949095283315006333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117051401299396855543337555 175577101949095283315006333)
  ·
    refine ⟨65841413230910731243127375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175577101949095283315006333 65841413230910731243127375)
    ·
      refine ⟨98762119846366096864691063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65841413230910731243127375 98762119846366096864691063)
      ·
        refine ⟨148143179769549145297036595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98762119846366096864691063 148143179769549145297036595)
        ·
          refine ⟨222214769654323717945554893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148143179769549145297036595 222214769654323717945554893)
          ·
            refine ⟨83330538620371394229583085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222214769654323717945554893 83330538620371394229583085)
            ·
              refine ⟨31248951982639272836093657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83330538620371394229583085 31248951982639272836093657)
              ·
                refine ⟨23436713986979454627070243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31248951982639272836093657 23436713986979454627070243)
                ·
                  refine ⟨35155070980469181940605365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23436713986979454627070243 35155070980469181940605365)
                  ·
                    refine ⟨3295787904418985806931753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35155070980469181940605365 3295787904418985806931753)
                    ·
                      refine ⟨2471840928314239355198815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3295787904418985806931753 2471840928314239355198815)
                      ·
                        rfl

theorem cell23_4813893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 5, 2].length) (baseStart_4813893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813893 prefixEnd_4813893 := by exact prefixLift 4813893
  have htrace : WordTrace (prefixWord ++ tailWord_4813893) baseStart_4813893 baseEnd_4813893 := by
    simpa [prefixWord, tailWord_4813893, baseEnd_4813893] using wordTrace_append hprefix tailTrace_4813893
  have hstable : (prefixWord ++ tailWord_4813893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813893).length < 2 ^ (prefixWord ++ tailWord_4813893).sum := by decide
  have hdescent : baseEnd_4813893 < baseStart_4813893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813936 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 6]
def baseStart_4813936 : Nat := 118140960795 + 4813936 * 2 ^ 59
def prefixEnd_4813936 : Nat := 4983230072969 + 3 ^ 40 * 4813936 * 2
def baseEnd_4813936 : Nat := 2471863007982382686961117

theorem tailTrace_4813936 : CollatzResearch.WordTrace tailWord_4813936 prefixEnd_4813936 2471863007982382686961117 := by
  unfold tailWord_4813936
  simp only [CollatzResearch.WordTrace]
  refine ⟨87789335143969750829410831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117052446858626334439214441 87789335143969750829410831)
  ·
    refine ⟨131684002715954626244116247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87789335143969750829410831 131684002715954626244116247)
    ·
      refine ⟨197526004073931939366174371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131684002715954626244116247 197526004073931939366174371)
      ·
        refine ⟨296289006110897909049261557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197526004073931939366174371 296289006110897909049261557)
        ·
          refine ⟨27777094322896678973368271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 296289006110897909049261557 27777094322896678973368271)
          ·
            refine ⟨41665641484345018460052407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27777094322896678973368271 41665641484345018460052407)
            ·
              refine ⟨62498462226517527690078611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41665641484345018460052407 62498462226517527690078611)
              ·
                refine ⟨93747693339776291535117917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62498462226517527690078611 93747693339776291535117917)
                ·
                  refine ⟨35155385002416109325669219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93747693339776291535117917 35155385002416109325669219)
                  ·
                    refine ⟨52733077503624163988503829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35155385002416109325669219 52733077503624163988503829)
                    ·
                      refine ⟨2471863007982382686961117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52733077503624163988503829 2471863007982382686961117)
                      ·
                        rfl

theorem cell23_4813936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 6].length) (baseStart_4813936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813936 prefixEnd_4813936 := by exact prefixLift 4813936
  have htrace : WordTrace (prefixWord ++ tailWord_4813936) baseStart_4813936 baseEnd_4813936 := by
    simpa [prefixWord, tailWord_4813936, baseEnd_4813936] using wordTrace_append hprefix tailTrace_4813936
  have hstable : (prefixWord ++ tailWord_4813936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813936).length < 2 ^ (prefixWord ++ tailWord_4813936).sum := by decide
  have hdescent : baseEnd_4813936 < baseStart_4813936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813943 : List Nat := [1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 3]
def baseStart_4813943 : Nat := 118140960795 + 4813943 * 2 ^ 59
def prefixEnd_4813943 : Nat := 4983230072969 + 3 ^ 40 * 4813943 * 2
def baseEnd_4813943 : Nat := 2471866602346964159573585

theorem tailTrace_4813943 : CollatzResearch.WordTrace tailWord_4813943 prefixEnd_4813943 2471866602346964159573585 := by
  unfold tailWord_4813943
  simp only [CollatzResearch.WordTrace]
  refine ⟨175578925598914141854326483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117052617065942761236217655 175578925598914141854326483)
  ·
    refine ⟨263368388398371212781489725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175578925598914141854326483 263368388398371212781489725)
    ·
      refine ⟨98763145649389204793058647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263368388398371212781489725 98763145649389204793058647)
      ·
        refine ⟨148144718474083807189587971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98763145649389204793058647 148144718474083807189587971)
        ·
          refine ⟨222217077711125710784381957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148144718474083807189587971 222217077711125710784381957)
          ·
            refine ⟨41665702070836070772071617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 222217077711125710784381957 41665702070836070772071617)
            ·
              refine ⟨31249276553127053079053713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41665702070836070772071617 31249276553127053079053713)
              ·
                refine ⟨23436957414845289809290285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31249276553127053079053713 23436957414845289809290285)
                ·
                  refine ⟨8788859030566983678483857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23436957414845289809290285 8788859030566983678483857)
                  ·
                    refine ⟨6591644272925237758862893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8788859030566983678483857 6591644272925237758862893)
                    ·
                      refine ⟨2471866602346964159573585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6591644272925237758862893 2471866602346964159573585)
                      ·
                        rfl

theorem cell23_4813943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 3].length) (baseStart_4813943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813943 prefixEnd_4813943 := by exact prefixLift 4813943
  have htrace : WordTrace (prefixWord ++ tailWord_4813943) baseStart_4813943 baseEnd_4813943 := by
    simpa [prefixWord, tailWord_4813943, baseEnd_4813943] using wordTrace_append hprefix tailTrace_4813943
  have hstable : (prefixWord ++ tailWord_4813943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813943).length < 2 ^ (prefixWord ++ tailWord_4813943).sum := by decide
  have hdescent : baseEnd_4813943 < baseStart_4813943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813953 : List Nat := [1, 2, 4, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_4813953 : Nat := 118140960795 + 4813953 * 2 ^ 59
def prefixEnd_4813953 : Nat := 4983230072969 + 3 ^ 40 * 4813953 * 2
def baseEnd_4813953 : Nat := 2471871737153509120448539

theorem tailTrace_4813953 : CollatzResearch.WordTrace tailWord_4813953 prefixEnd_4813953 2471871737153509120448539 := by
  unfold tailWord_4813953
  simp only [CollatzResearch.WordTrace]
  refine ⟨175579290328877913562190513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117052860219251942374793675 175579290328877913562190513)
  ·
    refine ⟨131684467746658435171642885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175579290328877913562190513 131684467746658435171642885)
    ·
      refine ⟨24690837702498456594683041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131684467746658435171642885 24690837702498456594683041)
      ·
        refine ⟨18518128276873842446012281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24690837702498456594683041 18518128276873842446012281)
        ·
          refine ⟨13888596207655381834509211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18518128276873842446012281 13888596207655381834509211)
          ·
            refine ⟨20832894311483072751763817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13888596207655381834509211 20832894311483072751763817)
            ·
              refine ⟨15624670733612304563822863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20832894311483072751763817 15624670733612304563822863)
              ·
                refine ⟨23437006100418456845734295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15624670733612304563822863 23437006100418456845734295)
                ·
                  refine ⟨35155509150627685268601443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23437006100418456845734295 35155509150627685268601443)
                  ·
                    refine ⟨52733263725941527902902165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35155509150627685268601443 52733263725941527902902165)
                    ·
                      refine ⟨2471871737153509120448539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52733263725941527902902165 2471871737153509120448539)
                      ·
                        rfl

theorem cell23_4813953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_4813953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813953 prefixEnd_4813953 := by exact prefixLift 4813953
  have htrace : WordTrace (prefixWord ++ tailWord_4813953) baseStart_4813953 baseEnd_4813953 := by
    simpa [prefixWord, tailWord_4813953, baseEnd_4813953] using wordTrace_append hprefix tailTrace_4813953
  have hstable : (prefixWord ++ tailWord_4813953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813953).length < 2 ^ (prefixWord ++ tailWord_4813953).sum := by decide
  have hdescent : baseEnd_4813953 < baseStart_4813953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813957 : List Nat := [1, 3, 1, 1, 6, 2, 1, 2, 1, 1, 4]
def baseStart_4813957 : Nat := 118140960795 + 4813957 * 2 ^ 59
def prefixEnd_4813957 : Nat := 4983230072969 + 3 ^ 40 * 4813957 * 2
def baseEnd_4813957 : Nat := 2471873791076127104798521

theorem tailTrace_4813957 : CollatzResearch.WordTrace tailWord_4813957 prefixEnd_4813957 2471873791076127104798521 := by
  unfold tailWord_4813957
  simp only [CollatzResearch.WordTrace]
  refine ⟨175579436220863422245336125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117052957480575614830224083 175579436220863422245336125)
  ·
    refine ⟨65842288582823783342001047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175579436220863422245336125 65842288582823783342001047)
    ·
      refine ⟨98763432874235675013001571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65842288582823783342001047 98763432874235675013001571)
      ·
        refine ⟨148145149311353512519502357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98763432874235675013001571 148145149311353512519502357)
        ·
          refine ⟨6944303873969695899351673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 148145149311353512519502357 6944303873969695899351673)
          ·
            refine ⟨5208227905477271924513755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6944303873969695899351673 5208227905477271924513755)
            ·
              refine ⟨7812341858215907886770633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5208227905477271924513755 7812341858215907886770633)
              ·
                refine ⟨5859256393661930915077975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7812341858215907886770633 5859256393661930915077975)
                ·
                  refine ⟨8788884590492896372616963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5859256393661930915077975 8788884590492896372616963)
                  ·
                    refine ⟨13183326885739344558925445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8788884590492896372616963 13183326885739344558925445)
                    ·
                      refine ⟨2471873791076127104798521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13183326885739344558925445 2471873791076127104798521)
                      ·
                        rfl

theorem cell23_4813957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 1, 4].length) (baseStart_4813957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813957 prefixEnd_4813957 := by exact prefixLift 4813957
  have htrace : WordTrace (prefixWord ++ tailWord_4813957) baseStart_4813957 baseEnd_4813957 := by
    simpa [prefixWord, tailWord_4813957, baseEnd_4813957] using wordTrace_append hprefix tailTrace_4813957
  have hstable : (prefixWord ++ tailWord_4813957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813957).length < 2 ^ (prefixWord ++ tailWord_4813957).sum := by decide
  have hdescent : baseEnd_4813957 < baseStart_4813957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813970 : List Nat := [3, 2, 3, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_4813970 : Nat := 118140960795 + 4813970 * 2 ^ 59
def prefixEnd_4813970 : Nat := 4983230072969 + 3 ^ 40 * 4813970 * 2
def baseEnd_4813970 : Nat := 2471880466324635553935961

theorem tailTrace_4813970 : CollatzResearch.WordTrace tailWord_4813970 prefixEnd_4813970 2471880466324635553935961 := by
  unfold tailWord_4813970
  simp only [CollatzResearch.WordTrace]
  refine ⟨43894977592454081366389841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117053273579877550310372909 43894977592454081366389841)
  ·
    refine ⟨32921233194340561024792381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43894977592454081366389841 32921233194340561024792381)
    ·
      refine ⟨12345462447877710384297143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32921233194340561024792381 12345462447877710384297143)
      ·
        refine ⟨18518193671816565576445715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12345462447877710384297143 18518193671816565576445715)
        ·
          refine ⟨27777290507724848364668573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18518193671816565576445715 27777290507724848364668573)
          ·
            refine ⟨10416483940396818136750715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27777290507724848364668573 10416483940396818136750715)
            ·
              refine ⟨15624725910595227205126073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10416483940396818136750715 15624725910595227205126073)
              ·
                refine ⟨11718544432946420403844555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15624725910595227205126073 11718544432946420403844555)
                ·
                  refine ⟨17577816649419630605766833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11718544432946420403844555 17577816649419630605766833)
                  ·
                    refine ⟨13183362487064722954325125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17577816649419630605766833 13183362487064722954325125)
                    ·
                      refine ⟨2471880466324635553935961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13183362487064722954325125 2471880466324635553935961)
                      ·
                        rfl

theorem cell23_4813970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_4813970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813970 prefixEnd_4813970 := by exact prefixLift 4813970
  have htrace : WordTrace (prefixWord ++ tailWord_4813970) baseStart_4813970 baseEnd_4813970 := by
    simpa [prefixWord, tailWord_4813970, baseEnd_4813970] using wordTrace_append hprefix tailTrace_4813970
  have hstable : (prefixWord ++ tailWord_4813970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813970).length < 2 ^ (prefixWord ++ tailWord_4813970).sum := by decide
  have hdescent : baseEnd_4813970 < baseStart_4813970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813991 : List Nat := [1, 1, 6, 2, 1, 2, 1, 4, 1, 2, 2]
def baseStart_4813991 : Nat := 118140960795 + 4813991 * 2 ^ 59
def prefixEnd_4813991 : Nat := 4983230072969 + 3 ^ 40 * 4813991 * 2
def baseEnd_4813991 : Nat := 2471891249418379971773365

theorem tailTrace_4813991 : CollatzResearch.WordTrace tailWord_4813991 prefixEnd_4813991 2471891249418379971773365 := by
  unfold tailWord_4813991
  simp only [CollatzResearch.WordTrace]
  refine ⟨175580676302740246052073827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117053784201826830701382551 175580676302740246052073827)
  ·
    refine ⟨263371014454110369078110741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175580676302740246052073827 263371014454110369078110741)
    ·
      refine ⟨12345516302536423550536441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 263371014454110369078110741 12345516302536423550536441)
      ·
        refine ⟨9259137226902317662902331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12345516302536423550536441 9259137226902317662902331)
        ·
          refine ⟨13888705840353476494353497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9259137226902317662902331 13888705840353476494353497)
          ·
            refine ⟨10416529380265107370765123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13888705840353476494353497 10416529380265107370765123)
            ·
              refine ⟨15624794070397661056147685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10416529380265107370765123 15624794070397661056147685)
              ·
                refine ⟨2929648888199561448027691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15624794070397661056147685 2929648888199561448027691)
                ·
                  refine ⟨4394473332299342172041537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2929648888199561448027691 4394473332299342172041537)
                  ·
                    refine ⟨3295854999224506629031153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4394473332299342172041537 3295854999224506629031153)
                    ·
                      refine ⟨2471891249418379971773365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3295854999224506629031153 2471891249418379971773365)
                      ·
                        rfl

theorem cell23_4813991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_4813991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813991 prefixEnd_4813991 := by exact prefixLift 4813991
  have htrace : WordTrace (prefixWord ++ tailWord_4813991) baseStart_4813991 baseEnd_4813991 := by
    simpa [prefixWord, tailWord_4813991, baseEnd_4813991] using wordTrace_append hprefix tailTrace_4813991
  have hstable : (prefixWord ++ tailWord_4813991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813991).length < 2 ^ (prefixWord ++ tailWord_4813991).sum := by decide
  have hdescent : baseEnd_4813991 < baseStart_4813991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4813997 : List Nat := [1, 5, 2, 1, 4, 1, 1, 8]
def baseStart_4813997 : Nat := 118140960795 + 4813997 * 2 ^ 59
def prefixEnd_4813997 : Nat := 4983230072969 + 3 ^ 40 * 4813997 * 2
def baseEnd_4813997 : Nat := 91551641863048405492531

theorem tailTrace_4813997 : CollatzResearch.WordTrace tailWord_4813997 prefixEnd_4813997 91551641863048405492531 := by
  unfold tailWord_4813997
  simp only [CollatzResearch.WordTrace]
  refine ⟨175580895140718509076792245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117053930093812339384528163 175580895140718509076792245)
  ·
    refine ⟨16460708919442360225949273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 175580895140718509076792245 16460708919442360225949273)
    ·
      refine ⟨12345531689581770169461955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16460708919442360225949273 12345531689581770169461955)
      ·
        refine ⟨18518297534372655254192933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12345531689581770169461955 18518297534372655254192933)
        ·
          refine ⟨3472180787694872860161175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18518297534372655254192933 3472180787694872860161175)
          ·
            refine ⟨5208271181542309290241763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3472180787694872860161175 5208271181542309290241763)
            ·
              refine ⟨7812406772313463935362645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5208271181542309290241763 7812406772313463935362645)
              ·
                refine ⟨91551641863048405492531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7812406772313463935362645 91551641863048405492531)
                ·
                  rfl

theorem cell23_4813997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 8].length) (baseStart_4813997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4813997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4813997 prefixEnd_4813997 := by exact prefixLift 4813997
  have htrace : WordTrace (prefixWord ++ tailWord_4813997) baseStart_4813997 baseEnd_4813997 := by
    simpa [prefixWord, tailWord_4813997, baseEnd_4813997] using wordTrace_append hprefix tailTrace_4813997
  have hstable : (prefixWord ++ tailWord_4813997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4813997).length < 2 ^ (prefixWord ++ tailWord_4813997).sum := by decide
  have hdescent : baseEnd_4813997 < baseStart_4813997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4813997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814083 : List Nat := [1, 1, 1, 3, 2, 4, 2, 1, 1, 7]
def baseStart_4814083 : Nat := 118140960795 + 4814083 * 2 ^ 59
def prefixEnd_4814083 : Nat := 4983230072969 + 3 ^ 40 * 4814083 * 2
def baseEnd_4814083 : Nat := 823979496546197870607647

theorem tailTrace_4814083 : CollatzResearch.WordTrace tailWord_4814083 prefixEnd_4814083 823979496546197870607647 := by
  unfold tailWord_4814083
  simp only [CollatzResearch.WordTrace]
  refine ⟨175584031818406945764422903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117056021212271297176281935 175584031818406945764422903)
  ·
    refine ⟨263376047727610418646634355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175584031818406945764422903 263376047727610418646634355)
    ·
      refine ⟨395064071591415627969951533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263376047727610418646634355 395064071591415627969951533)
      ·
        refine ⟨148149026846780860488731825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 395064071591415627969951533 148149026846780860488731825)
        ·
          refine ⟨111111770135085645366548869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148149026846780860488731825 111111770135085645366548869)
          ·
            refine ⟨20833456900328558506227913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111111770135085645366548869 20833456900328558506227913)
            ·
              refine ⟨15625092675246418879670935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20833456900328558506227913 15625092675246418879670935)
              ·
                refine ⟨23437639012869628319506403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15625092675246418879670935 23437639012869628319506403)
                ·
                  refine ⟨35156458519304442479259605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23437639012869628319506403 35156458519304442479259605)
                  ·
                    refine ⟨823979496546197870607647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35156458519304442479259605 823979496546197870607647)
                    ·
                      rfl

theorem cell23_4814083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 7].length) (baseStart_4814083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814083 prefixEnd_4814083 := by exact prefixLift 4814083
  have htrace : WordTrace (prefixWord ++ tailWord_4814083) baseStart_4814083 baseEnd_4814083 := by
    simpa [prefixWord, tailWord_4814083, baseEnd_4814083] using wordTrace_append hprefix tailTrace_4814083
  have hstable : (prefixWord ++ tailWord_4814083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814083).length < 2 ^ (prefixWord ++ tailWord_4814083).sum := by decide
  have hdescent : baseEnd_4814083 < baseStart_4814083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814090 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2]
def baseStart_4814090 : Nat := 118140960795 + 4814090 * 2 ^ 59
def prefixEnd_4814090 : Nat := 4983230072969 + 3 ^ 40 * 4814090 * 2
def baseEnd_4814090 : Nat := 2471942084003175084435409

theorem tailTrace_4814090 : CollatzResearch.WordTrace tailWord_4814090 prefixEnd_4814090 2471942084003175084435409 := by
  unfold tailWord_4814090
  simp only [CollatzResearch.WordTrace]
  refine ⟨43896071782345396489981931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117056191419587723973285149 43896071782345396489981931)
  ·
    refine ⟨65844107673518094734972897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43896071782345396489981931 65844107673518094734972897)
    ·
      refine ⟨49383080755138571051229673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65844107673518094734972897 49383080755138571051229673)
      ·
        refine ⟨37037310566353928288422255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49383080755138571051229673 37037310566353928288422255)
        ·
          refine ⟨55555965849530892432633383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37037310566353928288422255 55555965849530892432633383)
          ·
            refine ⟨83333948774296338648950075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55555965849530892432633383 83333948774296338648950075)
            ·
              refine ⟨125000923161444507973425113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83333948774296338648950075 125000923161444507973425113)
              ·
                refine ⟨93750692371083380980068835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125000923161444507973425113 93750692371083380980068835)
                ·
                  refine ⟨140626038556625071470103253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93750692371083380980068835 140626038556625071470103253)
                  ·
                    refine ⟨3295922778670900112580545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 140626038556625071470103253 3295922778670900112580545)
                    ·
                      refine ⟨2471942084003175084435409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3295922778670900112580545 2471942084003175084435409)
                      ·
                        rfl

theorem cell23_4814090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_4814090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814090 prefixEnd_4814090 := by exact prefixLift 4814090
  have htrace : WordTrace (prefixWord ++ tailWord_4814090) baseStart_4814090 baseEnd_4814090 := by
    simpa [prefixWord, tailWord_4814090, baseEnd_4814090] using wordTrace_append hprefix tailTrace_4814090
  have hstable : (prefixWord ++ tailWord_4814090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814090).length < 2 ^ (prefixWord ++ tailWord_4814090).sum := by decide
  have hdescent : baseEnd_4814090 < baseStart_4814090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814147 : List Nat := [1, 1, 1, 3, 1, 3, 1, 7, 1, 4]
def baseStart_4814147 : Nat := 118140960795 + 4814147 * 2 ^ 59
def prefixEnd_4814147 : Nat := 4983230072969 + 3 ^ 40 * 4814147 * 2
def baseEnd_4814147 : Nat := 823990450800160453807549

theorem tailTrace_4814147 : CollatzResearch.WordTrace tailWord_4814147 prefixEnd_4814147 823990450800160453807549 := by
  unfold tailWord_4814147
  simp only [CollatzResearch.WordTrace]
  refine ⟨175586366090175084694752695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117057577393450056463168463 175586366090175084694752695)
  ·
    refine ⟨263379549135262627042129043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175586366090175084694752695 263379549135262627042129043)
    ·
      refine ⟨395069323702893940563193565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263379549135262627042129043 395069323702893940563193565)
      ·
        refine ⟨148150996388585227711197587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 395069323702893940563193565 148150996388585227711197587)
        ·
          refine ⟨222226494582877841566796381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148150996388585227711197587 222226494582877841566796381)
          ·
            refine ⟨83334935468579190587548643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222226494582877841566796381 83334935468579190587548643)
            ·
              refine ⟨125002403202868785881322965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83334935468579190587548643 125002403202868785881322965)
              ·
                refine ⟨2929743825067237169093507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 125002403202868785881322965 2929743825067237169093507)
                ·
                  refine ⟨4394615737600855753640261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2929743825067237169093507 4394615737600855753640261)
                  ·
                    refine ⟨823990450800160453807549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4394615737600855753640261 823990450800160453807549)
                    ·
                      rfl

theorem cell23_4814147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 1, 4].length) (baseStart_4814147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814147 prefixEnd_4814147 := by exact prefixLift 4814147
  have htrace : WordTrace (prefixWord ++ tailWord_4814147) baseStart_4814147 baseEnd_4814147 := by
    simpa [prefixWord, tailWord_4814147, baseEnd_4814147] using wordTrace_append hprefix tailTrace_4814147
  have hstable : (prefixWord ++ tailWord_4814147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814147).length < 2 ^ (prefixWord ++ tailWord_4814147).sum := by decide
  have hdescent : baseEnd_4814147 < baseStart_4814147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814160 : List Nat := [2, 1, 1, 1, 1, 5, 4, 2, 6]
def baseStart_4814160 : Nat := 118140960795 + 4814160 * 2 ^ 59
def prefixEnd_4814160 : Nat := 4983230072969 + 3 ^ 40 * 4814160 * 2
def baseEnd_4814160 : Nat := 274664225294332201173343

theorem tailTrace_4814160 : CollatzResearch.WordTrace tailWord_4814160 prefixEnd_4814160 274664225294332201173343 := by
  unfold tailWord_4814160
  simp only [CollatzResearch.WordTrace]
  refine ⟨87793420119563993957487967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117057893492751991943317289 87793420119563993957487967)
  ·
    refine ⟨131690130179345990936231951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87793420119563993957487967 131690130179345990936231951)
    ·
      refine ⟨197535195269018986404347927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131690130179345990936231951 197535195269018986404347927)
      ·
        refine ⟨296302792903528479606521891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197535195269018986404347927 296302792903528479606521891)
        ·
          refine ⟨444454189355292719409782837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296302792903528479606521891 444454189355292719409782837)
          ·
            refine ⟨41667580252058692444667141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 444454189355292719409782837 41667580252058692444667141)
            ·
              refine ⟨7812671297261004833375089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41667580252058692444667141 7812671297261004833375089)
              ·
                refine ⟨5859503472945753625031317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7812671297261004833375089 5859503472945753625031317)
                ·
                  refine ⟨274664225294332201173343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5859503472945753625031317 274664225294332201173343)
                  ·
                    rfl

theorem cell23_4814160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 6].length) (baseStart_4814160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814160 prefixEnd_4814160 := by exact prefixLift 4814160
  have htrace : WordTrace (prefixWord ++ tailWord_4814160) baseStart_4814160 baseEnd_4814160 := by
    simpa [prefixWord, tailWord_4814160, baseEnd_4814160] using wordTrace_append hprefix tailTrace_4814160
  have hstable : (prefixWord ++ tailWord_4814160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814160).length < 2 ^ (prefixWord ++ tailWord_4814160).sum := by decide
  have hdescent : baseEnd_4814160 < baseStart_4814160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814163 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 6]
def baseStart_4814163 : Nat := 118140960795 + 4814163 * 2 ^ 59
def prefixEnd_4814163 : Nat := 4983230072969 + 3 ^ 40 * 4814163 * 2
def baseEnd_4814163 : Nat := 2471979568090953298822573

theorem tailTrace_4814163 : CollatzResearch.WordTrace tailWord_4814163 prefixEnd_4814163 2471979568090953298822573 := by
  unfold tailWord_4814163
  simp only [CollatzResearch.WordTrace]
  refine ⟨175586949658117119427335143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117057966438744746284890095 175586949658117119427335143)
  ·
    refine ⟨263380424487175679141002715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175586949658117119427335143 263380424487175679141002715)
    ·
      refine ⟨395070636730763518711504073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263380424487175679141002715 395070636730763518711504073)
      ·
        refine ⟨296302977548072639033628055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395070636730763518711504073 296302977548072639033628055)
        ·
          refine ⟨444454466322108958550442083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296302977548072639033628055 444454466322108958550442083)
          ·
            refine ⟨666681699483163437825663125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444454466322108958550442083 666681699483163437825663125)
            ·
              refine ⟨31250704663273286148077959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 666681699483163437825663125 31250704663273286148077959)
              ·
                refine ⟨46876056994909929222116939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31250704663273286148077959 46876056994909929222116939)
                ·
                  refine ⟨70314085492364893833175409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46876056994909929222116939 70314085492364893833175409)
                  ·
                    refine ⟨52735564119273670374881557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70314085492364893833175409 52735564119273670374881557)
                    ·
                      refine ⟨2471979568090953298822573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52735564119273670374881557 2471979568090953298822573)
                      ·
                        rfl

theorem cell23_4814163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 6].length) (baseStart_4814163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814163 prefixEnd_4814163 := by exact prefixLift 4814163
  have htrace : WordTrace (prefixWord ++ tailWord_4814163) baseStart_4814163 baseEnd_4814163 := by
    simpa [prefixWord, tailWord_4814163, baseEnd_4814163] using wordTrace_append hprefix tailTrace_4814163
  have hstable : (prefixWord ++ tailWord_4814163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814163).length < 2 ^ (prefixWord ++ tailWord_4814163).sum := by decide
  have hdescent : baseEnd_4814163 < baseStart_4814163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814164 : List Nat := [2, 4, 1, 1, 2, 1, 3, 4, 1, 4]
def baseStart_4814164 : Nat := 118140960795 + 4814164 * 2 ^ 59
def prefixEnd_4814164 : Nat := 4983230072969 + 3 ^ 40 * 4814164 * 2
def baseEnd_4814164 : Nat := 823993360523869264970023

theorem tailTrace_4814164 : CollatzResearch.WordTrace tailWord_4814164 prefixEnd_4814164 823993360523869264970023 := by
  unfold tailWord_4814164
  simp only [CollatzResearch.WordTrace]
  refine ⟨87793493065556748299060773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117057990754075664398747697 87793493065556748299060773)
  ·
    refine ⟨16461279949791890306073895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87793493065556748299060773 16461279949791890306073895)
    ·
      refine ⟨24691919924687835459110843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16461279949791890306073895 24691919924687835459110843)
      ·
        refine ⟨37037879887031753188666265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24691919924687835459110843 37037879887031753188666265)
        ·
          refine ⟨27778409915273814891499699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37037879887031753188666265 27778409915273814891499699)
          ·
            refine ⟨41667614872910722337249549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27778409915273814891499699 41667614872910722337249549)
            ·
              refine ⟨15625355577341520876468581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41667614872910722337249549 15625355577341520876468581)
              ·
                refine ⟨2929754170751535164337859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15625355577341520876468581 2929754170751535164337859)
                ·
                  refine ⟨4394631256127302746506789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2929754170751535164337859 4394631256127302746506789)
                  ·
                    refine ⟨823993360523869264970023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4394631256127302746506789 823993360523869264970023)
                    ·
                      rfl

theorem cell23_4814164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_4814164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814164 prefixEnd_4814164 := by exact prefixLift 4814164
  have htrace : WordTrace (prefixWord ++ tailWord_4814164) baseStart_4814164 baseEnd_4814164 := by
    simpa [prefixWord, tailWord_4814164, baseEnd_4814164] using wordTrace_append hprefix tailTrace_4814164
  have hstable : (prefixWord ++ tailWord_4814164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814164).length < 2 ^ (prefixWord ++ tailWord_4814164).sum := by decide
  have hdescent : baseEnd_4814164 < baseStart_4814164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814237 : List Nat := [1, 4, 2, 1, 3, 1, 3, 1, 1, 6]
def baseStart_4814237 : Nat := 118140960795 + 4814237 * 2 ^ 59
def prefixEnd_4814237 : Nat := 4983230072969 + 3 ^ 40 * 4814237 * 2
def baseEnd_4814237 : Nat := 824005855219795336432411

theorem tailTrace_4814237 : CollatzResearch.WordTrace tailWord_4814237 prefixEnd_4814237 824005855219795336432411 := by
  unfold tailWord_4814237
  simp only [CollatzResearch.WordTrace]
  refine ⟨175589648659849030065528965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117059765773232686710352643 175589648659849030065528965)
  ·
    refine ⟨32923059123721693137286681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175589648659849030065528965 32923059123721693137286681)
    ·
      refine ⟨24692294342791269852965011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32923059123721693137286681 24692294342791269852965011)
      ·
        refine ⟨37038441514186904779447517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24692294342791269852965011 37038441514186904779447517)
        ·
          refine ⟨13889415567820089292292819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37038441514186904779447517 13889415567820089292292819)
          ·
            refine ⟨20834123351730133938439229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13889415567820089292292819 20834123351730133938439229)
            ·
              refine ⟨7812796256898800226914711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20834123351730133938439229 7812796256898800226914711)
              ·
                refine ⟨11719194385348200340372067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7812796256898800226914711 11719194385348200340372067)
                ·
                  refine ⟨17578791578022300510558101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11719194385348200340372067 17578791578022300510558101)
                  ·
                    refine ⟨824005855219795336432411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17578791578022300510558101 824005855219795336432411)
                    ·
                      rfl

theorem cell23_4814237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_4814237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814237 prefixEnd_4814237 := by exact prefixLift 4814237
  have htrace : WordTrace (prefixWord ++ tailWord_4814237) baseStart_4814237 baseEnd_4814237 := by
    simpa [prefixWord, tailWord_4814237, baseEnd_4814237] using wordTrace_append hprefix tailTrace_4814237
  have hstable : (prefixWord ++ tailWord_4814237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814237).length < 2 ^ (prefixWord ++ tailWord_4814237).sum := by decide
  have hdescent : baseEnd_4814237 < baseStart_4814237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814240 : List Nat := [2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 6]
def baseStart_4814240 : Nat := 118140960795 + 4814240 * 2 ^ 59
def prefixEnd_4814240 : Nat := 4983230072969 + 3 ^ 40 * 4814240 * 2
def baseEnd_4814240 : Nat := 2472019106101349497559719

theorem tailTrace_4814240 : CollatzResearch.WordTrace tailWord_4814240 prefixEnd_4814240 2472019106101349497559719 := by
  unfold tailWord_4814240
  simp only [CollatzResearch.WordTrace]
  refine ⟨87794879039419080788944087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117059838719225441051925449 87794879039419080788944087)
  ·
    refine ⟨131692318559128621183416131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87794879039419080788944087 131692318559128621183416131)
    ·
      refine ⟨197538477838692931775124197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131692318559128621183416131 197538477838692931775124197)
      ·
        refine ⟨37038464594754924707835787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197538477838692931775124197 37038464594754924707835787)
        ·
          refine ⟨55557696892132387061753681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37038464594754924707835787 55557696892132387061753681)
          ·
            refine ⟨41668272669099290296315261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55557696892132387061753681 41668272669099290296315261)
            ·
              refine ⟨15625602250912233861118223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41668272669099290296315261 15625602250912233861118223)
              ·
                refine ⟨23438403376368350791677335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15625602250912233861118223 23438403376368350791677335)
                ·
                  refine ⟨35157605064552526187516003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23438403376368350791677335 35157605064552526187516003)
                  ·
                    refine ⟨52736407596828789281274005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35157605064552526187516003 52736407596828789281274005)
                    ·
                      refine ⟨2472019106101349497559719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52736407596828789281274005 2472019106101349497559719)
                      ·
                        rfl

theorem cell23_4814240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_4814240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814240 prefixEnd_4814240 := by exact prefixLift 4814240
  have htrace : WordTrace (prefixWord ++ tailWord_4814240) baseStart_4814240 baseEnd_4814240 := by
    simpa [prefixWord, tailWord_4814240, baseEnd_4814240] using wordTrace_append hprefix tailTrace_4814240
  have hstable : (prefixWord ++ tailWord_4814240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814240).length < 2 ^ (prefixWord ++ tailWord_4814240).sum := by decide
  have hdescent : baseEnd_4814240 < baseStart_4814240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814280 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 2, 7]
def baseStart_4814280 : Nat := 118140960795 + 4814280 * 2 ^ 59
def prefixEnd_4814280 : Nat := 4983230072969 + 3 ^ 40 * 4814280 * 2
def baseEnd_4814280 : Nat := 824013215109176447019845

theorem tailTrace_4814280 : CollatzResearch.WordTrace tailWord_4814280 prefixEnd_4814280 824013215109176447019845 := by
  unfold tailWord_4814280
  simp only [CollatzResearch.WordTrace]
  refine ⟨87795608499346624204672147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117060811332462165606229529 87795608499346624204672147)
  ·
    refine ⟨131693412749019936307008221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87795608499346624204672147 131693412749019936307008221)
    ·
      refine ⟨49385029780882476115128083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131693412749019936307008221 49385029780882476115128083)
      ·
        refine ⟨74077544671323714172692125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49385029780882476115128083 74077544671323714172692125)
        ·
          refine ⟨27779079251746392814759547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74077544671323714172692125 27779079251746392814759547)
          ·
            refine ⟨41668618877619589222139321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27779079251746392814759547 41668618877619589222139321)
            ·
              refine ⟨31251464158214691916604491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41668618877619589222139321 31251464158214691916604491)
              ·
                refine ⟨46877196237322037874906737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31251464158214691916604491 46877196237322037874906737)
                ·
                  refine ⟨35157897177991528406180053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46877196237322037874906737 35157897177991528406180053)
                  ·
                    refine ⟨824013215109176447019845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35157897177991528406180053 824013215109176447019845)
                    ·
                      rfl

theorem cell23_4814280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_4814280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814280 prefixEnd_4814280 := by exact prefixLift 4814280
  have htrace : WordTrace (prefixWord ++ tailWord_4814280) baseStart_4814280 baseEnd_4814280 := by
    simpa [prefixWord, tailWord_4814280, baseEnd_4814280] using wordTrace_append hprefix tailTrace_4814280
  have hstable : (prefixWord ++ tailWord_4814280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814280).length < 2 ^ (prefixWord ++ tailWord_4814280).sum := by decide
  have hdescent : baseEnd_4814280 < baseStart_4814280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814304 : List Nat := [2, 1, 1, 3, 1, 1, 2, 6, 1, 3, 2]
def baseStart_4814304 : Nat := 118140960795 + 4814304 * 2 ^ 59
def prefixEnd_4814304 : Nat := 4983230072969 + 3 ^ 40 * 4814304 * 2
def baseEnd_4814304 : Nat := 2472051968863237247159425

theorem tailTrace_4814304 : CollatzResearch.WordTrace tailWord_4814304 prefixEnd_4814304 2472051968863237247159425 := by
  unfold tailWord_4814304
  simp only [CollatzResearch.WordTrace]
  refine ⟨87796046175303150254108983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117061394900404200338811977 87796046175303150254108983)
  ·
    refine ⟨131694069262954725381163475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87796046175303150254108983 131694069262954725381163475)
    ·
      refine ⟨197541103894432088071745213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131694069262954725381163475 197541103894432088071745213)
      ·
        refine ⟨74077913960412033026904455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197541103894432088071745213 74077913960412033026904455)
        ·
          refine ⟨111116870940618049540356683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74077913960412033026904455 111116870940618049540356683)
          ·
            refine ⟨166675306410927074310535025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111116870940618049540356683 166675306410927074310535025)
            ·
              refine ⟨125006479808195305732901269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166675306410927074310535025 125006479808195305732901269)
              ·
                refine ⟨5859678741009154956229747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 125006479808195305732901269 5859678741009154956229747)
                ·
                  refine ⟨8789518111513732434344621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5859678741009154956229747 8789518111513732434344621)
                  ·
                    refine ⟨3296069291817649662879233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8789518111513732434344621 3296069291817649662879233)
                    ·
                      refine ⟨2472051968863237247159425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3296069291817649662879233 2472051968863237247159425)
                      ·
                        rfl

theorem cell23_4814304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 1, 3, 2].length) (baseStart_4814304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814304 prefixEnd_4814304 := by exact prefixLift 4814304
  have htrace : WordTrace (prefixWord ++ tailWord_4814304) baseStart_4814304 baseEnd_4814304 := by
    simpa [prefixWord, tailWord_4814304, baseEnd_4814304] using wordTrace_append hprefix tailTrace_4814304
  have hstable : (prefixWord ++ tailWord_4814304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814304).length < 2 ^ (prefixWord ++ tailWord_4814304).sum := by decide
  have hdescent : baseEnd_4814304 < baseStart_4814304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814357 : List Nat := [1, 3, 2, 1, 3, 3, 1, 2, 7]
def baseStart_4814357 : Nat := 118140960795 + 4814357 * 2 ^ 59
def prefixEnd_4814357 : Nat := 4983230072969 + 3 ^ 40 * 4814357 * 2
def baseEnd_4814357 : Nat := 274675464815325059977409

theorem tailTrace_4814357 : CollatzResearch.WordTrace tailWord_4814357 prefixEnd_4814357 274675464815325059977409 := by
  unfold tailWord_4814357
  simp only [CollatzResearch.WordTrace]
  refine ⟨175594025419414290559897325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117062683612942860373264883 175594025419414290559897325)
  ·
    refine ⟨65847759532280358959961497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175594025419414290559897325 65847759532280358959961497)
    ·
      refine ⟨49385819649210269219971123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65847759532280358959961497 49385819649210269219971123)
      ·
        refine ⟨74078729473815403829956685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49385819649210269219971123 74078729473815403829956685)
        ·
          refine ⟨27779523552680776436233757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74078729473815403829956685 27779523552680776436233757)
          ·
            refine ⟨10417321332255291163587659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27779523552680776436233757 10417321332255291163587659)
            ·
              refine ⟨15625981998382936745381489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10417321332255291163587659 15625981998382936745381489)
              ·
                refine ⟨11719486498787202559036117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15625981998382936745381489 11719486498787202559036117)
                ·
                  refine ⟨274675464815325059977409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11719486498787202559036117 274675464815325059977409)
                  ·
                    rfl

theorem cell23_4814357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 7].length) (baseStart_4814357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814357 prefixEnd_4814357 := by exact prefixLift 4814357
  have htrace : WordTrace (prefixWord ++ tailWord_4814357) baseStart_4814357 baseEnd_4814357 := by
    simpa [prefixWord, tailWord_4814357, baseEnd_4814357] using wordTrace_append hprefix tailTrace_4814357
  have hstable : (prefixWord ++ tailWord_4814357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814357).length < 2 ^ (prefixWord ++ tailWord_4814357).sum := by decide
  have hdescent : baseEnd_4814357 < baseStart_4814357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814447 : List Nat := [1, 1, 2, 1, 3, 2, 1, 6, 6]
def baseStart_4814447 : Nat := 118140960795 + 4814447 * 2 ^ 59
def prefixEnd_4814447 : Nat := 4983230072969 + 3 ^ 40 * 4814447 * 2
def baseEnd_4814447 : Nat := 274680599621870020852363

theorem tailTrace_4814447 : CollatzResearch.WordTrace tailWord_4814447 prefixEnd_4814447 274680599621870020852363 := by
  unfold tailWord_4814447
  simp only [CollatzResearch.WordTrace]
  refine ⟨175597307989088235930673595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117064871992725490620449063 175597307989088235930673595)
  ·
    refine ⟨263395961983632353896010393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175597307989088235930673595 263395961983632353896010393)
    ·
      refine ⟨197546971487724265422007795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263395961983632353896010393 197546971487724265422007795)
      ·
        refine ⟨296320457231586398133011693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197546971487724265422007795 296320457231586398133011693)
        ·
          refine ⟨111120171461844899299879385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 296320457231586398133011693 111120171461844899299879385)
          ·
            refine ⟨83340128596383674474909539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111120171461844899299879385 83340128596383674474909539)
            ·
              refine ⟨125010192894575511712364309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83340128596383674474909539 125010192894575511712364309)
              ·
                refine ⟨5859852791933227111517077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 125010192894575511712364309 5859852791933227111517077)
                ·
                  refine ⟨274680599621870020852363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5859852791933227111517077 274680599621870020852363)
                  ·
                    rfl

theorem cell23_4814447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 6].length) (baseStart_4814447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814447 prefixEnd_4814447 := by exact prefixLift 4814447
  have htrace : WordTrace (prefixWord ++ tailWord_4814447) baseStart_4814447 baseEnd_4814447 := by
    simpa [prefixWord, tailWord_4814447, baseEnd_4814447] using wordTrace_append hprefix tailTrace_4814447
  have hstable : (prefixWord ++ tailWord_4814447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814447).length < 2 ^ (prefixWord ++ tailWord_4814447).sum := by decide
  have hdescent : baseEnd_4814447 < baseStart_4814447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814498 : List Nat := [3, 3, 1, 4, 1, 1, 2, 2, 6]
def baseStart_4814498 : Nat := 118140960795 + 4814498 * 2 ^ 59
def prefixEnd_4814498 : Nat := 4983230072969 + 3 ^ 40 * 4814498 * 2
def baseEnd_4814498 : Nat := 274683509345578832014837

theorem tailTrace_4814498 : CollatzResearch.WordTrace tailWord_4814498 prefixEnd_4814498 274683509345578832014837 := by
  unfold tailWord_4814498
  simp only [CollatzResearch.WordTrace]
  refine ⟨43899792027975867910195037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117066112074602314427186765 43899792027975867910195037)
  ·
    refine ⟨16462422010490950466323139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43899792027975867910195037 16462422010490950466323139)
    ·
      refine ⟨24693633015736425699484709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16462422010490950466323139 24693633015736425699484709)
      ·
        refine ⟨4630056190450579818653383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24693633015736425699484709 4630056190450579818653383)
        ·
          refine ⟨6945084285675869727980075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4630056190450579818653383 6945084285675869727980075)
          ·
            refine ⟨10417626428513804591970113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6945084285675869727980075 10417626428513804591970113)
            ·
              refine ⟨7813219821385353443977585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10417626428513804591970113 7813219821385353443977585)
              ·
                refine ⟨5859914866039015082983189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7813219821385353443977585 5859914866039015082983189)
                ·
                  refine ⟨274683509345578832014837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5859914866039015082983189 274683509345578832014837)
                  ·
                    rfl

theorem cell23_4814498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_4814498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814498 prefixEnd_4814498 := by exact prefixLift 4814498
  have htrace : WordTrace (prefixWord ++ tailWord_4814498) baseStart_4814498 baseEnd_4814498 := by
    simpa [prefixWord, tailWord_4814498, baseEnd_4814498] using wordTrace_append hprefix tailTrace_4814498
  have hstable : (prefixWord ++ tailWord_4814498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814498).length < 2 ^ (prefixWord ++ tailWord_4814498).sum := by decide
  have hdescent : baseEnd_4814498 < baseStart_4814498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814501 : List Nat := [1, 3, 1, 2, 1, 2, 4, 2, 2, 3, 2]
def baseStart_4814501 : Nat := 118140960795 + 4814501 * 2 ^ 59
def prefixEnd_4814501 : Nat := 4983230072969 + 3 ^ 40 * 4814501 * 2
def baseEnd_4814501 : Nat := 2472153124552172976396019

theorem tailTrace_4814501 : CollatzResearch.WordTrace tailWord_4814501 prefixEnd_4814501 2472153124552172976396019 := by
  unfold tailWord_4814501
  simp only [CollatzResearch.WordTrace]
  refine ⟨175599277530892603153139357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117066185020595068768759571 175599277530892603153139357)
  ·
    refine ⟨65849729074084726182427259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175599277530892603153139357 65849729074084726182427259)
    ·
      refine ⟨98774593611127089273640889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65849729074084726182427259 98774593611127089273640889)
      ·
        refine ⟨74080945208345316955230667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98774593611127089273640889 74080945208345316955230667)
        ·
          refine ⟨111121417812517975432846001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74080945208345316955230667 111121417812517975432846001)
          ·
            refine ⟨83341063359388481574634501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111121417812517975432846001 83341063359388481574634501)
            ·
              refine ⟨15626449379885340295243969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83341063359388481574634501 15626449379885340295243969)
              ·
                refine ⟨11719837034914005221432977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15626449379885340295243969 11719837034914005221432977)
                ·
                  refine ⟨8789877776185503916074733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11719837034914005221432977 8789877776185503916074733)
                  ·
                    refine ⟨3296204166069563968528025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8789877776185503916074733 3296204166069563968528025)
                    ·
                      refine ⟨2472153124552172976396019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3296204166069563968528025 2472153124552172976396019)
                      ·
                        rfl

theorem cell23_4814501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 3, 2].length) (baseStart_4814501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814501 prefixEnd_4814501 := by exact prefixLift 4814501
  have htrace : WordTrace (prefixWord ++ tailWord_4814501) baseStart_4814501 baseEnd_4814501 := by
    simpa [prefixWord, tailWord_4814501, baseEnd_4814501] using wordTrace_append hprefix tailTrace_4814501
  have hstable : (prefixWord ++ tailWord_4814501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814501).length < 2 ^ (prefixWord ++ tailWord_4814501).sum := by decide
  have hdescent : baseEnd_4814501 < baseStart_4814501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814514 : List Nat := [3, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4]
def baseStart_4814514 : Nat := 118140960795 + 4814514 * 2 ^ 59
def prefixEnd_4814514 : Nat := 4983230072969 + 3 ^ 40 * 4814514 * 2
def baseEnd_4814514 : Nat := 2472159799800681425533459

theorem tailTrace_4814514 : CollatzResearch.WordTrace tailWord_4814514 prefixEnd_4814514 2472159799800681425533459 := by
  unfold tailWord_4814514
  simp only [CollatzResearch.WordTrace]
  refine ⟨43899937919961376593340649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117066501119897004248908397 43899937919961376593340649)
  ·
    refine ⟨32924953439971032445005487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43899937919961376593340649 32924953439971032445005487)
    ·
      refine ⟨49387430159956548667508231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32924953439971032445005487 49387430159956548667508231)
      ·
        refine ⟨74081145239934823001262347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49387430159956548667508231 74081145239934823001262347)
        ·
          refine ⟨111121717859902234501893521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74081145239934823001262347 111121717859902234501893521)
          ·
            refine ⟨83341288394926675876420141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111121717859902234501893521 83341288394926675876420141)
            ·
              refine ⟨31252983148097503453657553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83341288394926675876420141 31252983148097503453657553)
              ·
                refine ⟨23439737361073127590243165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31252983148097503453657553 23439737361073127590243165)
                ·
                  refine ⟨8789901510402422846341187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23439737361073127590243165 8789901510402422846341187)
                  ·
                    refine ⟨13184852265603634269511781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8789901510402422846341187 13184852265603634269511781)
                    ·
                      refine ⟨2472159799800681425533459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13184852265603634269511781 2472159799800681425533459)
                      ·
                        rfl

theorem cell23_4814514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_4814514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814514 prefixEnd_4814514 := by exact prefixLift 4814514
  have htrace : WordTrace (prefixWord ++ tailWord_4814514) baseStart_4814514 baseEnd_4814514 := by
    simpa [prefixWord, tailWord_4814514, baseEnd_4814514] using wordTrace_append hprefix tailTrace_4814514
  have hstable : (prefixWord ++ tailWord_4814514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814514).length < 2 ^ (prefixWord ++ tailWord_4814514).sum := by decide
  have hdescent : baseEnd_4814514 < baseStart_4814514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814524 : List Nat := [2, 2, 2, 3, 1, 2, 1, 3, 1, 6]
def baseStart_4814524 : Nat := 118140960795 + 4814524 * 2 ^ 59
def prefixEnd_4814524 : Nat := 4983230072969 + 3 ^ 40 * 4814524 * 2
def baseEnd_4814524 : Nat := 824054978202408795469471

theorem tailTrace_4814524 : CollatzResearch.WordTrace tailWord_4814524 prefixEnd_4814524 824054978202408795469471 := by
  unfold tailWord_4814524
  simp only [CollatzResearch.WordTrace]
  refine ⟨87800058204904639040613313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117066744273206185387484417 87800058204904639040613313)
  ·
    refine ⟨65850043653678479280459985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87800058204904639040613313 65850043653678479280459985)
    ·
      refine ⟨49387532740258859460344989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65850043653678479280459985 49387532740258859460344989)
      ·
        refine ⟨18520324777597072297629371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49387532740258859460344989 18520324777597072297629371)
        ·
          refine ⟨27780487166395608446444057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18520324777597072297629371 27780487166395608446444057)
          ·
            refine ⟨20835365374796706334833043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27780487166395608446444057 20835365374796706334833043)
            ·
              refine ⟨31253048062195059502249565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20835365374796706334833043 31253048062195059502249565)
              ·
                refine ⟨11719893023323147313343587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31253048062195059502249565 11719893023323147313343587)
                ·
                  refine ⟨17579839534984720970015381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11719893023323147313343587 17579839534984720970015381)
                  ·
                    refine ⟨824054978202408795469471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17579839534984720970015381 824054978202408795469471)
                    ·
                      rfl

theorem cell23_4814524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_4814524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814524 prefixEnd_4814524 := by exact prefixLift 4814524
  have htrace : WordTrace (prefixWord ++ tailWord_4814524) baseStart_4814524 baseEnd_4814524 := by
    simpa [prefixWord, tailWord_4814524, baseEnd_4814524] using wordTrace_append hprefix tailTrace_4814524
  have hstable : (prefixWord ++ tailWord_4814524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814524).length < 2 ^ (prefixWord ++ tailWord_4814524).sum := by decide
  have hdescent : baseEnd_4814524 < baseStart_4814524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814548 : List Nat := [2, 4, 1, 3, 1, 2, 1, 3, 1, 1, 4]
def baseStart_4814548 : Nat := 118140960795 + 4814548 * 2 ^ 59
def prefixEnd_4814548 : Nat := 4983230072969 + 3 ^ 40 * 4814548 * 2
def baseEnd_4814548 : Nat := 2472177258142934292508303

theorem tailTrace_4814548 : CollatzResearch.WordTrace tailWord_4814548 prefixEnd_4814548 2472177258142934292508303 := by
  unfold tailWord_4814548
  simp only [CollatzResearch.WordTrace]
  refine ⟨87800495880861165090050149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117067327841148220120066865 87800495880861165090050149)
  ·
    refine ⟨16462592977661468454384403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87800495880861165090050149 16462592977661468454384403)
    ·
      refine ⟨24693889466492202681576605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16462592977661468454384403 24693889466492202681576605)
      ·
        refine ⟨9260208549934576005591227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24693889466492202681576605 9260208549934576005591227)
        ·
          refine ⟨13890312824901864008386841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9260208549934576005591227 13890312824901864008386841)
          ·
            refine ⟨10417734618676398006290131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13890312824901864008386841 10417734618676398006290131)
            ·
              refine ⟨15626601928014597009435197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10417734618676398006290131 15626601928014597009435197)
              ·
                refine ⟨5859975723005473878538199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15626601928014597009435197 5859975723005473878538199)
                ·
                  refine ⟨8789963584508210817807299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5859975723005473878538199 8789963584508210817807299)
                  ·
                    refine ⟨13184945376762316226710949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8789963584508210817807299 13184945376762316226710949)
                    ·
                      refine ⟨2472177258142934292508303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13184945376762316226710949 2472177258142934292508303)
                      ·
                        rfl

theorem cell23_4814548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_4814548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814548 prefixEnd_4814548 := by exact prefixLift 4814548
  have htrace : WordTrace (prefixWord ++ tailWord_4814548) baseStart_4814548 baseEnd_4814548 := by
    simpa [prefixWord, tailWord_4814548, baseEnd_4814548] using wordTrace_append hprefix tailTrace_4814548
  have hstable : (prefixWord ++ tailWord_4814548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814548).length < 2 ^ (prefixWord ++ tailWord_4814548).sum := by decide
  have hdescent : baseEnd_4814548 < baseStart_4814548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814551 : List Nat := [1, 1, 3, 2, 1, 3, 3, 3, 1, 2, 3]
def baseStart_4814551 : Nat := 118140960795 + 4814551 * 2 ^ 59
def prefixEnd_4814551 : Nat := 4983230072969 + 3 ^ 40 * 4814551 * 2
def baseEnd_4814551 : Nat := 2472178798584897780770789

theorem tailTrace_4814551 : CollatzResearch.WordTrace tailWord_4814551 prefixEnd_4814551 2472178798584897780770789 := by
  unfold tailWord_4814551
  simp only [CollatzResearch.WordTrace]
  refine ⟨175601101180711461692459507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117067400787140974461639671 175601101180711461692459507)
  ·
    refine ⟨263401651771067192538689261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175601101180711461692459507 263401651771067192538689261)
    ·
      refine ⟨98775619414150197202008473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263401651771067192538689261 98775619414150197202008473)
      ·
        refine ⟨74081714560612647901506355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98775619414150197202008473 74081714560612647901506355)
        ·
          refine ⟨111122571840918971852259533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74081714560612647901506355 111122571840918971852259533)
          ·
            refine ⟨41670964440344614444597325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111122571840918971852259533 41670964440344614444597325)
            ·
              refine ⟨15626611665129230416723997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41670964440344614444597325 15626611665129230416723997)
              ·
                refine ⟨5859979374423461406271499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15626611665129230416723997 5859979374423461406271499)
                ·
                  refine ⟨8789969061635192109407249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5859979374423461406271499 8789969061635192109407249)
                  ·
                    refine ⟨6592476796226394082055437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8789969061635192109407249 6592476796226394082055437)
                    ·
                      refine ⟨2472178798584897780770789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6592476796226394082055437 2472178798584897780770789)
                      ·
                        rfl

theorem cell23_4814551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_4814551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814551 prefixEnd_4814551 := by exact prefixLift 4814551
  have htrace : WordTrace (prefixWord ++ tailWord_4814551) baseStart_4814551 baseEnd_4814551 := by
    simpa [prefixWord, tailWord_4814551, baseEnd_4814551] using wordTrace_append hprefix tailTrace_4814551
  have hstable : (prefixWord ++ tailWord_4814551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814551).length < 2 ^ (prefixWord ++ tailWord_4814551).sum := by decide
  have hdescent : baseEnd_4814551 < baseStart_4814551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814565 : List Nat := [1, 3, 1, 4, 1, 1, 1, 6, 1, 2, 2]
def baseStart_4814565 : Nat := 118140960795 + 4814565 * 2 ^ 59
def prefixEnd_4814565 : Nat := 4983230072969 + 3 ^ 40 * 4814565 * 2
def baseEnd_4814565 : Nat := 2472185987314060725995725

theorem tailTrace_4814565 : CollatzResearch.WordTrace tailWord_4814565 prefixEnd_4814565 2472185987314060725995725 := by
  unfold tailWord_4814565
  simp only [CollatzResearch.WordTrace]
  refine ⟨175601611802660742083469149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117067741201773828055646099 175601611802660742083469149)
  ·
    refine ⟨65850604425997778281300931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175601611802660742083469149 65850604425997778281300931)
    ·
      refine ⟨98775906638996667421951397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65850604425997778281300931 98775906638996667421951397)
      ·
        refine ⟨18520482494811875141615887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98775906638996667421951397 18520482494811875141615887)
        ·
          refine ⟨27780723742217812712423831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18520482494811875141615887 27780723742217812712423831)
          ·
            refine ⟨41671085613326719068635747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27780723742217812712423831 41671085613326719068635747)
            ·
              refine ⟨62506628419990078602953621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41671085613326719068635747 62506628419990078602953621)
              ·
                refine ⟨2929998207187034934513451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62506628419990078602953621 2929998207187034934513451)
                ·
                  refine ⟨4394997310780552401770177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2929998207187034934513451 4394997310780552401770177)
                  ·
                    refine ⟨3296247983085414301327633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4394997310780552401770177 3296247983085414301327633)
                    ·
                      refine ⟨2472185987314060725995725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3296247983085414301327633 2472185987314060725995725)
                      ·
                        rfl

theorem cell23_4814565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_4814565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814565 prefixEnd_4814565 := by exact prefixLift 4814565
  have htrace : WordTrace (prefixWord ++ tailWord_4814565) baseStart_4814565 baseEnd_4814565 := by
    simpa [prefixWord, tailWord_4814565, baseEnd_4814565] using wordTrace_append hprefix tailTrace_4814565
  have hstable : (prefixWord ++ tailWord_4814565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814565).length < 2 ^ (prefixWord ++ tailWord_4814565).sum := by decide
  have hdescent : baseEnd_4814565 < baseStart_4814565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814587 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 8]
def baseStart_4814587 : Nat := 118140960795 + 4814587 * 2 ^ 59
def prefixEnd_4814587 : Nat := 4983230072969 + 3 ^ 40 * 4814587 * 2
def baseEnd_4814587 : Nat := 2472197283888459639920623

theorem tailTrace_4814587 : CollatzResearch.WordTrace tailWord_4814587 prefixEnd_4814587 2472197283888459639920623 := by
  unfold tailWord_4814587
  simp only [CollatzResearch.WordTrace]
  refine ⟨175602414208581039840770015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117068276139054026560513343 175602414208581039840770015)
  ·
    refine ⟨263403621312871559761155023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175602414208581039840770015 263403621312871559761155023)
    ·
      refine ⟨395105431969307339641732535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263403621312871559761155023 395105431969307339641732535)
      ·
        refine ⟨592658147953961009462598803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395105431969307339641732535 592658147953961009462598803)
        ·
          refine ⟨888987221930941514193898205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 592658147953961009462598803 888987221930941514193898205)
          ·
            refine ⟨333370208224103067822711827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 888987221930941514193898205 333370208224103067822711827)
            ·
              refine ⟨500055312336154601734067741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333370208224103067822711827 500055312336154601734067741)
              ·
                refine ⟨187520742126057975650275403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 500055312336154601734067741 187520742126057975650275403)
                ·
                  refine ⟨281281113189086963475413105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187520742126057975650275403 281281113189086963475413105)
                  ·
                    refine ⟨210960834891815222606559829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 281281113189086963475413105 210960834891815222606559829)
                    ·
                      refine ⟨2472197283888459639920623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 210960834891815222606559829 2472197283888459639920623)
                      ·
                        rfl

theorem cell23_4814587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 8].length) (baseStart_4814587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814587 prefixEnd_4814587 := by exact prefixLift 4814587
  have htrace : WordTrace (prefixWord ++ tailWord_4814587) baseStart_4814587 baseEnd_4814587 := by
    simpa [prefixWord, tailWord_4814587, baseEnd_4814587] using wordTrace_append hprefix tailTrace_4814587
  have hstable : (prefixWord ++ tailWord_4814587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814587).length < 2 ^ (prefixWord ++ tailWord_4814587).sum := by decide
  have hdescent : baseEnd_4814587 < baseStart_4814587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814591 : List Nat := [1, 1, 2, 2, 1, 3, 2, 3, 3, 3, 2]
def baseStart_4814591 : Nat := 118140960795 + 4814591 * 2 ^ 59
def prefixEnd_4814591 : Nat := 4983230072969 + 3 ^ 40 * 4814591 * 2
def baseEnd_4814591 : Nat := 2472199337811077624270605

theorem tailTrace_4814591 : CollatzResearch.WordTrace tailWord_4814591 prefixEnd_4814591 2472199337811077624270605 := by
  unfold tailWord_4814591
  simp only [CollatzResearch.WordTrace]
  refine ⟨175602560100566548523915627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117068373400377699015943751 175602560100566548523915627)
  ·
    refine ⟨263403840150849822785873441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175602560100566548523915627 263403840150849822785873441)
    ·
      refine ⟨197552880113137367089405081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263403840150849822785873441 197552880113137367089405081)
      ·
        refine ⟨148164660084853025317053811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197552880113137367089405081 148164660084853025317053811)
        ·
          refine ⟨222246990127279537975580717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148164660084853025317053811 222246990127279537975580717)
          ·
            refine ⟨83342621297729826740842769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222246990127279537975580717 83342621297729826740842769)
            ·
              refine ⟨62506965973297370055632077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83342621297729826740842769 62506965973297370055632077)
              ·
                refine ⟨23440112239986513770862029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62506965973297370055632077 23440112239986513770862029)
                ·
                  refine ⟨8790042089994942664073261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23440112239986513770862029 8790042089994942664073261)
                  ·
                    refine ⟨3296265783748103499027473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8790042089994942664073261 3296265783748103499027473)
                    ·
                      refine ⟨2472199337811077624270605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3296265783748103499027473 2472199337811077624270605)
                      ·
                        rfl

theorem cell23_4814591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 3, 2].length) (baseStart_4814591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814591 prefixEnd_4814591 := by exact prefixLift 4814591
  have htrace : WordTrace (prefixWord ++ tailWord_4814591) baseStart_4814591 baseEnd_4814591 := by
    simpa [prefixWord, tailWord_4814591, baseEnd_4814591] using wordTrace_append hprefix tailTrace_4814591
  have hstable : (prefixWord ++ tailWord_4814591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814591).length < 2 ^ (prefixWord ++ tailWord_4814591).sum := by decide
  have hdescent : baseEnd_4814591 < baseStart_4814591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814599 : List Nat := [1, 1, 4, 4, 2, 2, 1, 3, 1, 2, 2]
def baseStart_4814599 : Nat := 118140960795 + 4814599 * 2 ^ 59
def prefixEnd_4814599 : Nat := 4983230072969 + 3 ^ 40 * 4814599 * 2
def baseEnd_4814599 : Nat := 2472203445656313592970569

theorem tailTrace_4814599 : CollatzResearch.WordTrace tailWord_4814599 prefixEnd_4814599 2472203445656313592970569 := by
  unfold tailWord_4814599
  simp only [CollatzResearch.WordTrace]
  refine ⟨175602851884537565890206851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117068567923025043926804567 175602851884537565890206851)
  ·
    refine ⟨263404277826806348835310277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175602851884537565890206851 263404277826806348835310277)
    ·
      refine ⟨49388302092526190406620677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 263404277826806348835310277 49388302092526190406620677)
      ·
        refine ⟨9260306642348660701241377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49388302092526190406620677 9260306642348660701241377)
        ·
          refine ⟨6945229981761495525931033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9260306642348660701241377 6945229981761495525931033)
          ·
            refine ⟨5208922486321121644448275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6945229981761495525931033 5208922486321121644448275)
            ·
              refine ⟨7813383729481682466672413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5208922486321121644448275 7813383729481682466672413)
              ·
                refine ⟨2930018898555630925002155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7813383729481682466672413 2930018898555630925002155)
                ·
                  refine ⟨4395028347833446387503233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2930018898555630925002155 4395028347833446387503233)
                  ·
                    refine ⟨3296271260875084790627425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4395028347833446387503233 3296271260875084790627425)
                    ·
                      refine ⟨2472203445656313592970569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3296271260875084790627425 2472203445656313592970569)
                      ·
                        rfl

theorem cell23_4814599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_4814599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814599 prefixEnd_4814599 := by exact prefixLift 4814599
  have htrace : WordTrace (prefixWord ++ tailWord_4814599) baseStart_4814599 baseEnd_4814599 := by
    simpa [prefixWord, tailWord_4814599, baseEnd_4814599] using wordTrace_append hprefix tailTrace_4814599
  have hstable : (prefixWord ++ tailWord_4814599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814599).length < 2 ^ (prefixWord ++ tailWord_4814599).sum := by decide
  have hdescent : baseEnd_4814599 < baseStart_4814599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814624 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 5]
def baseStart_4814624 : Nat := 118140960795 + 4814624 * 2 ^ 59
def prefixEnd_4814624 : Nat := 4983230072969 + 3 ^ 40 * 4814624 * 2
def baseEnd_4814624 : Nat := 2472216282672675995157953

theorem tailTrace_4814624 : CollatzResearch.WordTrace tailWord_4814624 prefixEnd_4814624 2472216282672675995157953 := by
  unfold tailWord_4814624
  simp only [CollatzResearch.WordTrace]
  refine ⟨87801881854723497579933463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117069175806297996773244617 87801881854723497579933463)
  ·
    refine ⟨131702822782085246369900195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87801881854723497579933463 131702822782085246369900195)
    ·
      refine ⟨197554234173127869554850293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131702822782085246369900195 197554234173127869554850293)
      ·
        refine ⟨18520709453730737770767215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 197554234173127869554850293 18520709453730737770767215)
        ·
          refine ⟨27781064180596106656150823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18520709453730737770767215 27781064180596106656150823)
          ·
            refine ⟨41671596270894159984226235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27781064180596106656150823 41671596270894159984226235)
            ·
              refine ⟨62507394406341239976339353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41671596270894159984226235 62507394406341239976339353)
              ·
                refine ⟨46880545804755929982254515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62507394406341239976339353 46880545804755929982254515)
                ·
                  refine ⟨70320818707133894973381773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46880545804755929982254515 70320818707133894973381773)
                  ·
                    refine ⟨26370307015175210615018165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70320818707133894973381773 26370307015175210615018165)
                    ·
                      refine ⟨2472216282672675995157953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26370307015175210615018165 2472216282672675995157953)
                      ·
                        rfl

theorem cell23_4814624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_4814624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814624 prefixEnd_4814624 := by exact prefixLift 4814624
  have htrace : WordTrace (prefixWord ++ tailWord_4814624) baseStart_4814624 baseEnd_4814624 := by
    simpa [prefixWord, tailWord_4814624, baseEnd_4814624] using wordTrace_append hprefix tailTrace_4814624
  have hstable : (prefixWord ++ tailWord_4814624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814624).length < 2 ^ (prefixWord ++ tailWord_4814624).sum := by decide
  have hdescent : baseEnd_4814624 < baseStart_4814624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814632 : List Nat := [2, 1, 5, 1, 1, 4, 2, 1, 2, 1, 3]
def baseStart_4814632 : Nat := 118140960795 + 4814632 * 2 ^ 59
def prefixEnd_4814632 : Nat := 4983230072969 + 3 ^ 40 * 4814632 * 2
def baseEnd_4814632 : Nat := 2472220390517911963857917

theorem tailTrace_4814632 : CollatzResearch.WordTrace tailWord_4814632 prefixEnd_4814632 2472220390517911963857917 := by
  unfold tailWord_4814632
  simp only [CollatzResearch.WordTrace]
  refine ⟨87802027746709006263079075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117069370328945341684105433 87802027746709006263079075)
  ·
    refine ⟨131703041620063509394618613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87802027746709006263079075 131703041620063509394618613)
    ·
      refine ⟨12347160151880954005745495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131703041620063509394618613 12347160151880954005745495)
      ·
        refine ⟨18520740227821431008618243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12347160151880954005745495 18520740227821431008618243)
        ·
          refine ⟨27781110341732146512927365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18520740227821431008618243 27781110341732146512927365)
          ·
            refine ⟨5208958189074777471173881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27781110341732146512927365 5208958189074777471173881)
            ·
              refine ⟨3906718641806083103380411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5208958189074777471173881 3906718641806083103380411)
              ·
                refine ⟨5860077962709124655070617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3906718641806083103380411 5860077962709124655070617)
                ·
                  refine ⟨4395058472031843491302963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5860077962709124655070617 4395058472031843491302963)
                  ·
                    refine ⟨6592587708047765236954445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4395058472031843491302963 6592587708047765236954445)
                    ·
                      refine ⟨2472220390517911963857917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6592587708047765236954445 2472220390517911963857917)
                      ·
                        rfl

theorem cell23_4814632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_4814632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814632 prefixEnd_4814632 := by exact prefixLift 4814632
  have htrace : WordTrace (prefixWord ++ tailWord_4814632) baseStart_4814632 baseEnd_4814632 := by
    simpa [prefixWord, tailWord_4814632, baseEnd_4814632] using wordTrace_append hprefix tailTrace_4814632
  have hstable : (prefixWord ++ tailWord_4814632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814632).length < 2 ^ (prefixWord ++ tailWord_4814632).sum := by decide
  have hdescent : baseEnd_4814632 < baseStart_4814632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814661 : List Nat := [1, 3, 1, 1, 1, 2, 4, 5, 5]
def baseStart_4814661 : Nat := 118140960795 + 4814661 * 2 ^ 59
def prefixEnd_4814661 : Nat := 4983230072969 + 3 ^ 40 * 4814661 * 2
def baseEnd_4814661 : Nat := 274692809050765816710587

theorem tailTrace_4814661 : CollatzResearch.WordTrace tailWord_4814661 prefixEnd_4814661 274692809050765816710587 := by
  unfold tailWord_4814661
  simp only [CollatzResearch.WordTrace]
  refine ⟨175605113210312950478963837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117070075473541966985975891 175605113210312950478963837)
  ·
    refine ⟨65851917453867356429611439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175605113210312950478963837 65851917453867356429611439)
    ·
      refine ⟨98777876180801034644417159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65851917453867356429611439 98777876180801034644417159)
      ·
        refine ⟨148166814271201551966625739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98777876180801034644417159 148166814271201551966625739)
        ·
          refine ⟨222250221406802327949938609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148166814271201551966625739 222250221406802327949938609)
          ·
            refine ⟨166687666055101745962453957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222250221406802327949938609 166687666055101745962453957)
            ·
              refine ⟨31253937385331577367960117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 166687666055101745962453957 31253937385331577367960117)
              ·
                refine ⟨2930056629874835378246261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31253937385331577367960117 2930056629874835378246261)
                ·
                  refine ⟨274692809050765816710587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2930056629874835378246261 274692809050765816710587)
                  ·
                    rfl

theorem cell23_4814661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 5].length) (baseStart_4814661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814661 prefixEnd_4814661 := by exact prefixLift 4814661
  have htrace : WordTrace (prefixWord ++ tailWord_4814661) baseStart_4814661 baseEnd_4814661 := by
    simpa [prefixWord, tailWord_4814661, baseEnd_4814661] using wordTrace_append hprefix tailTrace_4814661
  have hstable : (prefixWord ++ tailWord_4814661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814661).length < 2 ^ (prefixWord ++ tailWord_4814661).sum := by decide
  have hdescent : baseEnd_4814661 < baseStart_4814661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814681 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 1, 7, 2]
def baseStart_4814681 : Nat := 118140960795 + 4814681 * 2 ^ 59
def prefixEnd_4814681 : Nat := 4983230072969 + 3 ^ 40 * 4814681 * 2
def baseEnd_4814681 : Nat := 2472245551069982272145191

theorem tailTrace_4814681 : CollatzResearch.WordTrace tailWord_4814681 prefixEnd_4814681 2472245551069982272145191 := by
  unfold tailWord_4814681
  simp only [CollatzResearch.WordTrace]
  refine ⟨175605842670240493894691897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117070561780160329263127931 175605842670240493894691897)
  ·
    refine ⟨131704382002680370421018923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175605842670240493894691897 131704382002680370421018923)
    ·
      refine ⟨197556573004020555631528385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131704382002680370421018923 197556573004020555631528385)
      ·
        refine ⟨148167429753015416723646289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197556573004020555631528385 148167429753015416723646289)
        ·
          refine ⟨111125572314761562542734717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148167429753015416723646289 111125572314761562542734717)
          ·
            refine ⟨41672089618035585953525519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111125572314761562542734717 41672089618035585953525519)
            ·
              refine ⟨62508134427053378930288279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41672089618035585953525519 62508134427053378930288279)
              ·
                refine ⟨93762201640580068395432419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62508134427053378930288279 93762201640580068395432419)
                ·
                  refine ⟨140643302460870102593148629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93762201640580068395432419 140643302460870102593148629)
                  ·
                    refine ⟨3296327401426643029526921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 140643302460870102593148629 3296327401426643029526921)
                    ·
                      refine ⟨2472245551069982272145191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3296327401426643029526921 2472245551069982272145191)
                      ·
                        rfl

theorem cell23_4814681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 7, 2].length) (baseStart_4814681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814681 prefixEnd_4814681 := by exact prefixLift 4814681
  have htrace : WordTrace (prefixWord ++ tailWord_4814681) baseStart_4814681 baseEnd_4814681 := by
    simpa [prefixWord, tailWord_4814681, baseEnd_4814681] using wordTrace_append hprefix tailTrace_4814681
  have hstable : (prefixWord ++ tailWord_4814681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814681).length < 2 ^ (prefixWord ++ tailWord_4814681).sum := by decide
  have hdescent : baseEnd_4814681 < baseStart_4814681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814731 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 3]
def baseStart_4814731 : Nat := 118140960795 + 4814731 * 2 ^ 59
def prefixEnd_4814731 : Nat := 4983230072969 + 3 ^ 40 * 4814731 * 2
def baseEnd_4814731 : Nat := 2472271225102707076519961

theorem tailTrace_4814731 : CollatzResearch.WordTrace tailWord_4814731 prefixEnd_4814731 2472271225102707076519961 := by
  unfold tailWord_4814731
  simp only [CollatzResearch.WordTrace]
  refine ⟨175607666320059352434012047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117071777546706234956008031 175607666320059352434012047)
  ·
    refine ⟨263411499480089028651018071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175607666320059352434012047 263411499480089028651018071)
    ·
      refine ⟨395117249220133542976527107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263411499480089028651018071 395117249220133542976527107)
      ·
        refine ⟨592675873830200314464790661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395117249220133542976527107 592675873830200314464790661)
        ·
          refine ⟨111126726343162558962148249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 592675873830200314464790661 111126726343162558962148249)
          ·
            refine ⟨83345044757371919221611187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111126726343162558962148249 83345044757371919221611187)
            ·
              refine ⟨125017567136057878832416781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83345044757371919221611187 125017567136057878832416781)
              ·
                refine ⟨46881587676021704562156293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125017567136057878832416781 46881587676021704562156293)
                ·
                  refine ⟨8790297689254069605404305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46881587676021704562156293 8790297689254069605404305)
                  ·
                    refine ⟨6592723266940552204053229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8790297689254069605404305 6592723266940552204053229)
                    ·
                      refine ⟨2472271225102707076519961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6592723266940552204053229 2472271225102707076519961)
                      ·
                        rfl

theorem cell23_4814731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 3].length) (baseStart_4814731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814731 prefixEnd_4814731 := by exact prefixLift 4814731
  have htrace : WordTrace (prefixWord ++ tailWord_4814731) baseStart_4814731 baseEnd_4814731 := by
    simpa [prefixWord, tailWord_4814731, baseEnd_4814731] using wordTrace_append hprefix tailTrace_4814731
  have hstable : (prefixWord ++ tailWord_4814731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814731).length < 2 ^ (prefixWord ++ tailWord_4814731).sum := by decide
  have hdescent : baseEnd_4814731 < baseStart_4814731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814748 : List Nat := [2, 2, 3, 3, 1, 1, 1, 2, 1, 4, 3]
def baseStart_4814748 : Nat := 118140960795 + 4814748 * 2 ^ 59
def prefixEnd_4814748 : Nat := 4983230072969 + 3 ^ 40 * 4814748 * 2
def baseEnd_4814748 : Nat := 2472279954273833510007383

theorem tailTrace_4814748 : CollatzResearch.WordTrace tailWord_4814748 prefixEnd_4814748 2472279954273833510007383 := by
  unfold tailWord_4814748
  simp only [CollatzResearch.WordTrace]
  refine ⟨87804143180498882168690449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117072190907331842891587265 87804143180498882168690449)
  ·
    refine ⟨65853107385374161626517837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87804143180498882168690449 65853107385374161626517837)
    ·
      refine ⟨24694915269515310609944189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65853107385374161626517837 24694915269515310609944189)
      ·
        refine ⟨9260593226068241478729071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24694915269515310609944189 9260593226068241478729071)
        ·
          refine ⟨13890889839102362218093607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9260593226068241478729071 13890889839102362218093607)
          ·
            refine ⟨20836334758653543327140411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13890889839102362218093607 20836334758653543327140411)
            ·
              refine ⟨31254502137980314990710617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20836334758653543327140411 31254502137980314990710617)
              ·
                refine ⟨23440876603485236243032963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31254502137980314990710617 23440876603485236243032963)
                ·
                  refine ⟨35161314905227854364549445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23440876603485236243032963 35161314905227854364549445)
                  ·
                    refine ⟨6592746544730222693353021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35161314905227854364549445 6592746544730222693353021)
                    ·
                      refine ⟨2472279954273833510007383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6592746544730222693353021 2472279954273833510007383)
                      ·
                        rfl

theorem cell23_4814748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_4814748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814748 prefixEnd_4814748 := by exact prefixLift 4814748
  have htrace : WordTrace (prefixWord ++ tailWord_4814748) baseStart_4814748 baseEnd_4814748 := by
    simpa [prefixWord, tailWord_4814748, baseEnd_4814748] using wordTrace_append hprefix tailTrace_4814748
  have hstable : (prefixWord ++ tailWord_4814748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814748).length < 2 ^ (prefixWord ++ tailWord_4814748).sum := by decide
  have hdescent : baseEnd_4814748 < baseStart_4814748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814802 : List Nat := [3, 2, 2, 3, 2, 2, 2, 1, 6]
def baseStart_4814802 : Nat := 118140960795 + 4814802 * 2 ^ 59
def prefixEnd_4814802 : Nat := 4983230072969 + 3 ^ 40 * 4814802 * 2
def baseEnd_4814802 : Nat := 274700853581019588748015

theorem tailTrace_4814802 : CollatzResearch.WordTrace tailWord_4814802 prefixEnd_4814802 274700853581019588748015 := by
  unfold tailWord_4814802
  simp only [CollatzResearch.WordTrace]
  refine ⟨43902563975700532889961665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117073503935201421039897773 43902563975700532889961665)
  ·
    refine ⟨32926922981775399667471249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43902563975700532889961665 32926922981775399667471249)
    ·
      refine ⟨24695192236331549750603437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32926922981775399667471249 24695192236331549750603437)
      ·
        refine ⟨9260697088624331156476289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24695192236331549750603437 9260697088624331156476289)
        ·
          refine ⟨6945522816468248367357217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9260697088624331156476289 6945522816468248367357217)
          ·
            refine ⟨5209142112351186275517913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6945522816468248367357217 5209142112351186275517913)
            ·
              refine ⟨3906856584263389706638435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5209142112351186275517913 3906856584263389706638435)
              ·
                refine ⟨5860284876395084559957653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3906856584263389706638435 5860284876395084559957653)
                ·
                  refine ⟨274700853581019588748015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5860284876395084559957653 274700853581019588748015)
                  ·
                    rfl

theorem cell23_4814802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 6].length) (baseStart_4814802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814802 prefixEnd_4814802 := by exact prefixLift 4814802
  have htrace : WordTrace (prefixWord ++ tailWord_4814802) baseStart_4814802 baseEnd_4814802 := by
    simpa [prefixWord, tailWord_4814802, baseEnd_4814802] using wordTrace_append hprefix tailTrace_4814802
  have hstable : (prefixWord ++ tailWord_4814802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814802).length < 2 ^ (prefixWord ++ tailWord_4814802).sum := by decide
  have hdescent : baseEnd_4814802 < baseStart_4814802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814815 : List Nat := [1, 1, 2, 3, 4, 3, 1, 2, 1, 5]
def baseStart_4814815 : Nat := 118140960795 + 4814815 * 2 ^ 59
def prefixEnd_4814815 : Nat := 4983230072969 + 3 ^ 40 * 4814815 * 2
def baseEnd_4814815 : Nat := 824104785825894915956525

theorem tailTrace_4814815 : CollatzResearch.WordTrace tailWord_4814815 prefixEnd_4814815 824104785825894915956525 := by
  unfold tailWord_4814815
  simp only [CollatzResearch.WordTrace]
  refine ⟨175610730051755034780069899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117073820034503356520046599 175610730051755034780069899)
  ·
    refine ⟨263416095077632552170104849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175610730051755034780069899 263416095077632552170104849)
    ·
      refine ⟨197562071308224414127578637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263416095077632552170104849 197562071308224414127578637)
      ·
        refine ⟨74085776740584155297841989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197562071308224414127578637 74085776740584155297841989)
        ·
          refine ⟨13891083138859529118345373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74085776740584155297841989 13891083138859529118345373)
          ·
            refine ⟨5209156177072323419379515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13891083138859529118345373 5209156177072323419379515)
            ·
              refine ⟨7813734265608485129069273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5209156177072323419379515 7813734265608485129069273)
              ·
                refine ⟨5860300699206363846801955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7813734265608485129069273 5860300699206363846801955)
                ·
                  refine ⟨8790451048809545770202933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5860300699206363846801955 8790451048809545770202933)
                  ·
                    refine ⟨824104785825894915956525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8790451048809545770202933 824104785825894915956525)
                    ·
                      rfl

theorem cell23_4814815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 5].length) (baseStart_4814815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814815 prefixEnd_4814815 := by exact prefixLift 4814815
  have htrace : WordTrace (prefixWord ++ tailWord_4814815) baseStart_4814815 baseEnd_4814815 := by
    simpa [prefixWord, tailWord_4814815, baseEnd_4814815] using wordTrace_append hprefix tailTrace_4814815
  have hstable : (prefixWord ++ tailWord_4814815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814815).length < 2 ^ (prefixWord ++ tailWord_4814815).sum := by decide
  have hdescent : baseEnd_4814815 < baseStart_4814815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814846 : List Nat := [4, 2, 2, 2, 1, 1, 4, 2, 1, 1, 3]
def baseStart_4814846 : Nat := 118140960795 + 4814846 * 2 ^ 59
def prefixEnd_4814846 : Nat := 4983230072969 + 3 ^ 40 * 4814846 * 2
def baseEnd_4814846 : Nat := 2472330275377974126581933

theorem tailTrace_4814846 : CollatzResearch.WordTrace tailWord_4814846 prefixEnd_4814846 2472330275377974126581933 := by
  unfold tailWord_4814846
  simp only [CollatzResearch.WordTrace]
  refine ⟨21951482589330340884306049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117074573809761818049632261 21951482589330340884306049)
  ·
    refine ⟨16463611941997755663229537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21951482589330340884306049 16463611941997755663229537)
    ·
      refine ⟨12347708956498316747422153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16463611941997755663229537 12347708956498316747422153)
      ·
        refine ⟨9260781717373737560566615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12347708956498316747422153 9260781717373737560566615)
        ·
          refine ⟨13891172576060606340849923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9260781717373737560566615 13891172576060606340849923)
          ·
            refine ⟨20836758864090909511274885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13891172576060606340849923 20836758864090909511274885)
            ·
              refine ⟨3906892287017045533364041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20836758864090909511274885 3906892287017045533364041)
              ·
                refine ⟨2930169215262784150023031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3906892287017045533364041 2930169215262784150023031)
                ·
                  refine ⟨4395253822894176225034547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2930169215262784150023031 4395253822894176225034547)
                  ·
                    refine ⟨6592880734341264337551821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4395253822894176225034547 6592880734341264337551821)
                    ·
                      refine ⟨2472330275377974126581933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6592880734341264337551821 2472330275377974126581933)
                      ·
                        rfl

theorem cell23_4814846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_4814846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814846 prefixEnd_4814846 := by exact prefixLift 4814846
  have htrace : WordTrace (prefixWord ++ tailWord_4814846) baseStart_4814846 baseEnd_4814846 := by
    simpa [prefixWord, tailWord_4814846, baseEnd_4814846] using wordTrace_append hprefix tailTrace_4814846
  have hstable : (prefixWord ++ tailWord_4814846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814846).length < 2 ^ (prefixWord ++ tailWord_4814846).sum := by decide
  have hdescent : baseEnd_4814846 < baseStart_4814846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814891 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 4]
def baseStart_4814891 : Nat := 118140960795 + 4814891 * 2 ^ 59
def prefixEnd_4814891 : Nat := 4983230072969 + 3 ^ 40 * 4814891 * 2
def baseEnd_4814891 : Nat := 2472353382007426450519225

theorem tailTrace_4814891 : CollatzResearch.WordTrace tailWord_4814891 prefixEnd_4814891 2472353382007426450519225 := by
  unfold tailWord_4814891
  simp only [CollatzResearch.WordTrace]
  refine ⟨175613501999479699759836527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117075667999653133173224351 175613501999479699759836527)
  ·
    refine ⟨263420252999219549639754791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175613501999479699759836527 263420252999219549639754791)
    ·
      refine ⟨395130379498829324459632187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263420252999219549639754791 395130379498829324459632187)
      ·
        refine ⟨592695569248243986689448281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395130379498829324459632187 592695569248243986689448281)
        ·
          refine ⟨444521676936182990017086211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 592695569248243986689448281 444521676936182990017086211)
          ·
            refine ⟨666782515404274485025629317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444521676936182990017086211 666782515404274485025629317)
            ·
              refine ⟨125021721638301465942305497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 666782515404274485025629317 125021721638301465942305497)
              ·
                refine ⟨93766291228726099456729123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125021721638301465942305497 93766291228726099456729123)
                ·
                  refine ⟨140649436843089149185093685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93766291228726099456729123 140649436843089149185093685)
                  ·
                    refine ⟨13185884704039607736102533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 140649436843089149185093685 13185884704039607736102533)
                    ·
                      refine ⟨2472353382007426450519225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13185884704039607736102533 2472353382007426450519225)
                      ·
                        rfl

theorem cell23_4814891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 4].length) (baseStart_4814891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814891 prefixEnd_4814891 := by exact prefixLift 4814891
  have htrace : WordTrace (prefixWord ++ tailWord_4814891) baseStart_4814891 baseEnd_4814891 := by
    simpa [prefixWord, tailWord_4814891, baseEnd_4814891] using wordTrace_append hprefix tailTrace_4814891
  have hstable : (prefixWord ++ tailWord_4814891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814891).length < 2 ^ (prefixWord ++ tailWord_4814891).sum := by decide
  have hdescent : baseEnd_4814891 < baseStart_4814891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814902 : List Nat := [5, 1, 2, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_4814902 : Nat := 118140960795 + 4814902 * 2 ^ 59
def prefixEnd_4814902 : Nat := 4983230072969 + 3 ^ 40 * 4814902 * 2
def baseEnd_4814902 : Nat := 2472359030294625907481675

theorem tailTrace_4814902 : CollatzResearch.WordTrace tailWord_4814902 prefixEnd_4814902 2472359030294625907481675 := by
  unfold tailWord_4814902
  simp only [CollatzResearch.WordTrace]
  refine ⟨10975868950152490539905435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117075935468293232425657973 10975868950152490539905435)
  ·
    refine ⟨16463803425228735809858153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10975868950152490539905435 16463803425228735809858153)
    ·
      refine ⟨12347852568921551857393615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16463803425228735809858153 12347852568921551857393615)
      ·
        refine ⟨18521778853382327786090423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12347852568921551857393615 18521778853382327786090423)
        ·
          refine ⟨27782668280073491679135635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18521778853382327786090423 27782668280073491679135635)
          ·
            refine ⟨41674002420110237518703453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27782668280073491679135635 41674002420110237518703453)
            ·
              refine ⟨15627750907541339069513795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41674002420110237518703453 15627750907541339069513795)
              ·
                refine ⟨23441626361312008604270693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15627750907541339069513795 23441626361312008604270693)
                ·
                  refine ⟨4395304942746001613300755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23441626361312008604270693 4395304942746001613300755)
                  ·
                    refine ⟨6592957414119002419951133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4395304942746001613300755 6592957414119002419951133)
                    ·
                      refine ⟨2472359030294625907481675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6592957414119002419951133 2472359030294625907481675)
                      ·
                        rfl

theorem cell23_4814902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_4814902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814902 prefixEnd_4814902 := by exact prefixLift 4814902
  have htrace : WordTrace (prefixWord ++ tailWord_4814902) baseStart_4814902 baseEnd_4814902 := by
    simpa [prefixWord, tailWord_4814902, baseEnd_4814902] using wordTrace_append hprefix tailTrace_4814902
  have hstable : (prefixWord ++ tailWord_4814902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814902).length < 2 ^ (prefixWord ++ tailWord_4814902).sum := by decide
  have hdescent : baseEnd_4814902 < baseStart_4814902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4814958 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_4814958 : Nat := 118140960795 + 4814958 * 2 ^ 59
def prefixEnd_4814958 : Nat := 4983230072969 + 3 ^ 40 * 4814958 * 2
def baseEnd_4814958 : Nat := 2472387785211277688381417

theorem tailTrace_4814958 : CollatzResearch.WordTrace tailWord_4814958 prefixEnd_4814958 2472387785211277688381417 := by
  unfold tailWord_4814958
  simp only [CollatzResearch.WordTrace]
  refine ⟨21951993211279621275315691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117077297126824646801683685 21951993211279621275315691)
  ·
    refine ⟨32927989816919431912973537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21951993211279621275315691 32927989816919431912973537)
    ·
      refine ⟨24695992362689573934730153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32927989816919431912973537 24695992362689573934730153)
      ·
        refine ⟨18521994272017180451047615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24695992362689573934730153 18521994272017180451047615)
        ·
          refine ⟨27782991408025770676571423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18521994272017180451047615 27782991408025770676571423)
          ·
            refine ⟨41674487112038656014857135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27782991408025770676571423 41674487112038656014857135)
            ·
              refine ⟨62511730668057984022285703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41674487112038656014857135 62511730668057984022285703)
              ·
                refine ⟨93767596002086976033428555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62511730668057984022285703 93767596002086976033428555)
                ·
                  refine ⟨140651394003130464050142833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93767596002086976033428555 140651394003130464050142833)
                  ·
                    refine ⟨105488545502347848037607125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 140651394003130464050142833 105488545502347848037607125)
                    ·
                      refine ⟨2472387785211277688381417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 105488545502347848037607125 2472387785211277688381417)
                      ·
                        rfl

theorem cell23_4814958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_4814958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4814958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4814958 prefixEnd_4814958 := by exact prefixLift 4814958
  have htrace : WordTrace (prefixWord ++ tailWord_4814958) baseStart_4814958 baseEnd_4814958 := by
    simpa [prefixWord, tailWord_4814958, baseEnd_4814958] using wordTrace_append hprefix tailTrace_4814958
  have hstable : (prefixWord ++ tailWord_4814958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4814958).length < 2 ^ (prefixWord ++ tailWord_4814958).sum := by decide
  have hdescent : baseEnd_4814958 < baseStart_4814958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4814958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815062 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_4815062 : Nat := 118140960795 + 4815062 * 2 ^ 59
def prefixEnd_4815062 : Nat := 4983230072969 + 3 ^ 40 * 4815062 * 2
def baseEnd_4815062 : Nat := 2472441187199345281480939

theorem tailTrace_4815062 : CollatzResearch.WordTrace tailWord_4815062 prefixEnd_4815062 2472441187199345281480939 := by
  unfold tailWord_4815062
  simp only [CollatzResearch.WordTrace]
  refine ⟨10976233680116262247769465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117079825921240130642874293 10976233680116262247769465)
  ·
    refine ⟨8232175260087196685827099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10976233680116262247769465 8232175260087196685827099)
    ·
      refine ⟨12348262890130795028740649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8232175260087196685827099 12348262890130795028740649)
      ·
        refine ⟨9261197167598096271555487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12348262890130795028740649 9261197167598096271555487)
        ·
          refine ⟨13891795751397144407333231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9261197167598096271555487 13891795751397144407333231)
          ·
            refine ⟨20837693627095716610999847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13891795751397144407333231 20837693627095716610999847)
            ·
              refine ⟨31256540440643574916499771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20837693627095716610999847 31256540440643574916499771)
              ·
                refine ⟨46884810660965362374749657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31256540440643574916499771 46884810660965362374749657)
                ·
                  refine ⟨35163607995724021781062243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46884810660965362374749657 35163607995724021781062243)
                  ·
                    refine ⟨52745411993586032671593365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35163607995724021781062243 52745411993586032671593365)
                    ·
                      refine ⟨2472441187199345281480939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52745411993586032671593365 2472441187199345281480939)
                      ·
                        rfl

theorem cell23_4815062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_4815062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815062 prefixEnd_4815062 := by exact prefixLift 4815062
  have htrace : WordTrace (prefixWord ++ tailWord_4815062) baseStart_4815062 baseEnd_4815062 := by
    simpa [prefixWord, tailWord_4815062, baseEnd_4815062] using wordTrace_append hprefix tailTrace_4815062
  have hstable : (prefixWord ++ tailWord_4815062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815062).length < 2 ^ (prefixWord ++ tailWord_4815062).sum := by decide
  have hdescent : baseEnd_4815062 < baseStart_4815062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815115 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 6, 4]
def baseStart_4815115 : Nat := 118140960795 + 4815115 * 2 ^ 59
def prefixEnd_4815115 : Nat := 4983230072969 + 3 ^ 40 * 4815115 * 2
def baseEnd_4815115 : Nat := 824156133891344524706065

theorem tailTrace_4815115 : CollatzResearch.WordTrace tailWord_4815115 prefixEnd_4815115 824156133891344524706065 := by
  unfold tailWord_4815115
  simp only [CollatzResearch.WordTrace]
  refine ⟨175621671950668186015990799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117081114633778790677327199 175621671950668186015990799)
  ·
    refine ⟨263432507926002279023986199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175621671950668186015990799 263432507926002279023986199)
    ·
      refine ⟨395148761889003418535979299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263432507926002279023986199 395148761889003418535979299)
      ·
        refine ⟨592723142833505127803968949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395148761889003418535979299 592723142833505127803968949)
        ·
          refine ⟨55567794640641105731622089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 592723142833505127803968949 55567794640641105731622089)
          ·
            refine ⟨41675845980480829298716567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55567794640641105731622089 41675845980480829298716567)
            ·
              refine ⟨62513768970721243948074851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41675845980480829298716567 62513768970721243948074851)
              ·
                refine ⟨93770653456081865922112277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62513768970721243948074851 93770653456081865922112277)
                ·
                  refine ⟨4395499380753837465099013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 93770653456081865922112277 4395499380753837465099013)
                  ·
                    refine ⟨824156133891344524706065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4395499380753837465099013 824156133891344524706065)
                    ·
                      rfl

theorem cell23_4815115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 4].length) (baseStart_4815115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815115 prefixEnd_4815115 := by exact prefixLift 4815115
  have htrace : WordTrace (prefixWord ++ tailWord_4815115) baseStart_4815115 baseEnd_4815115 := by
    simpa [prefixWord, tailWord_4815115, baseEnd_4815115] using wordTrace_append hprefix tailTrace_4815115
  have hstable : (prefixWord ++ tailWord_4815115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815115).length < 2 ^ (prefixWord ++ tailWord_4815115).sum := by decide
  have hdescent : baseEnd_4815115 < baseStart_4815115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815125 : List Nat := [1, 3, 2, 1, 2, 1, 3, 3, 1, 1, 5]
def baseStart_4815125 : Nat := 118140960795 + 4815125 * 2 ^ 59
def prefixEnd_4815125 : Nat := 4983230072969 + 3 ^ 40 * 4815125 * 2
def baseEnd_4815125 : Nat := 2472473536480578534993149

theorem tailTrace_4815125 : CollatzResearch.WordTrace tailWord_4815125 prefixEnd_4815125 2472473536480578534993149 := by
  unfold tailWord_4815125
  simp only [CollatzResearch.WordTrace]
  refine ⟨175622036680631957723854829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117081357787087971815903219 175622036680631957723854829)
  ·
    refine ⟨65858263755236984146445561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175622036680631957723854829 65858263755236984146445561)
    ·
      refine ⟨49393697816427738109834171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65858263755236984146445561 49393697816427738109834171)
      ·
        refine ⟨74090546724641607164751257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49393697816427738109834171 74090546724641607164751257)
        ·
          refine ⟨55567910043481205373563443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74090546724641607164751257 55567910043481205373563443)
          ·
            refine ⟨83351865065221808060345165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55567910043481205373563443 83351865065221808060345165)
            ·
              refine ⟨31256949399458178022629437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83351865065221808060345165 31256949399458178022629437)
              ·
                refine ⟨11721356024796816758486039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31256949399458178022629437 11721356024796816758486039)
                ·
                  refine ⟨17582034037195225137729059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11721356024796816758486039 17582034037195225137729059)
                  ·
                    refine ⟨26373051055792837706593589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17582034037195225137729059 26373051055792837706593589)
                    ·
                      refine ⟨2472473536480578534993149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26373051055792837706593589 2472473536480578534993149)
                      ·
                        rfl

theorem cell23_4815125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_4815125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815125 prefixEnd_4815125 := by exact prefixLift 4815125
  have htrace : WordTrace (prefixWord ++ tailWord_4815125) baseStart_4815125 baseEnd_4815125 := by
    simpa [prefixWord, tailWord_4815125, baseEnd_4815125] using wordTrace_append hprefix tailTrace_4815125
  have hstable : (prefixWord ++ tailWord_4815125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815125).length < 2 ^ (prefixWord ++ tailWord_4815125).sum := by decide
  have hdescent : baseEnd_4815125 < baseStart_4815125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815132 : List Nat := [2, 2, 3, 1, 1, 1, 1, 6, 2, 4]
def baseStart_4815132 : Nat := 118140960795 + 4815132 * 2 ^ 59
def prefixEnd_4815132 : Nat := 4983230072969 + 3 ^ 40 * 4815132 * 2
def baseEnd_4815132 : Nat := 824159043615053335868539

theorem tailTrace_4815132 : CollatzResearch.WordTrace tailWord_4815132 prefixEnd_4815132 824159043615053335868539 := by
  unfold tailWord_4815132
  simp only [CollatzResearch.WordTrace]
  refine ⟨87811145995803298959679825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117081527994404398612906433 87811145995803298959679825)
  ·
    refine ⟨65858359496852474219759869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87811145995803298959679825 65858359496852474219759869)
    ·
      refine ⟨24696884811319677832409951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65858359496852474219759869 24696884811319677832409951)
      ·
        refine ⟨37045327216979516748614927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24696884811319677832409951 37045327216979516748614927)
        ·
          refine ⟨55567990825469275122922391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37045327216979516748614927 55567990825469275122922391)
          ·
            refine ⟨83351986238203912684383587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55567990825469275122922391 83351986238203912684383587)
            ·
              refine ⟨125027979357305869026575381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83351986238203912684383587 125027979357305869026575381)
              ·
                refine ⟨5860686532373712610620721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 125027979357305869026575381 5860686532373712610620721)
                ·
                  refine ⟨4395514899280284457965541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5860686532373712610620721 4395514899280284457965541)
                  ·
                    refine ⟨824159043615053335868539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4395514899280284457965541 824159043615053335868539)
                    ·
                      rfl

theorem cell23_4815132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_4815132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815132 prefixEnd_4815132 := by exact prefixLift 4815132
  have htrace : WordTrace (prefixWord ++ tailWord_4815132) baseStart_4815132 baseEnd_4815132 := by
    simpa [prefixWord, tailWord_4815132, baseEnd_4815132] using wordTrace_append hprefix tailTrace_4815132
  have hstable : (prefixWord ++ tailWord_4815132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815132).length < 2 ^ (prefixWord ++ tailWord_4815132).sum := by decide
  have hdescent : baseEnd_4815132 < baseStart_4815132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815133 : List Nat := [1, 4, 2, 3, 3, 1, 1, 1, 3, 1, 3]
def baseStart_4815133 : Nat := 118140960795 + 4815133 * 2 ^ 59
def prefixEnd_4815133 : Nat := 4983230072969 + 3 ^ 40 * 4815133 * 2
def baseEnd_4815133 : Nat := 2472477644325814503693113

theorem tailTrace_4815133 : CollatzResearch.WordTrace tailWord_4815133 prefixEnd_4815133 2472477644325814503693113 := by
  unfold tailWord_4815133
  simp only [CollatzResearch.WordTrace]
  refine ⟨175622328464602975090146053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117081552309735316726764035 175622328464602975090146053)
  ·
    refine ⟨32929186587113057829402385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175622328464602975090146053 32929186587113057829402385)
    ·
      refine ⟨24696889940334793372051789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32929186587113057829402385 24696889940334793372051789)
      ·
        refine ⟨9261333727625547514519421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24696889940334793372051789 9261333727625547514519421)
        ·
          refine ⟨3473000147859580317944783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9261333727625547514519421 3473000147859580317944783)
          ·
            refine ⟨5209500221789370476917175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3473000147859580317944783 5209500221789370476917175)
            ·
              refine ⟨7814250332684055715375763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5209500221789370476917175 7814250332684055715375763)
              ·
                refine ⟨11721375499026083573063645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7814250332684055715375763 11721375499026083573063645)
                ·
                  refine ⟨4395515812134781339898867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11721375499026083573063645 4395515812134781339898867)
                  ·
                    refine ⟨6593273718202172009848301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4395515812134781339898867 6593273718202172009848301)
                    ·
                      refine ⟨2472477644325814503693113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6593273718202172009848301 2472477644325814503693113)
                      ·
                        rfl

theorem cell23_4815133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_4815133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815133 prefixEnd_4815133 := by exact prefixLift 4815133
  have htrace : WordTrace (prefixWord ++ tailWord_4815133) baseStart_4815133 baseEnd_4815133 := by
    simpa [prefixWord, tailWord_4815133, baseEnd_4815133] using wordTrace_append hprefix tailTrace_4815133
  have hstable : (prefixWord ++ tailWord_4815133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815133).length < 2 ^ (prefixWord ++ tailWord_4815133).sum := by decide
  have hdescent : baseEnd_4815133 < baseStart_4815133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815135 : List Nat := [1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 6]
def baseStart_4815135 : Nat := 118140960795 + 4815135 * 2 ^ 59
def prefixEnd_4815135 : Nat := 4983230072969 + 3 ^ 40 * 4815135 * 2
def baseEnd_4815135 : Nat := 2472478671287123495868103

theorem tailTrace_4815135 : CollatzResearch.WordTrace tailWord_4815135 prefixEnd_4815135 2472478671287123495868103 := by
  unfold tailWord_4815135
  simp only [CollatzResearch.WordTrace]
  refine ⟨175622401410595729431718859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117081600940397152954479239 175622401410595729431718859)
  ·
    refine ⟨263433602115893594147578289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175622401410595729431718859 263433602115893594147578289)
    ·
      refine ⟨197575201586920195610683717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263433602115893594147578289 197575201586920195610683717)
      ·
        refine ⟨37045350297547536677003197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197575201586920195610683717 37045350297547536677003197)
        ·
          refine ⟨13892006361580326253876199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37045350297547536677003197 13892006361580326253876199)
          ·
            refine ⟨20838009542370489380814299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13892006361580326253876199 20838009542370489380814299)
            ·
              refine ⟨31257014313555734071221449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20838009542370489380814299 31257014313555734071221449)
              ·
                refine ⟨23442760735166800553416087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31257014313555734071221449 23442760735166800553416087)
                ·
                  refine ⟨35164141102750200830124131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23442760735166800553416087 35164141102750200830124131)
                  ·
                    refine ⟨52746211654125301245186197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35164141102750200830124131 52746211654125301245186197)
                    ·
                      refine ⟨2472478671287123495868103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52746211654125301245186197 2472478671287123495868103)
                      ·
                        rfl

theorem cell23_4815135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_4815135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815135 prefixEnd_4815135 := by exact prefixLift 4815135
  have htrace : WordTrace (prefixWord ++ tailWord_4815135) baseStart_4815135 baseEnd_4815135 := by
    simpa [prefixWord, tailWord_4815135, baseEnd_4815135] using wordTrace_append hprefix tailTrace_4815135
  have hstable : (prefixWord ++ tailWord_4815135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815135).length < 2 ^ (prefixWord ++ tailWord_4815135).sum := by decide
  have hdescent : baseEnd_4815135 < baseStart_4815135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815156 : List Nat := [2, 5, 1, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_4815156 : Nat := 118140960795 + 4815156 * 2 ^ 59
def prefixEnd_4815156 : Nat := 4983230072969 + 3 ^ 40 * 4815156 * 2
def baseEnd_4815156 : Nat := 2472489454380867913705507

theorem tailTrace_4815156 : CollatzResearch.WordTrace tailWord_4815156 prefixEnd_4815156 2472489454380867913705507 := by
  unfold tailWord_4815156
  simp only [CollatzResearch.WordTrace]
  refine ⟨87811583671759825009116661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117082111562346433345488881 87811583671759825009116661)
  ·
    refine ⟨8232335969227483594604687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87811583671759825009116661 8232335969227483594604687)
    ·
      refine ⟨12348503953841225391907031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8232335969227483594604687 12348503953841225391907031)
      ·
        refine ⟨18522755930761838087860547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12348503953841225391907031 18522755930761838087860547)
        ·
          refine ⟨27784133896142757131790821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18522755930761838087860547 27784133896142757131790821)
          ·
            refine ⟨5209525105526766962210779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27784133896142757131790821 5209525105526766962210779)
            ·
              refine ⟨7814287658290150443316169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5209525105526766962210779 7814287658290150443316169)
              ·
                refine ⟨5860715743717612832487127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7814287658290150443316169 5860715743717612832487127)
                ·
                  refine ⟨8791073615576419248730691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5860715743717612832487127 8791073615576419248730691)
                  ·
                    refine ⟨13186610423364628873096037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8791073615576419248730691 13186610423364628873096037)
                    ·
                      refine ⟨2472489454380867913705507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13186610423364628873096037 2472489454380867913705507)
                      ·
                        rfl

theorem cell23_4815156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_4815156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815156 prefixEnd_4815156 := by exact prefixLift 4815156
  have htrace : WordTrace (prefixWord ++ tailWord_4815156) baseStart_4815156 baseEnd_4815156 := by
    simpa [prefixWord, tailWord_4815156, baseEnd_4815156] using wordTrace_append hprefix tailTrace_4815156
  have hstable : (prefixWord ++ tailWord_4815156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815156).length < 2 ^ (prefixWord ++ tailWord_4815156).sum := by decide
  have hdescent : baseEnd_4815156 < baseStart_4815156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815169 : List Nat := [1, 2, 5, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_4815169 : Nat := 118140960795 + 4815169 * 2 ^ 59
def prefixEnd_4815169 : Nat := 4983230072969 + 3 ^ 40 * 4815169 * 2
def baseEnd_4815169 : Nat := 2472496129629376362842947

theorem tailTrace_4815169 : CollatzResearch.WordTrace tailWord_4815169 prefixEnd_4815169 2472496129629376362842947 := by
  unfold tailWord_4815169
  simp only [CollatzResearch.WordTrace]
  refine ⟨175623641492472553238456561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117082427661648368825637707 175623641492472553238456561)
  ·
    refine ⟨131717731119354414928842421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175623641492472553238456561 131717731119354414928842421)
    ·
      refine ⟨12348537292439476399578977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131717731119354414928842421 12348537292439476399578977)
      ·
        refine ⟨9261402969329607299684233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12348537292439476399578977 9261402969329607299684233)
        ·
          refine ⟨6946052226997205474763175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9261402969329607299684233 6946052226997205474763175)
          ·
            refine ⟨10419078340495808212144763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6946052226997205474763175 10419078340495808212144763)
            ·
              refine ⟨15628617510743712318217145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10419078340495808212144763 15628617510743712318217145)
              ·
                refine ⟨11721463133057784238662859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15628617510743712318217145 11721463133057784238662859)
                ·
                  refine ⟨17582194699586676357994289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11721463133057784238662859 17582194699586676357994289)
                  ·
                    refine ⟨13186646024690007268495717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17582194699586676357994289 13186646024690007268495717)
                    ·
                      refine ⟨2472496129629376362842947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13186646024690007268495717 2472496129629376362842947)
                      ·
                        rfl

theorem cell23_4815169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_4815169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815169 prefixEnd_4815169 := by exact prefixLift 4815169
  have htrace : WordTrace (prefixWord ++ tailWord_4815169) baseStart_4815169 baseEnd_4815169 := by
    simpa [prefixWord, tailWord_4815169, baseEnd_4815169] using wordTrace_append hprefix tailTrace_4815169
  have hstable : (prefixWord ++ tailWord_4815169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815169).length < 2 ^ (prefixWord ++ tailWord_4815169).sum := by decide
  have hdescent : baseEnd_4815169 < baseStart_4815169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815196 : List Nat := [2, 2, 4, 3, 2, 1, 1, 8]
def baseStart_4815196 : Nat := 118140960795 + 4815196 * 2 ^ 59
def prefixEnd_4815196 : Nat := 4983230072969 + 3 ^ 40 * 4815196 * 2
def baseEnd_4815196 : Nat := 91574444207668435452049

theorem tailTrace_4815196 : CollatzResearch.WordTrace tailWord_4815196 prefixEnd_4815196 91574444207668435452049 := by
  unfold tailWord_4815196
  simp only [CollatzResearch.WordTrace]
  refine ⟨87812313131687368424844721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117083084175583157899792961 87812313131687368424844721)
  ·
    refine ⟨65859234848765526318633541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87812313131687368424844721 65859234848765526318633541)
    ·
      refine ⟨12348606534143536184743789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65859234848765526318633541 12348606534143536184743789)
      ·
        refine ⟨4630727450303826069278921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12348606534143536184743789 4630727450303826069278921)
        ·
          refine ⟨3473045587727869551959191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4630727450303826069278921 3473045587727869551959191)
          ·
            refine ⟨5209568381591804327938787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3473045587727869551959191 5209568381591804327938787)
            ·
              refine ⟨7814352572387706491908181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5209568381591804327938787 7814352572387706491908181)
              ·
                refine ⟨91574444207668435452049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7814352572387706491908181 91574444207668435452049)
                ·
                  rfl

theorem cell23_4815196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 8].length) (baseStart_4815196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815196 prefixEnd_4815196 := by exact prefixLift 4815196
  have htrace : WordTrace (prefixWord ++ tailWord_4815196) baseStart_4815196 baseEnd_4815196 := by
    simpa [prefixWord, tailWord_4815196, baseEnd_4815196] using wordTrace_append hprefix tailTrace_4815196
  have hstable : (prefixWord ++ tailWord_4815196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815196).length < 2 ^ (prefixWord ++ tailWord_4815196).sum := by decide
  have hdescent : baseEnd_4815196 < baseStart_4815196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815205 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 1, 8]
def baseStart_4815205 : Nat := 118140960795 + 4815205 * 2 ^ 59
def prefixEnd_4815205 : Nat := 4983230072969 + 3 ^ 40 * 4815205 * 2
def baseEnd_4815205 : Nat := 824171538310979407330927

theorem tailTrace_4815205 : CollatzResearch.WordTrace tailWord_4815205 prefixEnd_4815205 824171538310979407330927 := by
  unfold tailWord_4815205
  simp only [CollatzResearch.WordTrace]
  refine ⟨175624954520342131386767069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117083303013561420924511379 175624954520342131386767069)
  ·
    refine ⟨65859357945128299270037651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175624954520342131386767069 65859357945128299270037651)
    ·
      refine ⟨98789036917692448905056477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65859357945128299270037651 98789036917692448905056477)
      ·
        refine ⟨37045888844134668339396179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98789036917692448905056477 37045888844134668339396179)
        ·
          refine ⟨55568833266202002509094269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37045888844134668339396179 55568833266202002509094269)
          ·
            refine ⟨20838312474825750940910351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55568833266202002509094269 20838312474825750940910351)
            ·
              refine ⟨31257468712238626411365527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20838312474825750940910351 31257468712238626411365527)
              ·
                refine ⟨46886203068357939617048291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31257468712238626411365527 46886203068357939617048291)
                ·
                  refine ⟨70329304602536909425572437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46886203068357939617048291 70329304602536909425572437)
                  ·
                    refine ⟨824171538310979407330927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70329304602536909425572437 824171538310979407330927)
                    ·
                      rfl

theorem cell23_4815205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_4815205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815205 prefixEnd_4815205 := by exact prefixLift 4815205
  have htrace : WordTrace (prefixWord ++ tailWord_4815205) baseStart_4815205 baseEnd_4815205 := by
    simpa [prefixWord, tailWord_4815205, baseEnd_4815205] using wordTrace_append hprefix tailTrace_4815205
  have hstable : (prefixWord ++ tailWord_4815205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815205).length < 2 ^ (prefixWord ++ tailWord_4815205).sum := by decide
  have hdescent : baseEnd_4815205 < baseStart_4815205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815215 : List Nat := [1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 5]
def baseStart_4815215 : Nat := 118140960795 + 4815215 * 2 ^ 59
def prefixEnd_4815215 : Nat := 4983230072969 + 3 ^ 40 * 4815215 * 2
def baseEnd_4815215 : Nat := 2472519749739483182867735

theorem tailTrace_4815215 : CollatzResearch.WordTrace tailWord_4815215 prefixEnd_4815215 2472519749739483182867735 := by
  unfold tailWord_4815215
  simp only [CollatzResearch.WordTrace]
  refine ⟨175625319250305903094631099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117083546166870602063087399 175625319250305903094631099)
  ·
    refine ⟨263437978875458854641946649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175625319250305903094631099 263437978875458854641946649)
    ·
      refine ⟨197578484156594140981459987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263437978875458854641946649 197578484156594140981459987)
      ·
        refine ⟨296367726234891211472189981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197578484156594140981459987 296367726234891211472189981)
        ·
          refine ⟨111137897338084204302071243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 296367726234891211472189981 111137897338084204302071243)
          ·
            refine ⟨166706846007126306453106865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111137897338084204302071243 166706846007126306453106865)
            ·
              refine ⟨125030134505344729839830149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166706846007126306453106865 125030134505344729839830149)
              ·
                refine ⟨23443150219752136844968153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125030134505344729839830149 23443150219752136844968153)
                ·
                  refine ⟨17582362664814102633726115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23443150219752136844968153 17582362664814102633726115)
                  ·
                    refine ⟨26373543997221153950589173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17582362664814102633726115 26373543997221153950589173)
                    ·
                      refine ⟨2472519749739483182867735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26373543997221153950589173 2472519749739483182867735)
                      ·
                        rfl

theorem cell23_4815215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 5].length) (baseStart_4815215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815215 prefixEnd_4815215 := by exact prefixLift 4815215
  have htrace : WordTrace (prefixWord ++ tailWord_4815215) baseStart_4815215 baseEnd_4815215 := by
    simpa [prefixWord, tailWord_4815215, baseEnd_4815215] using wordTrace_append hprefix tailTrace_4815215
  have hstable : (prefixWord ++ tailWord_4815215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815215).length < 2 ^ (prefixWord ++ tailWord_4815215).sum := by decide
  have hdescent : baseEnd_4815215 < baseStart_4815215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815225 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 3, 4, 4]
def baseStart_4815225 : Nat := 118140960795 + 4815225 * 2 ^ 59
def prefixEnd_4815225 : Nat := 4983230072969 + 3 ^ 40 * 4815225 * 2
def baseEnd_4815225 : Nat := 2472524884546028143742689

theorem tailTrace_4815225 : CollatzResearch.WordTrace tailWord_4815225 prefixEnd_4815225 2472524884546028143742689 := by
  unfold tailWord_4815225
  simp only [CollatzResearch.WordTrace]
  refine ⟨175625683980269674802495129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117083789320179783201663419 175625683980269674802495129)
  ·
    refine ⟨131719262985202256101871347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175625683980269674802495129 131719262985202256101871347)
    ·
      refine ⟨197578894477803384152807021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131719262985202256101871347 197578894477803384152807021)
      ·
        refine ⟨74092085429176269057302633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197578894477803384152807021 74092085429176269057302633)
        ·
          refine ⟨55569064071882201792976975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74092085429176269057302633 55569064071882201792976975)
          ·
            refine ⟨83353596107823302689465463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55569064071882201792976975 83353596107823302689465463)
            ·
              refine ⟨125030394161734954034198195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83353596107823302689465463 125030394161734954034198195)
              ·
                refine ⟨187545591242602431051297293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125030394161734954034198195 187545591242602431051297293)
                ·
                  refine ⟨70329596715975911644236485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 187545591242602431051297293 70329596715975911644236485)
                  ·
                    refine ⟨13186799384245483433294341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70329596715975911644236485 13186799384245483433294341)
                    ·
                      refine ⟨2472524884546028143742689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13186799384245483433294341 2472524884546028143742689)
                      ·
                        rfl

theorem cell23_4815225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_4815225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815225 prefixEnd_4815225 := by exact prefixLift 4815225
  have htrace : WordTrace (prefixWord ++ tailWord_4815225) baseStart_4815225 baseEnd_4815225 := by
    simpa [prefixWord, tailWord_4815225, baseEnd_4815225] using wordTrace_append hprefix tailTrace_4815225
  have hstable : (prefixWord ++ tailWord_4815225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815225).length < 2 ^ (prefixWord ++ tailWord_4815225).sum := by decide
  have hdescent : baseEnd_4815225 < baseStart_4815225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815229 : List Nat := [1, 4, 1, 1, 2, 3, 2, 2, 1, 4, 2]
def baseStart_4815229 : Nat := 118140960795 + 4815229 * 2 ^ 59
def prefixEnd_4815229 : Nat := 4983230072969 + 3 ^ 40 * 4815229 * 2
def baseEnd_4815229 : Nat := 2472526938468646128092671

theorem tailTrace_4815229 : CollatzResearch.WordTrace tailWord_4815229 prefixEnd_4815229 2472526938468646128092671 := by
  unfold tailWord_4815229
  simp only [CollatzResearch.WordTrace]
  refine ⟨175625829872255183485640741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117083886581503455657093827 175625829872255183485640741)
  ·
    refine ⟨32929843101047846903557639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175625829872255183485640741 32929843101047846903557639)
    ·
      refine ⟨49394764651571770355336459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32929843101047846903557639 49394764651571770355336459)
      ·
        refine ⟨74092146977357655533004689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49394764651571770355336459 74092146977357655533004689)
        ·
          refine ⟨55569110233018241649753517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74092146977357655533004689 55569110233018241649753517)
          ·
            refine ⟨20838416337381840618657569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55569110233018241649753517 20838416337381840618657569)
            ·
              refine ⟨15628812253036380463993177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20838416337381840618657569 15628812253036380463993177)
              ·
                refine ⟨11721609189777285347994883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15628812253036380463993177 11721609189777285347994883)
                ·
                  refine ⟨17582413784665928021992325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11721609189777285347994883 17582413784665928021992325)
                  ·
                    refine ⟨3296702584624861504123561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17582413784665928021992325 3296702584624861504123561)
                    ·
                      refine ⟨2472526938468646128092671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3296702584624861504123561 2472526938468646128092671)
                      ·
                        rfl

theorem cell23_4815229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 4, 2].length) (baseStart_4815229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815229 prefixEnd_4815229 := by exact prefixLift 4815229
  have htrace : WordTrace (prefixWord ++ tailWord_4815229) baseStart_4815229 baseEnd_4815229 := by
    simpa [prefixWord, tailWord_4815229, baseEnd_4815229] using wordTrace_append hprefix tailTrace_4815229
  have hstable : (prefixWord ++ tailWord_4815229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815229).length < 2 ^ (prefixWord ++ tailWord_4815229).sum := by decide
  have hdescent : baseEnd_4815229 < baseStart_4815229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815233 : List Nat := [1, 2, 4, 3, 1, 1, 4, 1, 1, 3, 2]
def baseStart_4815233 : Nat := 118140960795 + 4815233 * 2 ^ 59
def prefixEnd_4815233 : Nat := 4983230072969 + 3 ^ 40 * 4815233 * 2
def baseEnd_4815233 : Nat := 2472528992391264112442653

theorem tailTrace_4815233 : CollatzResearch.WordTrace tailWord_4815233 prefixEnd_4815233 2472528992391264112442653 := by
  unfold tailWord_4815233
  simp only [CollatzResearch.WordTrace]
  refine ⟨175625975764240692168786353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117083983842827128112524235 175625975764240692168786353)
  ·
    refine ⟨131719481823180519126589765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175625975764240692168786353 131719481823180519126589765)
    ·
      refine ⟨24697402841846347336235581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131719481823180519126589765 24697402841846347336235581)
      ·
        refine ⟨9261526065692380251088343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24697402841846347336235581 9261526065692380251088343)
        ·
          refine ⟨13892289098538570376632515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9261526065692380251088343 13892289098538570376632515)
          ·
            refine ⟨20838433647807855564948773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13892289098538570376632515 20838433647807855564948773)
            ·
              refine ⟨3907206308963972918427895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20838433647807855564948773 3907206308963972918427895)
              ·
                refine ⟨5860809463445959377641843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3907206308963972918427895 5860809463445959377641843)
                ·
                  refine ⟨8791214195168939066462765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5860809463445959377641843 8791214195168939066462765)
                  ·
                    refine ⟨3296705323188352149923537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8791214195168939066462765 3296705323188352149923537)
                    ·
                      refine ⟨2472528992391264112442653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3296705323188352149923537 2472528992391264112442653)
                      ·
                        rfl

theorem cell23_4815233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_4815233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815233 prefixEnd_4815233 := by exact prefixLift 4815233
  have htrace : WordTrace (prefixWord ++ tailWord_4815233) baseStart_4815233 baseEnd_4815233 := by
    simpa [prefixWord, tailWord_4815233, baseEnd_4815233] using wordTrace_append hprefix tailTrace_4815233
  have hstable : (prefixWord ++ tailWord_4815233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815233).length < 2 ^ (prefixWord ++ tailWord_4815233).sum := by decide
  have hdescent : baseEnd_4815233 < baseStart_4815233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815263 : List Nat := [1, 1, 2, 5, 1, 1, 5, 1, 2, 2, 2]
def baseStart_4815263 : Nat := 118140960795 + 4815263 * 2 ^ 59
def prefixEnd_4815263 : Nat := 4983230072969 + 3 ^ 40 * 4815263 * 2
def baseEnd_4815263 : Nat := 2472544396810898995067515

theorem tailTrace_4815263 : CollatzResearch.WordTrace tailWord_4815263 prefixEnd_4815263 2472544396810898995067515 := by
  unfold tailWord_4815263
  simp only [CollatzResearch.WordTrace]
  refine ⟨175627069954132007292378443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117084713302754671528252295 175627069954132007292378443)
  ·
    refine ⟨263440604931198010938567665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175627069954132007292378443 263440604931198010938567665)
    ·
      refine ⟨197580453698398508203925749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263440604931198010938567665 197580453698398508203925749)
      ·
        refine ⟨18523167534224860144118039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 197580453698398508203925749 18523167534224860144118039)
        ·
          refine ⟨27784751301337290216177059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18523167534224860144118039 27784751301337290216177059)
          ·
            refine ⟨41677126952005935324265589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27784751301337290216177059 41677126952005935324265589)
            ·
              refine ⟨3907230651750556436649899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41677126952005935324265589 3907230651750556436649899)
              ·
                refine ⟨5860845977625834654974849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3907230651750556436649899 5860845977625834654974849)
                ·
                  refine ⟨4395634483219375991231137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5860845977625834654974849 4395634483219375991231137)
                  ·
                    refine ⟨3296725862414531993423353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4395634483219375991231137 3296725862414531993423353)
                    ·
                      refine ⟨2472544396810898995067515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3296725862414531993423353 2472544396810898995067515)
                      ·
                        rfl

theorem cell23_4815263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_4815263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815263 prefixEnd_4815263 := by exact prefixLift 4815263
  have htrace : WordTrace (prefixWord ++ tailWord_4815263) baseStart_4815263 baseEnd_4815263 := by
    simpa [prefixWord, tailWord_4815263, baseEnd_4815263] using wordTrace_append hprefix tailTrace_4815263
  have hstable : (prefixWord ++ tailWord_4815263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815263).length < 2 ^ (prefixWord ++ tailWord_4815263).sum := by decide
  have hdescent : baseEnd_4815263 < baseStart_4815263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815282 : List Nat := [3, 2, 1, 1, 1, 1, 4, 3, 2, 5]
def baseStart_4815282 : Nat := 118140960795 + 4815282 * 2 ^ 59
def prefixEnd_4815282 : Nat := 4983230072969 + 3 ^ 40 * 4815282 * 2
def baseEnd_4815282 : Nat := 824184717647778140243309

theorem tailTrace_4815282 : CollatzResearch.WordTrace tailWord_4815282 prefixEnd_4815282 824184717647778140243309 := by
  unfold tailWord_4815282
  simp only [CollatzResearch.WordTrace]
  refine ⟨43906940735265793384330025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117085175294042115691546733 43906940735265793384330025)
  ·
    refine ⟨32930205551449345038247519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43906940735265793384330025 32930205551449345038247519)
    ·
      refine ⟨49395308327174017557371279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32930205551449345038247519 49395308327174017557371279)
      ·
        refine ⟨74092962490761026336056919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49395308327174017557371279 74092962490761026336056919)
        ·
          refine ⟨111139443736141539504085379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74092962490761026336056919 111139443736141539504085379)
          ·
            refine ⟨166709165604212309256128069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111139443736141539504085379 166709165604212309256128069)
            ·
              refine ⟨31257968550789807985524013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 166709165604212309256128069 31257968550789807985524013)
              ·
                refine ⟨11721738206546177994571505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31257968550789807985524013 11721738206546177994571505)
                ·
                  refine ⟨8791303654909633495928629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11721738206546177994571505 8791303654909633495928629)
                  ·
                    refine ⟨824184717647778140243309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8791303654909633495928629 824184717647778140243309)
                    ·
                      rfl

theorem cell23_4815282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_4815282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815282 prefixEnd_4815282 := by exact prefixLift 4815282
  have htrace : WordTrace (prefixWord ++ tailWord_4815282) baseStart_4815282 baseEnd_4815282 := by
    simpa [prefixWord, tailWord_4815282, baseEnd_4815282] using wordTrace_append hprefix tailTrace_4815282
  have hstable : (prefixWord ++ tailWord_4815282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815282).length < 2 ^ (prefixWord ++ tailWord_4815282).sum := by decide
  have hdescent : baseEnd_4815282 < baseStart_4815282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815314 : List Nat := [3, 2, 2, 4, 2, 1, 2, 1, 2, 2, 2]
def baseStart_4815314 : Nat := 118140960795 + 4815314 * 2 ^ 59
def prefixEnd_4815314 : Nat := 4983230072969 + 3 ^ 40 * 4815314 * 2
def baseEnd_4815314 : Nat := 2472570584324278295529781

theorem tailTrace_4815314 : CollatzResearch.WordTrace tailWord_4815314 prefixEnd_4815314 2472570584324278295529781 := by
  unfold tailWord_4815314
  simp only [CollatzResearch.WordTrace]
  refine ⟨43907232519236810750621249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117085953384631495334989997 43907232519236810750621249)
  ·
    refine ⟨32930424389427608062965937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43907232519236810750621249 32930424389427608062965937)
    ·
      refine ⟨24697818292070706047224453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32930424389427608062965937 24697818292070706047224453)
      ·
        refine ⟨4630840929763257383854585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24697818292070706047224453 4630840929763257383854585)
        ·
          refine ⟨3473130697322443037890939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4630840929763257383854585 3473130697322443037890939)
          ·
            refine ⟨5209696045983664556836409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3473130697322443037890939 5209696045983664556836409)
            ·
              refine ⟨3907272034487748417627307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5209696045983664556836409 3907272034487748417627307)
              ·
                refine ⟨5860908051731622626440961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3907272034487748417627307 5860908051731622626440961)
                ·
                  refine ⟨4395681038798716969830721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5860908051731622626440961 4395681038798716969830721)
                  ·
                    refine ⟨3296760779099037727373041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4395681038798716969830721 3296760779099037727373041)
                    ·
                      refine ⟨2472570584324278295529781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3296760779099037727373041 2472570584324278295529781)
                      ·
                        rfl

theorem cell23_4815314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_4815314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815314 prefixEnd_4815314 := by exact prefixLift 4815314
  have htrace : WordTrace (prefixWord ++ tailWord_4815314) baseStart_4815314 baseEnd_4815314 := by
    simpa [prefixWord, tailWord_4815314, baseEnd_4815314] using wordTrace_append hprefix tailTrace_4815314
  have hstable : (prefixWord ++ tailWord_4815314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815314).length < 2 ^ (prefixWord ++ tailWord_4815314).sum := by decide
  have hdescent : baseEnd_4815314 < baseStart_4815314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815315 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 6]
def baseStart_4815315 : Nat := 118140960795 + 4815315 * 2 ^ 59
def prefixEnd_4815315 : Nat := 4983230072969 + 3 ^ 40 * 4815315 * 2
def baseEnd_4815315 : Nat := 2472571097804932791617275

theorem tailTrace_4815315 : CollatzResearch.WordTrace tailWord_4815315 prefixEnd_4815315 2472571097804932791617275 := by
  unfold tailWord_4815315
  simp only [CollatzResearch.WordTrace]
  refine ⟨175628966549943620173271399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117085977699962413448847599 175628966549943620173271399)
  ·
    refine ⟨263443449824915430259907099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175628966549943620173271399 263443449824915430259907099)
    ·
      refine ⟨395165174737373145389860649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263443449824915430259907099 395165174737373145389860649)
      ·
        refine ⟨296373881053029859042395487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395165174737373145389860649 296373881053029859042395487)
        ·
          refine ⟨444560821579544788563593231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296373881053029859042395487 444560821579544788563593231)
          ·
            refine ⟨666841232369317182845389847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444560821579544788563593231 666841232369317182845389847)
            ·
              refine ⟨1000261848553975774268084771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 666841232369317182845389847 1000261848553975774268084771)
              ·
                refine ⟨1500392772830963661402127157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1000261848553975774268084771 1500392772830963661402127157)
                ·
                  refine ⟨140661822452902843256449421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1500392772830963661402127157 140661822452902843256449421)
                  ·
                    refine ⟨52748183419838566221168533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 140661822452902843256449421 52748183419838566221168533)
                    ·
                      refine ⟨2472571097804932791617275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52748183419838566221168533 2472571097804932791617275)
                      ·
                        rfl

theorem cell23_4815315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_4815315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815315 prefixEnd_4815315 := by exact prefixLift 4815315
  have htrace : WordTrace (prefixWord ++ tailWord_4815315) baseStart_4815315 baseEnd_4815315 := by
    simpa [prefixWord, tailWord_4815315, baseEnd_4815315] using wordTrace_append hprefix tailTrace_4815315
  have hstable : (prefixWord ++ tailWord_4815315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815315).length < 2 ^ (prefixWord ++ tailWord_4815315).sum := by decide
  have hdescent : baseEnd_4815315 < baseStart_4815315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815339 : List Nat := [1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 3]
def baseStart_4815339 : Nat := 118140960795 + 4815339 * 2 ^ 59
def prefixEnd_4815339 : Nat := 4983230072969 + 3 ^ 40 * 4815339 * 2
def baseEnd_4815339 : Nat := 2472583421340640697717165

theorem tailTrace_4815339 : CollatzResearch.WordTrace tailWord_4815339 prefixEnd_4815339 2472583421340640697717165 := by
  unfold tailWord_4815339
  simp only [CollatzResearch.WordTrace]
  refine ⟨175629841901856672272145071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117086561267904448181430047 175629841901856672272145071)
  ·
    refine ⟨263444762852785008408217607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175629841901856672272145071 263444762852785008408217607)
    ·
      refine ⟨395167144279177512612326411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263444762852785008408217607 395167144279177512612326411)
      ·
        refine ⟨592750716418766268918489617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395167144279177512612326411 592750716418766268918489617)
        ·
          refine ⟨444563037314074701688867213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 592750716418766268918489617 444563037314074701688867213)
          ·
            refine ⟨166711138992778013133325205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 444563037314074701688867213 166711138992778013133325205)
            ·
              refine ⟨7814584640286469365624619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 166711138992778013133325205 7814584640286469365624619)
              ·
                refine ⟨11721876960429704048436929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7814584640286469365624619 11721876960429704048436929)
                ·
                  refine ⟨8791407720322278036327697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11721876960429704048436929 8791407720322278036327697)
                  ·
                    refine ⟨6593555790241708527245773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8791407720322278036327697 6593555790241708527245773)
                    ·
                      refine ⟨2472583421340640697717165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6593555790241708527245773 2472583421340640697717165)
                      ·
                        rfl

theorem cell23_4815339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 3].length) (baseStart_4815339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815339 prefixEnd_4815339 := by exact prefixLift 4815339
  have htrace : WordTrace (prefixWord ++ tailWord_4815339) baseStart_4815339 baseEnd_4815339 := by
    simpa [prefixWord, tailWord_4815339, baseEnd_4815339] using wordTrace_append hprefix tailTrace_4815339
  have hstable : (prefixWord ++ tailWord_4815339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815339).length < 2 ^ (prefixWord ++ tailWord_4815339).sum := by decide
  have hdescent : baseEnd_4815339 < baseStart_4815339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815379 : List Nat := [1, 1, 1, 2, 1, 5, 2, 2, 1, 5, 2]
def baseStart_4815379 : Nat := 118140960795 + 4815379 * 2 ^ 59
def prefixEnd_4815379 : Nat := 4983230072969 + 3 ^ 40 * 4815379 * 2
def baseEnd_4815379 : Nat := 2472603960566820541216981

theorem tailTrace_4815379 : CollatzResearch.WordTrace tailWord_4815379 prefixEnd_4815379 2472603960566820541216981 := by
  unfold tailWord_4815379
  simp only [CollatzResearch.WordTrace]
  refine ⟨175631300821711759103601191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117087533881141172735734127 175631300821711759103601191)
  ·
    refine ⟨263446951232567638655401787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175631300821711759103601191 263446951232567638655401787)
    ·
      refine ⟨395170426848851457983102681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263446951232567638655401787 395170426848851457983102681)
      ·
        refine ⟨296377820136638593487327011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395170426848851457983102681 296377820136638593487327011)
        ·
          refine ⟨444566730204957890230990517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296377820136638593487327011 444566730204957890230990517)
          ·
            refine ⟨41678130956714802209155361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 444566730204957890230990517 41678130956714802209155361)
            ·
              refine ⟨31258598217536101656866521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41678130956714802209155361 31258598217536101656866521)
              ·
                refine ⟨23443948663152076242649891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31258598217536101656866521 23443948663152076242649891)
                ·
                  refine ⟨35165922994728114363974837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23443948663152076242649891 35165922994728114363974837)
                  ·
                    refine ⟨3296805280755760721622641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35165922994728114363974837 3296805280755760721622641)
                    ·
                      refine ⟨2472603960566820541216981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3296805280755760721622641 2472603960566820541216981)
                      ·
                        rfl

theorem cell23_4815379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 5, 2].length) (baseStart_4815379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815379 prefixEnd_4815379 := by exact prefixLift 4815379
  have htrace : WordTrace (prefixWord ++ tailWord_4815379) baseStart_4815379 baseEnd_4815379 := by
    simpa [prefixWord, tailWord_4815379, baseEnd_4815379] using wordTrace_append hprefix tailTrace_4815379
  have hstable : (prefixWord ++ tailWord_4815379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815379).length < 2 ^ (prefixWord ++ tailWord_4815379).sum := by decide
  have hdescent : baseEnd_4815379 < baseStart_4815379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815389 : List Nat := [1, 4, 2, 2, 1, 2, 2, 1, 3, 5]
def baseStart_4815389 : Nat := 118140960795 + 4815389 * 2 ^ 59
def prefixEnd_4815389 : Nat := 4983230072969 + 3 ^ 40 * 4815389 * 2
def baseEnd_4815389 : Nat := 824203031791121834030645

theorem tailTrace_4815389 : CollatzResearch.WordTrace tailWord_4815389 prefixEnd_4815389 824203031791121834030645 := by
  unfold tailWord_4815389
  simp only [CollatzResearch.WordTrace]
  refine ⟨175631665551675530811465221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117087777034450353874310147 175631665551675530811465221)
  ·
    refine ⟨32930937290939162027149729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175631665551675530811465221 32930937290939162027149729)
    ·
      refine ⟨24698202968204371520362297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32930937290939162027149729 24698202968204371520362297)
      ·
        refine ⟨18523652226153278640271723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24698202968204371520362297 18523652226153278640271723)
        ·
          refine ⟨27785478339229917960407585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18523652226153278640271723 27785478339229917960407585)
          ·
            refine ⟨20839108754422438470305689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27785478339229917960407585 20839108754422438470305689)
            ·
              refine ⟨15629331565816828852729267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20839108754422438470305689 15629331565816828852729267)
              ·
                refine ⟨23443997348725243279093901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15629331565816828852729267 23443997348725243279093901)
                ·
                  refine ⟨8791499005771966229660213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23443997348725243279093901 8791499005771966229660213)
                  ·
                    refine ⟨824203031791121834030645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8791499005771966229660213 824203031791121834030645)
                    ·
                      rfl

theorem cell23_4815389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_4815389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815389 prefixEnd_4815389 := by exact prefixLift 4815389
  have htrace : WordTrace (prefixWord ++ tailWord_4815389) baseStart_4815389 baseEnd_4815389 := by
    simpa [prefixWord, tailWord_4815389, baseEnd_4815389] using wordTrace_append hprefix tailTrace_4815389
  have hstable : (prefixWord ++ tailWord_4815389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815389).length < 2 ^ (prefixWord ++ tailWord_4815389).sum := by decide
  have hdescent : baseEnd_4815389 < baseStart_4815389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815429 : List Nat := [1, 3, 1, 1, 1, 6, 1, 2, 1, 1, 5]
def baseStart_4815429 : Nat := 118140960795 + 4815429 * 2 ^ 59
def prefixEnd_4815429 : Nat := 4983230072969 + 3 ^ 40 * 4815429 * 2
def baseEnd_4815429 : Nat := 2472629634599545345591751

theorem tailTrace_4815429 : CollatzResearch.WordTrace tailWord_4815429 prefixEnd_4815429 2472629634599545345591751 := by
  unfold tailWord_4815429
  simp only [CollatzResearch.WordTrace]
  refine ⟨175633124471530617642921341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117088749647687078428614227 175633124471530617642921341)
  ·
    refine ⟨65862421676823981616095503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175633124471530617642921341 65862421676823981616095503)
    ·
      refine ⟨98793632515235972424143255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65862421676823981616095503 98793632515235972424143255)
      ·
        refine ⟨148190448772853958636214883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98793632515235972424143255 148190448772853958636214883)
        ·
          refine ⟨222285673159280937954322325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148190448772853958636214883 222285673159280937954322325)
          ·
            refine ⟨10419640929341293966608859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 222285673159280937954322325 10419640929341293966608859)
            ·
              refine ⟨15629461394011940949913289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10419640929341293966608859 15629461394011940949913289)
              ·
                refine ⟨11722096045508955712434967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15629461394011940949913289 11722096045508955712434967)
                ·
                  refine ⟨17583144068263433568652451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11722096045508955712434967 17583144068263433568652451)
                  ·
                    refine ⟨26374716102395150352978677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17583144068263433568652451 26374716102395150352978677)
                    ·
                      refine ⟨2472629634599545345591751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26374716102395150352978677 2472629634599545345591751)
                      ·
                        rfl

theorem cell23_4815429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_4815429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815429 prefixEnd_4815429 := by exact prefixLift 4815429
  have htrace : WordTrace (prefixWord ++ tailWord_4815429) baseStart_4815429 baseEnd_4815429 := by
    simpa [prefixWord, tailWord_4815429, baseEnd_4815429] using wordTrace_append hprefix tailTrace_4815429
  have hstable : (prefixWord ++ tailWord_4815429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815429).length < 2 ^ (prefixWord ++ tailWord_4815429).sum := by decide
  have hdescent : baseEnd_4815429 < baseStart_4815429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815439 : List Nat := [1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 4]
def baseStart_4815439 : Nat := 118140960795 + 4815439 * 2 ^ 59
def prefixEnd_4815439 : Nat := 4983230072969 + 3 ^ 40 * 4815439 * 2
def baseEnd_4815439 : Nat := 2472634769406090306466705

theorem tailTrace_4815439 : CollatzResearch.WordTrace tailWord_4815439 prefixEnd_4815439 2472634769406090306466705 := by
  unfold tailWord_4815439
  simp only [CollatzResearch.WordTrace]
  refine ⟨175633489201494389350785371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117088992800996259567190247 175633489201494389350785371)
  ·
    refine ⟨263450233802241584026178057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175633489201494389350785371 263450233802241584026178057)
    ·
      refine ⟨197587675351681188019633543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263450233802241584026178057 197587675351681188019633543)
      ·
        refine ⟨296381513027521782029450315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197587675351681188019633543 296381513027521782029450315)
        ·
          refine ⟨444572269541282673044175473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296381513027521782029450315 444572269541282673044175473)
          ·
            refine ⟨333429202155962004783131605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 444572269541282673044175473 333429202155962004783131605)
            ·
              refine ⟨7814746925530359487104647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 333429202155962004783131605 7814746925530359487104647)
              ·
                refine ⟨11722120388295539230656971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7814746925530359487104647 11722120388295539230656971)
                ·
                  refine ⟨17583180582443308845985457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11722120388295539230656971 17583180582443308845985457)
                  ·
                    refine ⟨13187385436832481634489093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17583180582443308845985457 13187385436832481634489093)
                    ·
                      refine ⟨2472634769406090306466705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13187385436832481634489093 2472634769406090306466705)
                      ·
                        rfl

theorem cell23_4815439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 4].length) (baseStart_4815439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815439 prefixEnd_4815439 := by exact prefixLift 4815439
  have htrace : WordTrace (prefixWord ++ tailWord_4815439) baseStart_4815439 baseEnd_4815439 := by
    simpa [prefixWord, tailWord_4815439, baseEnd_4815439] using wordTrace_append hprefix tailTrace_4815439
  have hstable : (prefixWord ++ tailWord_4815439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815439).length < 2 ^ (prefixWord ++ tailWord_4815439).sum := by decide
  have hdescent : baseEnd_4815439 < baseStart_4815439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815459 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 3]
def baseStart_4815459 : Nat := 118140960795 + 4815459 * 2 ^ 59
def prefixEnd_4815459 : Nat := 4983230072969 + 3 ^ 40 * 4815459 * 2
def baseEnd_4815459 : Nat := 2472645039019180228216613

theorem tailTrace_4815459 : CollatzResearch.WordTrace tailWord_4815459 prefixEnd_4815459 2472645039019180228216613 := by
  unfold tailWord_4815459
  simp only [CollatzResearch.WordTrace]
  refine ⟨175634218661421932766513431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117089479107614621844342287 175634218661421932766513431)
  ·
    refine ⟨263451327992132899149770147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175634218661421932766513431 263451327992132899149770147)
    ·
      refine ⟨395176991988199348724655221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263451327992132899149770147 395176991988199348724655221)
      ·
        refine ⟨37047842998893688942936427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 395176991988199348724655221 37047842998893688942936427)
        ·
          refine ⟨55571764498340533414404641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37047842998893688942936427 55571764498340533414404641)
          ·
            refine ⟨41678823373755400060803481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55571764498340533414404641 41678823373755400060803481)
            ·
              refine ⟨31259117530316550045602611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41678823373755400060803481 31259117530316550045602611)
              ·
                refine ⟨46888676295474825068403917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31259117530316550045602611 46888676295474825068403917)
                ·
                  refine ⟨17583253610803059400651469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46888676295474825068403917 17583253610803059400651469)
                  ·
                    refine ⟨6593720104051147275244301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17583253610803059400651469 6593720104051147275244301)
                    ·
                      refine ⟨2472645039019180228216613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6593720104051147275244301 2472645039019180228216613)
                      ·
                        rfl

theorem cell23_4815459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_4815459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815459 prefixEnd_4815459 := by exact prefixLift 4815459
  have htrace : WordTrace (prefixWord ++ tailWord_4815459) baseStart_4815459 baseEnd_4815459 := by
    simpa [prefixWord, tailWord_4815459, baseEnd_4815459] using wordTrace_append hprefix tailTrace_4815459
  have hstable : (prefixWord ++ tailWord_4815459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815459).length < 2 ^ (prefixWord ++ tailWord_4815459).sum := by decide
  have hdescent : baseEnd_4815459 < baseStart_4815459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815477 : List Nat := [1, 3, 4, 2, 2, 2, 1, 1, 3, 2, 2]
def baseStart_4815477 : Nat := 118140960795 + 4815477 * 2 ^ 59
def prefixEnd_4815477 : Nat := 4983230072969 + 3 ^ 40 * 4815477 * 2
def baseEnd_4815477 : Nat := 2472654281670961157791531

theorem tailTrace_4815477 : CollatzResearch.WordTrace tailWord_4815477 prefixEnd_4815477 2472654281670961157791531 := by
  unfold tailWord_4815477
  simp only [CollatzResearch.WordTrace]
  refine ⟨175634875175356721840668685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117089916783571147893779123 175634875175356721840668685)
  ·
    refine ⟨65863078190758770690250757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175634875175356721840668685 65863078190758770690250757)
    ·
      refine ⟨12349327160767269504422017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65863078190758770690250757 12349327160767269504422017)
      ·
        refine ⟨9261995370575452128316513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12349327160767269504422017 9261995370575452128316513)
        ·
          refine ⟨6946496527931589096237385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9261995370575452128316513 6946496527931589096237385)
          ·
            refine ⟨5209872395948691822178039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6946496527931589096237385 5209872395948691822178039)
            ·
              refine ⟨7814808593923037733267059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5209872395948691822178039 7814808593923037733267059)
              ·
                refine ⟨11722212890884556599900589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7814808593923037733267059 11722212890884556599900589)
                ·
                  refine ⟨4395829834081708724962721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11722212890884556599900589 4395829834081708724962721)
                  ·
                    refine ⟨3296872375561281543722041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4395829834081708724962721 3296872375561281543722041)
                    ·
                      refine ⟨2472654281670961157791531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3296872375561281543722041 2472654281670961157791531)
                      ·
                        rfl

theorem cell23_4815477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_4815477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815477 prefixEnd_4815477 := by exact prefixLift 4815477
  have htrace : WordTrace (prefixWord ++ tailWord_4815477) baseStart_4815477 baseEnd_4815477 := by
    simpa [prefixWord, tailWord_4815477, baseEnd_4815477] using wordTrace_append hprefix tailTrace_4815477
  have hstable : (prefixWord ++ tailWord_4815477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815477).length < 2 ^ (prefixWord ++ tailWord_4815477).sum := by decide
  have hdescent : baseEnd_4815477 < baseStart_4815477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4815482 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10]
def baseStart_4815482 : Nat := 118140960795 + 4815482 * 2 ^ 59
def prefixEnd_4815482 : Nat := 4983230072969 + 3 ^ 40 * 4815482 * 2
def baseEnd_4815482 : Nat := 2472656849074233638229007

theorem tailTrace_4815482 : CollatzResearch.WordTrace tailWord_4815482 prefixEnd_4815482 2472656849074233638229007 := by
  unfold tailWord_4815482
  simp only [CollatzResearch.WordTrace]
  refine ⟨43908764385084651923650175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117090038360225738463067133 43908764385084651923650175)
  ·
    refine ⟨65863146577626977885475263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43908764385084651923650175 65863146577626977885475263)
    ·
      refine ⟨98794719866440466828212895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65863146577626977885475263 98794719866440466828212895)
      ·
        refine ⟨148192079799660700242319343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98794719866440466828212895 148192079799660700242319343)
        ·
          refine ⟨222288119699491050363479015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148192079799660700242319343 222288119699491050363479015)
          ·
            refine ⟨333432179549236575545218523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222288119699491050363479015 333432179549236575545218523)
            ·
              refine ⟨500148269323854863317827785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333432179549236575545218523 500148269323854863317827785)
              ·
                refine ⟨375111201992891147488370839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 500148269323854863317827785 375111201992891147488370839)
                ·
                  refine ⟨562666802989336721232556259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 375111201992891147488370839 562666802989336721232556259)
                  ·
                    refine ⟨844000204484005081848834389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 562666802989336721232556259 844000204484005081848834389)
                    ·
                      refine ⟨2472656849074233638229007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 844000204484005081848834389 2472656849074233638229007)
                      ·
                        rfl

theorem cell23_4815482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_4815482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4815482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4815482 prefixEnd_4815482 := by exact prefixLift 4815482
  have htrace : WordTrace (prefixWord ++ tailWord_4815482) baseStart_4815482 baseEnd_4815482 := by
    simpa [prefixWord, tailWord_4815482, baseEnd_4815482] using wordTrace_append hprefix tailTrace_4815482
  have hstable : (prefixWord ++ tailWord_4815482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4815482).length < 2 ^ (prefixWord ++ tailWord_4815482).sum := by decide
  have hdescent : baseEnd_4815482 < baseStart_4815482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4815482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
