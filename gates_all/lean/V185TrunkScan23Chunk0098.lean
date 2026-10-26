import V185TrunkScan23Chunk0097

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_580924 : List Nat := [2, 2, 2, 2, 1, 3, 2, 1, 2, 1, 5]
def baseStart_580924 : Nat := 118140960795 + 580924 * 2 ^ 59
def prefixEnd_580924 : Nat := 4983230072969 + 3 ^ 40 * 580924 * 2
def baseEnd_580924 : Nat := 298293235732590365878385

theorem tailTrace_580924 : CollatzResearch.WordTrace tailWord_580924 prefixEnd_580924 298293235732590365878385 := by
  unfold tailWord_580924
  simp only [CollatzResearch.WordTrace]
  refine ⟨10594019473709518382742913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14125359298279357843657217 10594019473709518382742913)
  ·
    refine ⟨7945514605282138787057185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10594019473709518382742913 7945514605282138787057185)
    ·
      refine ⟨5959135953961604090292889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7945514605282138787057185 5959135953961604090292889)
      ·
        refine ⟨4469351965471203067719667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5959135953961604090292889 4469351965471203067719667)
        ·
          refine ⟨6704027948206804601579501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4469351965471203067719667 6704027948206804601579501)
          ·
            refine ⟨2514010480577551725592313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6704027948206804601579501 2514010480577551725592313)
            ·
              refine ⟨1885507860433163794194235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2514010480577551725592313 1885507860433163794194235)
              ·
                refine ⟨2828261790649745691291353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1885507860433163794194235 2828261790649745691291353)
                ·
                  refine ⟨2121196342987309268468515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2828261790649745691291353 2121196342987309268468515)
                  ·
                    refine ⟨3181794514480963902702773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2121196342987309268468515 3181794514480963902702773)
                    ·
                      refine ⟨298293235732590365878385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3181794514480963902702773 298293235732590365878385)
                      ·
                        rfl

theorem cell23_580924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_580924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580924 prefixEnd_580924 := by exact prefixLift 580924
  have htrace : WordTrace (prefixWord ++ tailWord_580924) baseStart_580924 baseEnd_580924 := by
    simpa [prefixWord, tailWord_580924, baseEnd_580924] using wordTrace_append hprefix tailTrace_580924
  have hstable : (prefixWord ++ tailWord_580924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580924).length < 2 ^ (prefixWord ++ tailWord_580924).sum := by decide
  have hdescent : baseEnd_580924 < baseStart_580924 := by decide
  rcases family_descends (prefixWord ++ tailWord_580924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580937 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 1, 2, 7]
def baseStart_580937 : Nat := 118140960795 + 580937 * 2 ^ 59
def prefixEnd_580937 : Nat := 4983230072969 + 3 ^ 40 * 580937 * 2
def baseEnd_580937 : Nat := 298299910981098815015825

theorem tailTrace_580937 : CollatzResearch.WordTrace tailWord_580937 prefixEnd_580937 298299910981098815015825 := by
  unfold tailWord_580937
  simp only [CollatzResearch.WordTrace]
  refine ⟨21188513096371939985709065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14125675397581293323806043 21188513096371939985709065)
  ·
    refine ⟨15891384822278954989281799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21188513096371939985709065 15891384822278954989281799)
    ·
      refine ⟨23837077233418432483922699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15891384822278954989281799 23837077233418432483922699)
      ·
        refine ⟨35755615850127648725884049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23837077233418432483922699 35755615850127648725884049)
        ·
          refine ⟨26816711887595736544413037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35755615850127648725884049 26816711887595736544413037)
          ·
            refine ⟨10056266957848401204154889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26816711887595736544413037 10056266957848401204154889)
            ·
              refine ⟨7542200218386300903116167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10056266957848401204154889 7542200218386300903116167)
              ·
                refine ⟨11313300327579451354674251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7542200218386300903116167 11313300327579451354674251)
                ·
                  refine ⟨16969950491369177032011377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11313300327579451354674251 16969950491369177032011377)
                  ·
                    refine ⟨12727462868526882774008533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16969950491369177032011377 12727462868526882774008533)
                    ·
                      refine ⟨298299910981098815015825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 12727462868526882774008533 298299910981098815015825)
                      ·
                        rfl

theorem cell23_580937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_580937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580937 prefixEnd_580937 := by exact prefixLift 580937
  have htrace : WordTrace (prefixWord ++ tailWord_580937) baseStart_580937 baseEnd_580937 := by
    simpa [prefixWord, tailWord_580937, baseEnd_580937] using wordTrace_append hprefix tailTrace_580937
  have hstable : (prefixWord ++ tailWord_580937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580937).length < 2 ^ (prefixWord ++ tailWord_580937).sum := by decide
  have hdescent : baseEnd_580937 < baseStart_580937 := by decide
  rcases family_descends (prefixWord ++ tailWord_580937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580954 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3]
def baseStart_580954 : Nat := 118140960795 + 580954 * 2 ^ 59
def prefixEnd_580954 : Nat := 4983230072969 + 3 ^ 40 * 580954 * 2
def baseEnd_580954 : Nat := 298308640152225248503247

theorem tailTrace_580954 : CollatzResearch.WordTrace tailWord_580954 prefixEnd_580954 298308640152225248503247 := by
  unfold tailWord_580954
  simp only [CollatzResearch.WordTrace]
  refine ⟨5297283284327587972269479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14126088758206901259385277 5297283284327587972269479)
  ·
    refine ⟨7945924926491381958404219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5297283284327587972269479 7945924926491381958404219)
    ·
      refine ⟨11918887389737072937606329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7945924926491381958404219 11918887389737072937606329)
      ·
        refine ⟨8939165542302804703204747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11918887389737072937606329 8939165542302804703204747)
        ·
          refine ⟨13408748313454207054807121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8939165542302804703204747 13408748313454207054807121)
          ·
            refine ⟨10056561235090655291105341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13408748313454207054807121 10056561235090655291105341)
            ·
              refine ⟨3771210463158995734164503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10056561235090655291105341 3771210463158995734164503)
              ·
                refine ⟨5656815694738493601246755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3771210463158995734164503 5656815694738493601246755)
                ·
                  refine ⟨8485223542107740401870133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5656815694738493601246755 8485223542107740401870133)
                  ·
                    refine ⟨795489707072600662675325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8485223542107740401870133 795489707072600662675325)
                    ·
                      refine ⟨298308640152225248503247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 795489707072600662675325 298308640152225248503247)
                      ·
                        rfl

theorem cell23_580954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_580954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580954 prefixEnd_580954 := by exact prefixLift 580954
  have htrace : WordTrace (prefixWord ++ tailWord_580954) baseStart_580954 baseEnd_580954 := by
    simpa [prefixWord, tailWord_580954, baseEnd_580954] using wordTrace_append hprefix tailTrace_580954
  have hstable : (prefixWord ++ tailWord_580954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580954).length < 2 ^ (prefixWord ++ tailWord_580954).sum := by decide
  have hdescent : baseEnd_580954 < baseStart_580954 := by decide
  rcases family_descends (prefixWord ++ tailWord_580954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581024 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 4]
def baseStart_581024 : Nat := 118140960795 + 581024 * 2 ^ 59
def prefixEnd_581024 : Nat := 4983230072969 + 3 ^ 40 * 581024 * 2
def baseEnd_581024 : Nat := 298344583798039974627925

theorem tailTrace_581024 : CollatzResearch.WordTrace tailWord_581024 prefixEnd_581024 298344583798039974627925 := by
  unfold tailWord_581024
  simp only [CollatzResearch.WordTrace]
  refine ⟨10595843123528376922063063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14127790831371169229417417 10595843123528376922063063)
  ·
    refine ⟨15893764685292565383094595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10595843123528376922063063 15893764685292565383094595)
    ·
      refine ⟨23840647027938848074641893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15893764685292565383094595 23840647027938848074641893)
      ·
        refine ⟨4470121317738534013995355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23840647027938848074641893 4470121317738534013995355)
        ·
          refine ⟨6705181976607801020993033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4470121317738534013995355 6705181976607801020993033)
          ·
            refine ⟨5028886482455850765744775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6705181976607801020993033 5028886482455850765744775)
            ·
              refine ⟨7543329723683776148617163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5028886482455850765744775 7543329723683776148617163)
              ·
                refine ⟨11314994585525664222925745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7543329723683776148617163 11314994585525664222925745)
                ·
                  refine ⟨8486245939144248167194309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11314994585525664222925745 8486245939144248167194309)
                  ·
                    refine ⟨1591171113589546531348933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8486245939144248167194309 1591171113589546531348933)
                    ·
                      refine ⟨298344583798039974627925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1591171113589546531348933 298344583798039974627925)
                      ·
                        rfl

theorem cell23_581024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_581024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581024 prefixEnd_581024 := by exact prefixLift 581024
  have htrace : WordTrace (prefixWord ++ tailWord_581024) baseStart_581024 baseEnd_581024 := by
    simpa [prefixWord, tailWord_581024, baseEnd_581024] using wordTrace_append hprefix tailTrace_581024
  have hstable : (prefixWord ++ tailWord_581024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581024).length < 2 ^ (prefixWord ++ tailWord_581024).sum := by decide
  have hdescent : baseEnd_581024 < baseStart_581024 := by decide
  rcases family_descends (prefixWord ++ tailWord_581024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581031 : List Nat := [1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_581031 : Nat := 118140960795 + 581031 * 2 ^ 59
def prefixEnd_581031 : Nat := 4983230072969 + 3 ^ 40 * 581031 * 2
def baseEnd_581031 : Nat := 298348178162621447240393

theorem tailTrace_581031 : CollatzResearch.WordTrace tailWord_581031 prefixEnd_581031 298348178162621447240393 := by
  unfold tailWord_581031
  simp only [CollatzResearch.WordTrace]
  refine ⟨21191941558031394039630947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14127961038687596026420631 21191941558031394039630947)
  ·
    refine ⟨31787912337047091059446421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21191941558031394039630947 31787912337047091059446421)
    ·
      refine ⟨1490058390799082393411551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31787912337047091059446421 1490058390799082393411551)
      ·
        refine ⟨2235087586198623590117327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1490058390799082393411551 2235087586198623590117327)
        ·
          refine ⟨3352631379297935385175991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2235087586198623590117327 3352631379297935385175991)
          ·
            refine ⟨5028947068946903077763987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3352631379297935385175991 5028947068946903077763987)
            ·
              refine ⟨7543420603420354616645981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5028947068946903077763987 7543420603420354616645981)
              ·
                refine ⟨2828782726282632981242243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7543420603420354616645981 2828782726282632981242243)
                ·
                  refine ⟨4243174089423949471863365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2828782726282632981242243 4243174089423949471863365)
                  ·
                    refine ⟨795595141766990525974381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4243174089423949471863365 795595141766990525974381)
                    ·
                      refine ⟨298348178162621447240393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 795595141766990525974381 298348178162621447240393)
                      ·
                        rfl

theorem cell23_581031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_581031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581031 prefixEnd_581031 := by exact prefixLift 581031
  have htrace : WordTrace (prefixWord ++ tailWord_581031) baseStart_581031 baseEnd_581031 := by
    simpa [prefixWord, tailWord_581031, baseEnd_581031] using wordTrace_append hprefix tailTrace_581031
  have hstable : (prefixWord ++ tailWord_581031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581031).length < 2 ^ (prefixWord ++ tailWord_581031).sum := by decide
  have hdescent : baseEnd_581031 < baseStart_581031 := by decide
  rcases family_descends (prefixWord ++ tailWord_581031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581068 : List Nat := [2, 2, 1, 4, 2, 1, 4, 1, 6]
def baseStart_581068 : Nat := 118140960795 + 581068 * 2 ^ 59
def prefixEnd_581068 : Nat := 4983230072969 + 3 ^ 40 * 581068 * 2
def baseEnd_581068 : Nat := 33151908549648644719747

theorem tailTrace_581068 : CollatzResearch.WordTrace tailWord_581068 prefixEnd_581068 33151908549648644719747 := by
  unfold tailWord_581068
  simp only [CollatzResearch.WordTrace]
  refine ⟨10596645529448674679363929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14128860705931566239151905 10596645529448674679363929)
  ·
    refine ⟨7947484147086506009522947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10596645529448674679363929 7947484147086506009522947)
    ·
      refine ⟨11921226220629759014284421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7947484147086506009522947 11921226220629759014284421)
      ·
        refine ⟨2235229916368079815178329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11921226220629759014284421 2235229916368079815178329)
        ·
          refine ⟨1676422437276059861383747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2235229916368079815178329 1676422437276059861383747)
          ·
            refine ⟨2514633655914089792075621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1676422437276059861383747 2514633655914089792075621)
            ·
              refine ⟨471493810483891836014179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2514633655914089792075621 471493810483891836014179)
              ·
                refine ⟨707240715725837754021269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 471493810483891836014179 707240715725837754021269)
                ·
                  refine ⟨33151908549648644719747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 707240715725837754021269 33151908549648644719747)
                  ·
                    rfl

theorem cell23_581068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 6].length) (baseStart_581068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581068 prefixEnd_581068 := by exact prefixLift 581068
  have htrace : WordTrace (prefixWord ++ tailWord_581068) baseStart_581068 baseEnd_581068 := by
    simpa [prefixWord, tailWord_581068, baseEnd_581068] using wordTrace_append hprefix tailTrace_581068
  have hstable : (prefixWord ++ tailWord_581068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581068).length < 2 ^ (prefixWord ++ tailWord_581068).sum := by decide
  have hdescent : baseEnd_581068 < baseStart_581068 := by decide
  rcases family_descends (prefixWord ++ tailWord_581068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581071 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 3, 5, 2]
def baseStart_581071 : Nat := 118140960795 + 581071 * 2 ^ 59
def prefixEnd_581071 : Nat := 4983230072969 + 3 ^ 40 * 581071 * 2
def baseEnd_581071 : Nat := 298368717388801290740209

theorem tailTrace_581071 : CollatzResearch.WordTrace tailWord_581071 prefixEnd_581071 298368717388801290740209 := by
  unfold tailWord_581071
  simp only [CollatzResearch.WordTrace]
  refine ⟨21193400477886480871087067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14128933651924320580724711 21193400477886480871087067)
  ·
    refine ⟨31790100716829721306630601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21193400477886480871087067 31790100716829721306630601)
    ·
      refine ⟨23842575537622290979972951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31790100716829721306630601 23842575537622290979972951)
      ·
        refine ⟨35763863306433436469959427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23842575537622290979972951 35763863306433436469959427)
        ·
          refine ⟨53645794959650154704939141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35763863306433436469959427 53645794959650154704939141)
          ·
            refine ⟨10058586554934404007176089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53645794959650154704939141 10058586554934404007176089)
            ·
              refine ⟨7543939916200803005382067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10058586554934404007176089 7543939916200803005382067)
              ·
                refine ⟨11315909874301204508073101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7543939916200803005382067 11315909874301204508073101)
                ·
                  refine ⟨4243466202862951690527413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11315909874301204508073101 4243466202862951690527413)
                  ·
                    refine ⟨397824956518401720986945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4243466202862951690527413 397824956518401720986945)
                    ·
                      refine ⟨298368717388801290740209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 397824956518401720986945 298368717388801290740209)
                      ·
                        rfl

theorem cell23_581071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 5, 2].length) (baseStart_581071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581071 prefixEnd_581071 := by exact prefixLift 581071
  have htrace : WordTrace (prefixWord ++ tailWord_581071) baseStart_581071 baseEnd_581071 := by
    simpa [prefixWord, tailWord_581071, baseEnd_581071] using wordTrace_append hprefix tailTrace_581071
  have hstable : (prefixWord ++ tailWord_581071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581071).length < 2 ^ (prefixWord ++ tailWord_581071).sum := by decide
  have hdescent : baseEnd_581071 < baseStart_581071 := by decide
  rcases family_descends (prefixWord ++ tailWord_581071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581081 : List Nat := [1, 2, 1, 2, 4, 3, 1, 1, 3, 5]
def baseStart_581081 : Nat := 118140960795 + 581081 * 2 ^ 59
def prefixEnd_581081 : Nat := 4983230072969 + 3 ^ 40 * 581081 * 2
def baseEnd_581081 : Nat := 99457950731782083871721

theorem tailTrace_581081 : CollatzResearch.WordTrace tailWord_581081 prefixEnd_581081 99457950731782083871721 := by
  unfold tailWord_581081
  simp only [CollatzResearch.WordTrace]
  refine ⟨21193765207850252578951097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14129176805233501719300731 21193765207850252578951097)
  ·
    refine ⟨15895323905887689434213323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21193765207850252578951097 15895323905887689434213323)
    ·
      refine ⟨23842985858831534151319985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15895323905887689434213323 23842985858831534151319985)
      ·
        refine ⟨17882239394123650613489989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23842985858831534151319985 17882239394123650613489989)
        ·
          refine ⟨3352919886398184490029373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17882239394123650613489989 3352919886398184490029373)
          ·
            refine ⟨1257344957399319183761015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3352919886398184490029373 1257344957399319183761015)
            ·
              refine ⟨1886017436098978775641523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1257344957399319183761015 1886017436098978775641523)
              ·
                refine ⟨2829026154148468163462285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1886017436098978775641523 2829026154148468163462285)
                ·
                  refine ⟨1060884807805675561298357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2829026154148468163462285 1060884807805675561298357)
                  ·
                    refine ⟨99457950731782083871721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1060884807805675561298357 99457950731782083871721)
                    ·
                      rfl

theorem cell23_581081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 5].length) (baseStart_581081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581081 prefixEnd_581081 := by exact prefixLift 581081
  have htrace : WordTrace (prefixWord ++ tailWord_581081) baseStart_581081 baseEnd_581081 := by
    simpa [prefixWord, tailWord_581081, baseEnd_581081] using wordTrace_append hprefix tailTrace_581081
  have hstable : (prefixWord ++ tailWord_581081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581081).length < 2 ^ (prefixWord ++ tailWord_581081).sum := by decide
  have hdescent : baseEnd_581081 < baseStart_581081 := by decide
  rcases family_descends (prefixWord ++ tailWord_581081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581112 : List Nat := [2, 1, 2, 1, 1, 5, 4, 2, 1, 1, 3]
def baseStart_581112 : Nat := 118140960795 + 581112 * 2 ^ 59
def prefixEnd_581112 : Nat := 4983230072969 + 3 ^ 40 * 581112 * 2
def baseEnd_581112 : Nat := 298389770095635630327521

theorem tailTrace_581112 : CollatzResearch.WordTrace tailWord_581112 prefixEnd_581112 298389770095635630327521 := by
  unfold tailWord_581112
  simp only [CollatzResearch.WordTrace]
  refine ⟨10597447935368972436664795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14129930580491963248886393 10597447935368972436664795)
  ·
    refine ⟨15896171903053458654997193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10597447935368972436664795 15896171903053458654997193)
    ·
      refine ⟨11922128927290093991247895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15896171903053458654997193 11922128927290093991247895)
      ·
        refine ⟨17883193390935140986871843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11922128927290093991247895 17883193390935140986871843)
        ·
          refine ⟨26824790086402711480307765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17883193390935140986871843 26824790086402711480307765)
          ·
            refine ⟨2514824070600254201278853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26824790086402711480307765 2514824070600254201278853)
            ·
              refine ⟨471529513237547662739785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2514824070600254201278853 471529513237547662739785)
              ·
                refine ⟨353647134928160747054839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 471529513237547662739785 353647134928160747054839)
                ·
                  refine ⟨530470702392241120582259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 353647134928160747054839 530470702392241120582259)
                  ·
                    refine ⟨795706053588361680873389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 530470702392241120582259 795706053588361680873389)
                    ·
                      refine ⟨298389770095635630327521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 795706053588361680873389 298389770095635630327521)
                      ·
                        rfl

theorem cell23_581112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 1, 1, 3].length) (baseStart_581112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581112 prefixEnd_581112 := by exact prefixLift 581112
  have htrace : WordTrace (prefixWord ++ tailWord_581112) baseStart_581112 baseEnd_581112 := by
    simpa [prefixWord, tailWord_581112, baseEnd_581112] using wordTrace_append hprefix tailTrace_581112
  have hstable : (prefixWord ++ tailWord_581112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581112).length < 2 ^ (prefixWord ++ tailWord_581112).sum := by decide
  have hdescent : baseEnd_581112 < baseStart_581112 := by decide
  rcases family_descends (prefixWord ++ tailWord_581112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581128 : List Nat := [2, 1, 3, 2, 1, 1, 4, 3, 2, 4]
def baseStart_581128 : Nat := 118140960795 + 581128 * 2 ^ 59
def prefixEnd_581128 : Nat := 4983230072969 + 3 ^ 40 * 581128 * 2
def baseEnd_581128 : Nat := 99465995262035855909149

theorem tailTrace_581128 : CollatzResearch.WordTrace tailWord_581128 prefixEnd_581128 99465995262035855909149 := by
  unfold tailWord_581128
  simp only [CollatzResearch.WordTrace]
  refine ⟨10597739719339989802956019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14130319625786653070608025 10597739719339989802956019)
  ·
    refine ⟨15896609579009984704434029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10597739719339989802956019 15896609579009984704434029)
    ·
      refine ⟨5961228592128744264162761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15896609579009984704434029 5961228592128744264162761)
      ·
        refine ⟨4470921444096558198122071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5961228592128744264162761 4470921444096558198122071)
        ·
          refine ⟨6706382166144837297183107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4470921444096558198122071 6706382166144837297183107)
          ·
            refine ⟨10059573249217255945774661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6706382166144837297183107 10059573249217255945774661)
            ·
              refine ⟨1886169984228235489832749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10059573249217255945774661 1886169984228235489832749)
              ·
                refine ⟨707313744085588308687281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1886169984228235489832749 707313744085588308687281)
                ·
                  refine ⟨530485308064191231515461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 707313744085588308687281 530485308064191231515461)
                  ·
                    refine ⟨99465995262035855909149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 530485308064191231515461 99465995262035855909149)
                    ·
                      rfl

theorem cell23_581128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_581128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581128 prefixEnd_581128 := by exact prefixLift 581128
  have htrace : WordTrace (prefixWord ++ tailWord_581128) baseStart_581128 baseEnd_581128 := by
    simpa [prefixWord, tailWord_581128, baseEnd_581128] using wordTrace_append hprefix tailTrace_581128
  have hstable : (prefixWord ++ tailWord_581128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581128).length < 2 ^ (prefixWord ++ tailWord_581128).sum := by decide
  have hdescent : baseEnd_581128 < baseStart_581128 := by decide
  rcases family_descends (prefixWord ++ tailWord_581128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581152 : List Nat := [2, 1, 1, 6, 1, 3, 2, 1, 1, 1, 4]
def baseStart_581152 : Nat := 118140960795 + 581152 * 2 ^ 59
def prefixEnd_581152 : Nat := 4983230072969 + 3 ^ 40 * 581152 * 2
def baseEnd_581152 : Nat := 298410309321815473827337

theorem tailTrace_581152 : CollatzResearch.WordTrace tailWord_581152 prefixEnd_581152 298410309321815473827337 := by
  unfold tailWord_581152
  simp only [CollatzResearch.WordTrace]
  refine ⟨10598177395296515852392855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14130903193728687803190473 10598177395296515852392855)
  ·
    refine ⟨15897266092944773778589283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10598177395296515852392855 15897266092944773778589283)
    ·
      refine ⟨23845899139417160667883925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15897266092944773778589283 23845899139417160667883925)
      ·
        refine ⟨1117776522160179406307059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23845899139417160667883925 1117776522160179406307059)
        ·
          refine ⟨1676664783240269109460589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1117776522160179406307059 1676664783240269109460589)
          ·
            refine ⟨628749293715100916047721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1676664783240269109460589 628749293715100916047721)
            ·
              refine ⟨471561970286325687035791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 628749293715100916047721 471561970286325687035791)
              ·
                refine ⟨707342955429488530553687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 471561970286325687035791 707342955429488530553687)
                ·
                  refine ⟨1061014433144232795830531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 707342955429488530553687 1061014433144232795830531)
                  ·
                    refine ⟨1591521649716349193745797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1061014433144232795830531 1591521649716349193745797)
                    ·
                      refine ⟨298410309321815473827337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1591521649716349193745797 298410309321815473827337)
                      ·
                        rfl

theorem cell23_581152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_581152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581152 prefixEnd_581152 := by exact prefixLift 581152
  have htrace : WordTrace (prefixWord ++ tailWord_581152) baseStart_581152 baseEnd_581152 := by
    simpa [prefixWord, tailWord_581152, baseEnd_581152] using wordTrace_append hprefix tailTrace_581152
  have hstable : (prefixWord ++ tailWord_581152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581152).length < 2 ^ (prefixWord ++ tailWord_581152).sum := by decide
  have hdescent : baseEnd_581152 < baseStart_581152 := by decide
  rcases family_descends (prefixWord ++ tailWord_581152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581155 : List Nat := [1, 1, 1, 4, 5, 1, 1, 3, 1, 2, 3]
def baseStart_581155 : Nat := 118140960795 + 581155 * 2 ^ 59
def prefixEnd_581155 : Nat := 4983230072969 + 3 ^ 40 * 581155 * 2
def baseEnd_581155 : Nat := 298411849763778962089823

theorem tailTrace_581155 : CollatzResearch.WordTrace tailWord_581155 prefixEnd_581155 298411849763778962089823 := by
  unfold tailWord_581155
  simp only [CollatzResearch.WordTrace]
  refine ⟨21196464209582163217144919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14130976139721442144763279 21196464209582163217144919)
  ·
    refine ⟨31794696314373244825717379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21196464209582163217144919 31794696314373244825717379)
    ·
      refine ⟨47692044471559867238576069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31794696314373244825717379 47692044471559867238576069)
      ·
        refine ⟨8942258338417475107233013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47692044471559867238576069 8942258338417475107233013)
        ·
          refine ⟨838336719226638291303095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8942258338417475107233013 838336719226638291303095)
          ·
            refine ⟨1257505078839957436954643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 838336719226638291303095 1257505078839957436954643)
            ·
              refine ⟨1886257618259936155431965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1257505078839957436954643 1886257618259936155431965)
              ·
                refine ⟨707346606847476058286987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1886257618259936155431965 707346606847476058286987)
                ·
                  refine ⟨1061019910271214087430481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 707346606847476058286987 1061019910271214087430481)
                  ·
                    refine ⟨795764932703410565572861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1061019910271214087430481 795764932703410565572861)
                    ·
                      refine ⟨298411849763778962089823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 795764932703410565572861 298411849763778962089823)
                      ·
                        rfl

theorem cell23_581155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_581155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581155 prefixEnd_581155 := by exact prefixLift 581155
  have htrace : WordTrace (prefixWord ++ tailWord_581155) baseStart_581155 baseEnd_581155 := by
    simpa [prefixWord, tailWord_581155, baseEnd_581155] using wordTrace_append hprefix tailTrace_581155
  have hstable : (prefixWord ++ tailWord_581155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581155).length < 2 ^ (prefixWord ++ tailWord_581155).sum := by decide
  have hdescent : baseEnd_581155 < baseStart_581155 := by decide
  rcases family_descends (prefixWord ++ tailWord_581155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581208 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 3, 4, 2]
def baseStart_581208 : Nat := 118140960795 + 581208 * 2 ^ 59
def prefixEnd_581208 : Nat := 4983230072969 + 3 ^ 40 * 581208 * 2
def baseEnd_581208 : Nat := 298439064238467254727079

theorem tailTrace_581208 : CollatzResearch.WordTrace tailWord_581208 prefixEnd_581208 298439064238467254727079 := by
  unfold tailWord_581208
  simp only [CollatzResearch.WordTrace]
  refine ⟨10599198639195076634412139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14132264852260102179216185 10599198639195076634412139)
  ·
    refine ⟨15898797958792614951618209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10599198639195076634412139 15898797958792614951618209)
    ·
      refine ⟨11924098469094461213713657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15898797958792614951618209 11924098469094461213713657)
      ·
        refine ⟨8943073851820845910285243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11924098469094461213713657 8943073851820845910285243)
        ·
          refine ⟨13414610777731268865427865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8943073851820845910285243 13414610777731268865427865)
          ·
            refine ⟨10060958083298451649070899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13414610777731268865427865 10060958083298451649070899)
            ·
              refine ⟨15091437124947677473606349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10060958083298451649070899 15091437124947677473606349)
              ·
                refine ⟨5659288921855379052602381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15091437124947677473606349 5659288921855379052602381)
                ·
                  refine ⟨2122233345695767144725893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5659288921855379052602381 2122233345695767144725893)
                  ·
                    refine ⟨397918752317956339636105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2122233345695767144725893 397918752317956339636105)
                    ·
                      refine ⟨298439064238467254727079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 397918752317956339636105 298439064238467254727079)
                      ·
                        rfl

theorem cell23_581208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 3, 4, 2].length) (baseStart_581208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581208 prefixEnd_581208 := by exact prefixLift 581208
  have htrace : WordTrace (prefixWord ++ tailWord_581208) baseStart_581208 baseEnd_581208 := by
    simpa [prefixWord, tailWord_581208, baseEnd_581208] using wordTrace_append hprefix tailTrace_581208
  have hstable : (prefixWord ++ tailWord_581208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581208).length < 2 ^ (prefixWord ++ tailWord_581208).sum := by decide
  have hdescent : baseEnd_581208 < baseStart_581208 := by decide
  rcases family_descends (prefixWord ++ tailWord_581208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581212 : List Nat := [2, 2, 4, 1, 2, 1, 2, 3, 1, 3, 2]
def baseStart_581212 : Nat := 118140960795 + 581212 * 2 ^ 59
def prefixEnd_581212 : Nat := 4983230072969 + 3 ^ 40 * 581212 * 2
def baseEnd_581212 : Nat := 298441118161085239077061

theorem tailTrace_581212 : CollatzResearch.WordTrace tailWord_581212 prefixEnd_581212 298441118161085239077061 := by
  unfold tailWord_581212
  simp only [CollatzResearch.WordTrace]
  refine ⟨10599271585187830975984945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14132362113583774634646593 10599271585187830975984945)
  ·
    refine ⟨7949453688890873231988709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10599271585187830975984945 7949453688890873231988709)
    ·
      refine ⟨1490522566667038730997883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7949453688890873231988709 1490522566667038730997883)
      ·
        refine ⟨2235783850000558096496825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1490522566667038730997883 2235783850000558096496825)
        ·
          refine ⟨1676837887500418572372619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2235783850000558096496825 1676837887500418572372619)
          ·
            refine ⟨2515256831250627858558929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1676837887500418572372619 2515256831250627858558929)
            ·
              refine ⟨1886442623437970893919197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2515256831250627858558929 1886442623437970893919197)
              ·
                refine ⟨707415983789239085219699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1886442623437970893919197 707415983789239085219699)
                ·
                  refine ⟨1061123975683858627829549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 707415983789239085219699 1061123975683858627829549)
                  ·
                    refine ⟨397921490881446985436081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1061123975683858627829549 397921490881446985436081)
                    ·
                      refine ⟨298441118161085239077061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 397921490881446985436081 298441118161085239077061)
                      ·
                        rfl

theorem cell23_581212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_581212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581212 prefixEnd_581212 := by exact prefixLift 581212
  have htrace : WordTrace (prefixWord ++ tailWord_581212) baseStart_581212 baseEnd_581212 := by
    simpa [prefixWord, tailWord_581212, baseEnd_581212] using wordTrace_append hprefix tailTrace_581212
  have hstable : (prefixWord ++ tailWord_581212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581212).length < 2 ^ (prefixWord ++ tailWord_581212).sum := by decide
  have hdescent : baseEnd_581212 < baseStart_581212 := by decide
  rcases family_descends (prefixWord ++ tailWord_581212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581225 : List Nat := [1, 2, 1, 1, 1, 4, 4, 1, 4, 2, 2]
def baseStart_581225 : Nat := 118140960795 + 581225 * 2 ^ 59
def prefixEnd_581225 : Nat := 4983230072969 + 3 ^ 40 * 581225 * 2
def baseEnd_581225 : Nat := 298447793409593688214501

theorem tailTrace_581225 : CollatzResearch.WordTrace tailWord_581225 prefixEnd_581225 298447793409593688214501 := by
  unfold tailWord_581225
  simp only [CollatzResearch.WordTrace]
  refine ⟨21199017319328565172193129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14132678212885710114795419 21199017319328565172193129)
  ·
    refine ⟨15899262989496423879144847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21199017319328565172193129 15899262989496423879144847)
    ·
      refine ⟨23848894484244635818717271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15899262989496423879144847 23848894484244635818717271)
      ·
        refine ⟨35773341726366953728075907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23848894484244635818717271 35773341726366953728075907)
        ·
          refine ⟨53660012589550430592113861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35773341726366953728075907 53660012589550430592113861)
          ·
            refine ⟨10061252360540705736021349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53660012589550430592113861 10061252360540705736021349)
            ·
              refine ⟨1886484817601382325504003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10061252360540705736021349 1886484817601382325504003)
              ·
                refine ⟨2829727226402073488256005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1886484817601382325504003 2829727226402073488256005)
                ·
                  refine ⟨530573854950388779048001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2829727226402073488256005 530573854950388779048001)
                  ·
                    refine ⟨397930391212791584286001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 530573854950388779048001 397930391212791584286001)
                    ·
                      refine ⟨298447793409593688214501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 397930391212791584286001 298447793409593688214501)
                      ·
                        rfl

theorem cell23_581225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 2, 2].length) (baseStart_581225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581225 prefixEnd_581225 := by exact prefixLift 581225
  have htrace : WordTrace (prefixWord ++ tailWord_581225) baseStart_581225 baseEnd_581225 := by
    simpa [prefixWord, tailWord_581225, baseEnd_581225] using wordTrace_append hprefix tailTrace_581225
  have hstable : (prefixWord ++ tailWord_581225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581225).length < 2 ^ (prefixWord ++ tailWord_581225).sum := by decide
  have hdescent : baseEnd_581225 < baseStart_581225 := by decide
  rcases family_descends (prefixWord ++ tailWord_581225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581298 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4]
def baseStart_581298 : Nat := 118140960795 + 581298 * 2 ^ 59
def prefixEnd_581298 : Nat := 4983230072969 + 3 ^ 40 * 581298 * 2
def baseEnd_581298 : Nat := 298485277497371902601665

theorem tailTrace_581298 : CollatzResearch.WordTrace tailWord_581298 prefixEnd_581298 298485277497371902601665 := by
  unfold tailWord_581298
  simp only [CollatzResearch.WordTrace]
  refine ⟨5300419962016024659900137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14134453232042732426400365 5300419962016024659900137)
  ·
    refine ⟨3975314971512018494925103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5300419962016024659900137 3975314971512018494925103)
    ·
      refine ⟨5962972457268027742387655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3975314971512018494925103 5962972457268027742387655)
      ·
        refine ⟨8944458685902041613581483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5962972457268027742387655 8944458685902041613581483)
        ·
          refine ⟨13416688028853062420372225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8944458685902041613581483 13416688028853062420372225)
          ·
            refine ⟨10062516021639796815279169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13416688028853062420372225 10062516021639796815279169)
            ·
              refine ⟨7546887016229847611459377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10062516021639796815279169 7546887016229847611459377)
              ·
                refine ⟨5660165262172385708594533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7546887016229847611459377 5660165262172385708594533)
                ·
                  refine ⟨1061280986657322320361475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5660165262172385708594533 1061280986657322320361475)
                  ·
                    refine ⟨1591921479985983480542213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1061280986657322320361475 1591921479985983480542213)
                    ·
                      refine ⟨298485277497371902601665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1591921479985983480542213 298485277497371902601665)
                      ·
                        rfl

theorem cell23_581298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_581298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581298 prefixEnd_581298 := by exact prefixLift 581298
  have htrace : WordTrace (prefixWord ++ tailWord_581298) baseStart_581298 baseEnd_581298 := by
    simpa [prefixWord, tailWord_581298, baseEnd_581298] using wordTrace_append hprefix tailTrace_581298
  have hstable : (prefixWord ++ tailWord_581298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581298).length < 2 ^ (prefixWord ++ tailWord_581298).sum := by decide
  have hdescent : baseEnd_581298 < baseStart_581298 := by decide
  rcases family_descends (prefixWord ++ tailWord_581298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581332 : List Nat := [2, 4, 1, 3, 1, 1, 1, 2, 2, 4, 2]
def baseStart_581332 : Nat := 118140960795 + 581332 * 2 ^ 59
def prefixEnd_581332 : Nat := 4983230072969 + 3 ^ 40 * 581332 * 2
def baseEnd_581332 : Nat := 298502735839624769576509

theorem tailTrace_581332 : CollatzResearch.WordTrace tailWord_581332 prefixEnd_581332 298502735839624769576509 := by
  unfold tailWord_581332
  simp only [CollatzResearch.WordTrace]
  refine ⟨10601459964970461223169125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14135279953293948297558833 10601459964970461223169125)
  ·
    refine ⟨1987773743431961479344211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10601459964970461223169125 1987773743431961479344211)
    ·
      refine ⟨2981660615147942219016317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1987773743431961479344211 2981660615147942219016317)
      ·
        refine ⟨1118122730680478332131119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2981660615147942219016317 1118122730680478332131119)
        ·
          refine ⟨1677184096020717498196679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1118122730680478332131119 1677184096020717498196679)
          ·
            refine ⟨2515776144031076247295019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1677184096020717498196679 2515776144031076247295019)
            ·
              refine ⟨3773664216046614370942529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2515776144031076247295019 3773664216046614370942529)
              ·
                refine ⟨2830248162034960778206897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3773664216046614370942529 2830248162034960778206897)
                ·
                  refine ⟨2122686121526220583655173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2830248162034960778206897 2122686121526220583655173)
                  ·
                    refine ⟨398003647786166359435345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2122686121526220583655173 398003647786166359435345)
                    ·
                      refine ⟨298502735839624769576509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 398003647786166359435345 298502735839624769576509)
                      ·
                        rfl

theorem cell23_581332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_581332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581332 prefixEnd_581332 := by exact prefixLift 581332
  have htrace : WordTrace (prefixWord ++ tailWord_581332) baseStart_581332 baseEnd_581332 := by
    simpa [prefixWord, tailWord_581332, baseEnd_581332] using wordTrace_append hprefix tailTrace_581332
  have hstable : (prefixWord ++ tailWord_581332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581332).length < 2 ^ (prefixWord ++ tailWord_581332).sum := by decide
  have hdescent : baseEnd_581332 < baseStart_581332 := by decide
  rcases family_descends (prefixWord ++ tailWord_581332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581338 : List Nat := [3, 1, 1, 2, 2, 4, 1, 1, 8]
def baseStart_581338 : Nat := 118140960795 + 581338 * 2 ^ 59
def prefixEnd_581338 : Nat := 4983230072969 + 3 ^ 40 * 581338 * 2
def baseEnd_581338 : Nat := 33167312969283527344609

theorem tailTrace_581338 : CollatzResearch.WordTrace tailWord_581338 prefixEnd_581338 33167312969283527344609 := by
  unfold tailWord_581338
  simp only [CollatzResearch.WordTrace]
  refine ⟨5300784691979796367764167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14135425845279456980704445 5300784691979796367764167)
  ·
    refine ⟨7951177037969694551646251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5300784691979796367764167 7951177037969694551646251)
    ·
      refine ⟨11926765556954541827469377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7951177037969694551646251 11926765556954541827469377)
      ·
        refine ⟨8945074167715906370602033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11926765556954541827469377 8945074167715906370602033)
        ·
          refine ⟨6708805625786929777951525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8945074167715906370602033 6708805625786929777951525)
          ·
            refine ⟨1257901054835049333365911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6708805625786929777951525 1257901054835049333365911)
            ·
              refine ⟨1886851582252574000048867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1257901054835049333365911 1886851582252574000048867)
              ·
                refine ⟨2830277373378861000073301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1886851582252574000048867 2830277373378861000073301)
                ·
                  refine ⟨33167312969283527344609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2830277373378861000073301 33167312969283527344609)
                  ·
                    rfl

theorem cell23_581338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 8].length) (baseStart_581338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581338 prefixEnd_581338 := by exact prefixLift 581338
  have htrace : WordTrace (prefixWord ++ tailWord_581338) baseStart_581338 baseEnd_581338 := by
    simpa [prefixWord, tailWord_581338, baseEnd_581338] using wordTrace_append hprefix tailTrace_581338
  have hstable : (prefixWord ++ tailWord_581338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581338).length < 2 ^ (prefixWord ++ tailWord_581338).sum := by decide
  have hdescent : baseEnd_581338 < baseStart_581338 := by decide
  rcases family_descends (prefixWord ++ tailWord_581338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581358 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_581358 : Nat := 118140960795 + 581358 * 2 ^ 59
def prefixEnd_581358 : Nat := 4983230072969 + 3 ^ 40 * 581358 * 2
def baseEnd_581358 : Nat := 298516086336641667851389

theorem tailTrace_581358 : CollatzResearch.WordTrace tailWord_581358 prefixEnd_581358 298516086336641667851389 := by
  unfold tailWord_581358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2650483528480841110848091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14135912151897819257856485 2650483528480841110848091)
  ·
    refine ⟨3975725292721261666272137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2650483528480841110848091 3975725292721261666272137)
    ·
      refine ⟨2981793969540946249704103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3975725292721261666272137 2981793969540946249704103)
      ·
        refine ⟨4472690954311419374556155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2981793969540946249704103 4472690954311419374556155)
        ·
          refine ⟨6709036431467129061834233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4472690954311419374556155 6709036431467129061834233)
          ·
            refine ⟨5031777323600346796375675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6709036431467129061834233 5031777323600346796375675)
            ·
              refine ⟨7547665985400520194563513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5031777323600346796375675 7547665985400520194563513)
              ·
                refine ⟨5660749489050390145922635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7547665985400520194563513 5660749489050390145922635)
                ·
                  refine ⟨8491124233575585218883953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5660749489050390145922635 8491124233575585218883953)
                  ·
                    refine ⟨6368343175181688914162965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8491124233575585218883953 6368343175181688914162965)
                    ·
                      refine ⟨298516086336641667851389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6368343175181688914162965 298516086336641667851389)
                      ·
                        rfl

theorem cell23_581358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_581358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581358 prefixEnd_581358 := by exact prefixLift 581358
  have htrace : WordTrace (prefixWord ++ tailWord_581358) baseStart_581358 baseEnd_581358 := by
    simpa [prefixWord, tailWord_581358, baseEnd_581358] using wordTrace_append hprefix tailTrace_581358
  have hstable : (prefixWord ++ tailWord_581358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581358).length < 2 ^ (prefixWord ++ tailWord_581358).sum := by decide
  have hdescent : baseEnd_581358 < baseStart_581358 := by decide
  rcases family_descends (prefixWord ++ tailWord_581358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581375 : List Nat := [1, 1, 2, 2, 1, 3, 4, 1, 1, 5, 2]
def baseStart_581375 : Nat := 118140960795 + 581375 * 2 ^ 59
def prefixEnd_581375 : Nat := 4983230072969 + 3 ^ 40 * 581375 * 2
def baseEnd_581375 : Nat := 298524815507768101338811

theorem tailTrace_581375 : CollatzResearch.WordTrace tailWord_581375 prefixEnd_581375 298524815507768101338811 := by
  unfold tailWord_581375
  simp only [CollatzResearch.WordTrace]
  refine ⟨21204488268785140790153579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14136325512523427193435719 21204488268785140790153579)
  ·
    refine ⟨31806732403177711185230369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21204488268785140790153579 31806732403177711185230369)
    ·
      refine ⟨23855049302383283388922777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31806732403177711185230369 23855049302383283388922777)
      ·
        refine ⟨17891286976787462541692083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23855049302383283388922777 17891286976787462541692083)
        ·
          refine ⟨26836930465181193812538125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17891286976787462541692083 26836930465181193812538125)
          ·
            refine ⟨10063848924442947679701797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26836930465181193812538125 10063848924442947679701797)
            ·
              refine ⟨1886971673333052689944087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10063848924442947679701797 1886971673333052689944087)
              ·
                refine ⟨2830457509999579034916131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1886971673333052689944087 2830457509999579034916131)
                ·
                  refine ⟨4245686264999368552374197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2830457509999579034916131 4245686264999368552374197)
                  ·
                    refine ⟨398033087343690801785081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4245686264999368552374197 398033087343690801785081)
                    ·
                      refine ⟨298524815507768101338811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 398033087343690801785081 298524815507768101338811)
                      ·
                        rfl

theorem cell23_581375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 5, 2].length) (baseStart_581375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581375 prefixEnd_581375 := by exact prefixLift 581375
  have htrace : WordTrace (prefixWord ++ tailWord_581375) baseStart_581375 baseEnd_581375 := by
    simpa [prefixWord, tailWord_581375, baseEnd_581375] using wordTrace_append hprefix tailTrace_581375
  have hstable : (prefixWord ++ tailWord_581375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581375).length < 2 ^ (prefixWord ++ tailWord_581375).sum := by decide
  have hdescent : baseEnd_581375 < baseStart_581375 := by decide
  rcases family_descends (prefixWord ++ tailWord_581375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581399 : List Nat := [1, 1, 3, 4, 2, 3, 1, 1, 3, 1, 3]
def baseStart_581399 : Nat := 118140960795 + 581399 * 2 ^ 59
def prefixEnd_581399 : Nat := 4983230072969 + 3 ^ 40 * 581399 * 2
def baseEnd_581399 : Nat := 298537139043476007438701

theorem tailTrace_581399 : CollatzResearch.WordTrace tailWord_581399 prefixEnd_581399 298537139043476007438701 := by
  unfold tailWord_581399
  simp only [CollatzResearch.WordTrace]
  refine ⟨21205363620698192889027251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14136909080465461926018167 21205363620698192889027251)
  ·
    refine ⟨31808045431047289333540877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21205363620698192889027251 31808045431047289333540877)
    ·
      refine ⟨11928017036642733500077829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31808045431047289333540877 11928017036642733500077829)
      ·
        refine ⟨2236503194370512531264593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11928017036642733500077829 2236503194370512531264593)
        ·
          refine ⟨1677377395777884398448445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2236503194370512531264593 1677377395777884398448445)
          ·
            refine ⟨629016523416706649418167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1677377395777884398448445 629016523416706649418167)
            ·
              refine ⟨943524785125059974127251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 629016523416706649418167 943524785125059974127251)
              ·
                refine ⟨1415287177687589961190877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 943524785125059974127251 1415287177687589961190877)
                ·
                  refine ⟨530732691632846235446579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1415287177687589961190877 530732691632846235446579)
                  ·
                    refine ⟨796099037449269353169869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 530732691632846235446579 796099037449269353169869)
                    ·
                      refine ⟨298537139043476007438701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 796099037449269353169869 298537139043476007438701)
                      ·
                        rfl

theorem cell23_581399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_581399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581399 prefixEnd_581399 := by exact prefixLift 581399
  have htrace : WordTrace (prefixWord ++ tailWord_581399) baseStart_581399 baseEnd_581399 := by
    simpa [prefixWord, tailWord_581399, baseEnd_581399] using wordTrace_append hprefix tailTrace_581399
  have hstable : (prefixWord ++ tailWord_581399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581399).length < 2 ^ (prefixWord ++ tailWord_581399).sum := by decide
  have hdescent : baseEnd_581399 < baseStart_581399 := by decide
  rcases family_descends (prefixWord ++ tailWord_581399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581439 : List Nat := [1, 1, 2, 2, 6, 1, 3, 1, 1, 1, 4]
def baseStart_581439 : Nat := 118140960795 + 581439 * 2 ^ 59
def prefixEnd_581439 : Nat := 4983230072969 + 3 ^ 40 * 581439 * 2
def baseEnd_581439 : Nat := 298557678269655850938517

theorem tailTrace_581439 : CollatzResearch.WordTrace tailWord_581439 prefixEnd_581439 298557678269655850938517 := by
  unfold tailWord_581439
  simp only [CollatzResearch.WordTrace]
  refine ⟨21206822540553279720483371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14137881693702186480322247 21206822540553279720483371)
  ·
    refine ⟨31810233810829919580725057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21206822540553279720483371 31810233810829919580725057)
    ·
      refine ⟨23857675358122439685543793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31810233810829919580725057 23857675358122439685543793)
      ·
        refine ⟨17893256518591829764157845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23857675358122439685543793 17893256518591829764157845)
        ·
          refine ⟨838746399308992020194899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17893256518591829764157845 838746399308992020194899)
          ·
            refine ⟨1258119598963488030292349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 838746399308992020194899 1258119598963488030292349)
            ·
              refine ⟨471794849611308011359631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1258119598963488030292349 471794849611308011359631)
              ·
                refine ⟨707692274416962017039447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 471794849611308011359631 707692274416962017039447)
                ·
                  refine ⟨1061538411625443025559171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 707692274416962017039447 1061538411625443025559171)
                  ·
                    refine ⟨1592307617438164538338757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1061538411625443025559171 1592307617438164538338757)
                    ·
                      refine ⟨298557678269655850938517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1592307617438164538338757 298557678269655850938517)
                      ·
                        rfl

theorem cell23_581439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 1, 1, 4].length) (baseStart_581439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581439 prefixEnd_581439 := by exact prefixLift 581439
  have htrace : WordTrace (prefixWord ++ tailWord_581439) baseStart_581439 baseEnd_581439 := by
    simpa [prefixWord, tailWord_581439, baseEnd_581439] using wordTrace_append hprefix tailTrace_581439
  have hstable : (prefixWord ++ tailWord_581439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581439).length < 2 ^ (prefixWord ++ tailWord_581439).sum := by decide
  have hdescent : baseEnd_581439 < baseStart_581439 := by decide
  rcases family_descends (prefixWord ++ tailWord_581439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581472 : List Nat := [2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 3]
def baseStart_581472 : Nat := 118140960795 + 581472 * 2 ^ 59
def prefixEnd_581472 : Nat := 4983230072969 + 3 ^ 40 * 581472 * 2
def baseEnd_581472 : Nat := 298574623131254221825865

theorem tailTrace_581472 : CollatzResearch.WordTrace tailWord_581472 prefixEnd_581472 298574623131254221825865 := by
  unfold tailWord_581472
  simp only [CollatzResearch.WordTrace]
  refine ⟨10604013074716863178217335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14138684099622484237623113 10604013074716863178217335)
  ·
    refine ⟨15906019612075294767326003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10604013074716863178217335 15906019612075294767326003)
    ·
      refine ⟨23859029418112942150989005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15906019612075294767326003 23859029418112942150989005)
      ·
        refine ⟨8947136031792353306620877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23859029418112942150989005 8947136031792353306620877)
        ·
          refine ⟨3355176011922132489982829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8947136031792353306620877 3355176011922132489982829)
          ·
            refine ⟨1258191004470799683743561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3355176011922132489982829 1258191004470799683743561)
            ·
              refine ⟨943643253353099762807671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1258191004470799683743561 943643253353099762807671)
              ·
                refine ⟨1415464880029649644211507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 943643253353099762807671 1415464880029649644211507)
                ·
                  refine ⟨2123197320044474466317261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1415464880029649644211507 2123197320044474466317261)
                  ·
                    refine ⟨796198995016677924868973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2123197320044474466317261 796198995016677924868973)
                    ·
                      refine ⟨298574623131254221825865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 796198995016677924868973 298574623131254221825865)
                      ·
                        rfl

theorem cell23_581472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_581472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581472 prefixEnd_581472 := by exact prefixLift 581472
  have htrace : WordTrace (prefixWord ++ tailWord_581472) baseStart_581472 baseEnd_581472 := by
    simpa [prefixWord, tailWord_581472, baseEnd_581472] using wordTrace_append hprefix tailTrace_581472
  have hstable : (prefixWord ++ tailWord_581472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581472).length < 2 ^ (prefixWord ++ tailWord_581472).sum := by decide
  have hdescent : baseEnd_581472 < baseStart_581472 := by decide
  rcases family_descends (prefixWord ++ tailWord_581472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581488 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 3, 8]
def baseStart_581488 : Nat := 118140960795 + 581488 * 2 ^ 59
def prefixEnd_581488 : Nat := 4983230072969 + 3 ^ 40 * 581488 * 2
def baseEnd_581488 : Nat := 99527612940575386408597

theorem tailTrace_581488 : CollatzResearch.WordTrace tailWord_581488 prefixEnd_581488 99527612940575386408597 := by
  unfold tailWord_581488
  simp only [CollatzResearch.WordTrace]
  refine ⟨10604304858687880544508559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14139073144917174059344745 10604304858687880544508559)
  ·
    refine ⟨15906457288031820816762839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10604304858687880544508559 15906457288031820816762839)
    ·
      refine ⟨23859685932047731225144259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15906457288031820816762839 23859685932047731225144259)
      ·
        refine ⟨35789528898071596837716389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23859685932047731225144259 35789528898071596837716389)
        ·
          refine ⟨6710536668388424407071823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35789528898071596837716389 6710536668388424407071823)
          ·
            refine ⟨10065805002582636610607735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6710536668388424407071823 10065805002582636610607735)
            ·
              refine ⟨15098707503873954915911603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10065805002582636610607735 15098707503873954915911603)
              ·
                refine ⟨22648061255810932373867405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15098707503873954915911603 22648061255810932373867405)
                ·
                  refine ⟨8493022970929099640200277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22648061255810932373867405 8493022970929099640200277)
                  ·
                    refine ⟨99527612940575386408597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8493022970929099640200277 99527612940575386408597)
                    ·
                      rfl

theorem cell23_581488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 8].length) (baseStart_581488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581488 prefixEnd_581488 := by exact prefixLift 581488
  have htrace : WordTrace (prefixWord ++ tailWord_581488) baseStart_581488 baseEnd_581488 := by
    simpa [prefixWord, tailWord_581488, baseEnd_581488] using wordTrace_append hprefix tailTrace_581488
  have hstable : (prefixWord ++ tailWord_581488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581488).length < 2 ^ (prefixWord ++ tailWord_581488).sum := by decide
  have hdescent : baseEnd_581488 < baseStart_581488 := by decide
  rcases family_descends (prefixWord ++ tailWord_581488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581522 : List Nat := [3, 2, 3, 2, 1, 1, 2, 1, 2, 6]
def baseStart_581522 : Nat := 118140960795 + 581522 * 2 ^ 59
def prefixEnd_581522 : Nat := 4983230072969 + 3 ^ 40 * 581522 * 2
def baseEnd_581522 : Nat := 99533432387993008733545

theorem tailTrace_581522 : CollatzResearch.WordTrace tailWord_581522 prefixEnd_581522 99533432387993008733545 := by
  unfold tailWord_581522
  simp only [CollatzResearch.WordTrace]
  refine ⟨5302462449813146223938705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14139899866168389930503213 5302462449813146223938705)
  ·
    refine ⟨3976846837359859667954029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5302462449813146223938705 3976846837359859667954029)
    ·
      refine ⟨1491317564009947375482761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3976846837359859667954029 1491317564009947375482761)
      ·
        refine ⟨1118488173007460531612071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1491317564009947375482761 1118488173007460531612071)
        ·
          refine ⟨1677732259511190797418107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1118488173007460531612071 1677732259511190797418107)
          ·
            refine ⟨2516598389266786196127161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1677732259511190797418107 2516598389266786196127161)
            ·
              refine ⟨1887448791950089647095371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2516598389266786196127161 1887448791950089647095371)
              ·
                refine ⟨2831173187925134470643057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1887448791950089647095371 2831173187925134470643057)
                ·
                  refine ⟨2123379890943850852982293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2831173187925134470643057 2123379890943850852982293)
                  ·
                    refine ⟨99533432387993008733545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2123379890943850852982293 99533432387993008733545)
                    ·
                      rfl

theorem cell23_581522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_581522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581522 prefixEnd_581522 := by exact prefixLift 581522
  have htrace : WordTrace (prefixWord ++ tailWord_581522) baseStart_581522 baseEnd_581522 := by
    simpa [prefixWord, tailWord_581522, baseEnd_581522] using wordTrace_append hprefix tailTrace_581522
  have hstable : (prefixWord ++ tailWord_581522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581522).length < 2 ^ (prefixWord ++ tailWord_581522).sum := by decide
  have hdescent : baseEnd_581522 < baseStart_581522 := by decide
  rcases family_descends (prefixWord ++ tailWord_581522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581525 : List Nat := [1, 3, 2, 1, 1, 3, 1, 3, 2, 2, 4]
def baseStart_581525 : Nat := 118140960795 + 581525 * 2 ^ 59
def prefixEnd_581525 : Nat := 4983230072969 + 3 ^ 40 * 581525 * 2
def baseEnd_581525 : Nat := 298601837605942514463121

theorem tailTrace_581525 : CollatzResearch.WordTrace tailWord_581525 prefixEnd_581525 298601837605942514463121 := by
  unfold tailWord_581525
  simp only [CollatzResearch.WordTrace]
  refine ⟨21209959218241716408114029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14139972812161144272076019 21209959218241716408114029)
  ·
    refine ⟨7953734706840643653042761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21209959218241716408114029 7953734706840643653042761)
    ·
      refine ⟨5965301030130482739782071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7953734706840643653042761 5965301030130482739782071)
      ·
        refine ⟨8947951545195724109673107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5965301030130482739782071 8947951545195724109673107)
        ·
          refine ⟨13421927317793586164509661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8947951545195724109673107 13421927317793586164509661)
          ·
            refine ⟨5033222744172594811691123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13421927317793586164509661 5033222744172594811691123)
            ·
              refine ⟨7549834116258892217536685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5033222744172594811691123 7549834116258892217536685)
              ·
                refine ⟨2831187793597084581576257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7549834116258892217536685 2831187793597084581576257)
                ·
                  refine ⟨2123390845197813436182193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2831187793597084581576257 2123390845197813436182193)
                  ·
                    refine ⟨1592543133898360077136645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2123390845197813436182193 1592543133898360077136645)
                    ·
                      refine ⟨298601837605942514463121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1592543133898360077136645 298601837605942514463121)
                      ·
                        rfl

theorem cell23_581525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_581525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581525 prefixEnd_581525 := by exact prefixLift 581525
  have htrace : WordTrace (prefixWord ++ tailWord_581525) baseStart_581525 baseEnd_581525 := by
    simpa [prefixWord, tailWord_581525, baseEnd_581525] using wordTrace_append hprefix tailTrace_581525
  have hstable : (prefixWord ++ tailWord_581525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581525).length < 2 ^ (prefixWord ++ tailWord_581525).sum := by decide
  have hdescent : baseEnd_581525 < baseStart_581525 := by decide
  rcases family_descends (prefixWord ++ tailWord_581525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581529 : List Nat := [1, 2, 1, 2, 1, 3, 2, 5, 2, 2, 2]
def baseStart_581529 : Nat := 118140960795 + 581529 * 2 ^ 59
def prefixEnd_581529 : Nat := 4983230072969 + 3 ^ 40 * 581529 * 2
def baseEnd_581529 : Nat := 298603891528560498813103

theorem tailTrace_581529 : CollatzResearch.WordTrace tailWord_581529 prefixEnd_581529 298603891528560498813103 := by
  unfold tailWord_581529
  simp only [CollatzResearch.WordTrace]
  refine ⟨21210105110227225091259641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14140070073484816727506427 21210105110227225091259641)
  ·
    refine ⟨15907578832670418818444731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21210105110227225091259641 15907578832670418818444731)
    ·
      refine ⟨23861368249005628227667097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15907578832670418818444731 23861368249005628227667097)
      ·
        refine ⟨17896026186754221170750323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23861368249005628227667097 17896026186754221170750323)
        ·
          refine ⟨26844039280131331756125485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17896026186754221170750323 26844039280131331756125485)
          ·
            refine ⟨10066514730049249408547057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26844039280131331756125485 10066514730049249408547057)
            ·
              refine ⟨7549886047536937056410293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10066514730049249408547057 7549886047536937056410293)
              ·
                refine ⟨707801816956587849038465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7549886047536937056410293 707801816956587849038465)
                ·
                  refine ⟨530851362717440886778849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 707801816956587849038465 530851362717440886778849)
                  ·
                    refine ⟨398138522038080665084137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 530851362717440886778849 398138522038080665084137)
                    ·
                      refine ⟨298603891528560498813103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 398138522038080665084137 298603891528560498813103)
                      ·
                        rfl

theorem cell23_581529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 2, 2].length) (baseStart_581529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581529 prefixEnd_581529 := by exact prefixLift 581529
  have htrace : WordTrace (prefixWord ++ tailWord_581529) baseStart_581529 baseEnd_581529 := by
    simpa [prefixWord, tailWord_581529, baseEnd_581529] using wordTrace_append hprefix tailTrace_581529
  have hstable : (prefixWord ++ tailWord_581529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581529).length < 2 ^ (prefixWord ++ tailWord_581529).sum := by decide
  have hdescent : baseEnd_581529 < baseStart_581529 := by decide
  rcases family_descends (prefixWord ++ tailWord_581529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581545 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 4, 3, 3]
def baseStart_581545 : Nat := 118140960795 + 581545 * 2 ^ 59
def prefixEnd_581545 : Nat := 4983230072969 + 3 ^ 40 * 581545 * 2
def baseEnd_581545 : Nat := 298612107219032436213029

theorem tailTrace_581545 : CollatzResearch.WordTrace tailWord_581545 prefixEnd_581545 298612107219032436213029 := by
  unfold tailWord_581545
  simp only [CollatzResearch.WordTrace]
  refine ⟨21210688678169259823842089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14140459118779506549228059 21210688678169259823842089)
  ·
    refine ⟨15908016508626944867881567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21210688678169259823842089 15908016508626944867881567)
    ·
      refine ⟨23862024762940417301822351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15908016508626944867881567 23862024762940417301822351)
      ·
        refine ⟨35793037144410625952733527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23862024762940417301822351 35793037144410625952733527)
        ·
          refine ⟨53689555716615938929100291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35793037144410625952733527 53689555716615938929100291)
          ·
            refine ⟨80534333574923908393650437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53689555716615938929100291 80534333574923908393650437)
            ·
              refine ⟨15100187545298232823809457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80534333574923908393650437 15100187545298232823809457)
              ·
                refine ⟨11325140658973674617857093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15100187545298232823809457 11325140658973674617857093)
                ·
                  refine ⟨2123463873557563990848205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11325140658973674617857093 2123463873557563990848205)
                  ·
                    refine ⟨796298952584086496568077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2123463873557563990848205 796298952584086496568077)
                    ·
                      refine ⟨298612107219032436213029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 796298952584086496568077 298612107219032436213029)
                      ·
                        rfl

theorem cell23_581545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 3, 3].length) (baseStart_581545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581545 prefixEnd_581545 := by exact prefixLift 581545
  have htrace : WordTrace (prefixWord ++ tailWord_581545) baseStart_581545 baseEnd_581545 := by
    simpa [prefixWord, tailWord_581545, baseEnd_581545] using wordTrace_append hprefix tailTrace_581545
  have hstable : (prefixWord ++ tailWord_581545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581545).length < 2 ^ (prefixWord ++ tailWord_581545).sum := by decide
  have hdescent : baseEnd_581545 < baseStart_581545 := by decide
  rcases family_descends (prefixWord ++ tailWord_581545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581585 : List Nat := [1, 2, 2, 1, 2, 1, 2, 4, 1, 3, 4]
def baseStart_581585 : Nat := 118140960795 + 581585 * 2 ^ 59
def prefixEnd_581585 : Nat := 4983230072969 + 3 ^ 40 * 581585 * 2
def baseEnd_581585 : Nat := 298632646445212279712845

theorem tailTrace_581585 : CollatzResearch.WordTrace tailWord_581585 prefixEnd_581585 298632646445212279712845 := by
  unfold tailWord_581585
  simp only [CollatzResearch.WordTrace]
  refine ⟨21212147598024346655298209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14141431732016231103532139 21212147598024346655298209)
  ·
    refine ⟨15909110698518259991473657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21212147598024346655298209 15909110698518259991473657)
    ·
      refine ⟨11931833023888694993605243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15909110698518259991473657 11931833023888694993605243)
      ·
        refine ⟨17897749535833042490407865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11931833023888694993605243 17897749535833042490407865)
        ·
          refine ⟨13423312151874781867805899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17897749535833042490407865 13423312151874781867805899)
          ·
            refine ⟨20134968227812172801708849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13423312151874781867805899 20134968227812172801708849)
            ·
              refine ⟨15101226170859129601281637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20134968227812172801708849 15101226170859129601281637)
              ·
                refine ⟨2831479907036086800240307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15101226170859129601281637 2831479907036086800240307)
                ·
                  refine ⟨4247219860554130200360461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2831479907036086800240307 4247219860554130200360461)
                  ·
                    refine ⟨1592707447707798825135173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4247219860554130200360461 1592707447707798825135173)
                    ·
                      refine ⟨298632646445212279712845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1592707447707798825135173 298632646445212279712845)
                      ·
                        rfl

theorem cell23_581585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_581585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581585 prefixEnd_581585 := by exact prefixLift 581585
  have htrace : WordTrace (prefixWord ++ tailWord_581585) baseStart_581585 baseEnd_581585 := by
    simpa [prefixWord, tailWord_581585, baseEnd_581585] using wordTrace_append hprefix tailTrace_581585
  have hstable : (prefixWord ++ tailWord_581585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581585).length < 2 ^ (prefixWord ++ tailWord_581585).sum := by decide
  have hdescent : baseEnd_581585 < baseStart_581585 := by decide
  rcases family_descends (prefixWord ++ tailWord_581585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581615 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 6]
def baseStart_581615 : Nat := 118140960795 + 581615 * 2 ^ 59
def prefixEnd_581615 : Nat := 4983230072969 + 3 ^ 40 * 581615 * 2
def baseEnd_581615 : Nat := 298648050864847162337707

theorem tailTrace_581615 : CollatzResearch.WordTrace tailWord_581615 prefixEnd_581615 298648050864847162337707 := by
  unfold tailWord_581615
  simp only [CollatzResearch.WordTrace]
  refine ⟨21213241787915661778890299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14142161191943774519260199 21213241787915661778890299)
  ·
    refine ⟨31819862681873492668335449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21213241787915661778890299 31819862681873492668335449)
    ·
      refine ⟨23864897011405119501251587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31819862681873492668335449 23864897011405119501251587)
      ·
        refine ⟨35797345517107679251877381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23864897011405119501251587 35797345517107679251877381)
        ·
          refine ⟨6712002284457689859727009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35797345517107679251877381 6712002284457689859727009)
          ·
            refine ⟨5034001713343267394795257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6712002284457689859727009 5034001713343267394795257)
            ·
              refine ⟨3775501285007450546096443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5034001713343267394795257 3775501285007450546096443)
              ·
                refine ⟨5663251927511175819144665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3775501285007450546096443 5663251927511175819144665)
                ·
                  refine ⟨4247438945633381864358499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5663251927511175819144665 4247438945633381864358499)
                  ·
                    refine ⟨6371158418450072796537749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4247438945633381864358499 6371158418450072796537749)
                    ·
                      refine ⟨298648050864847162337707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6371158418450072796537749 298648050864847162337707)
                      ·
                        rfl

theorem cell23_581615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 6].length) (baseStart_581615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581615 prefixEnd_581615 := by exact prefixLift 581615
  have htrace : WordTrace (prefixWord ++ tailWord_581615) baseStart_581615 baseEnd_581615 := by
    simpa [prefixWord, tailWord_581615, baseEnd_581615] using wordTrace_append hprefix tailTrace_581615
  have hstable : (prefixWord ++ tailWord_581615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581615).length < 2 ^ (prefixWord ++ tailWord_581615).sum := by decide
  have hdescent : baseEnd_581615 < baseStart_581615 := by decide
  rcases family_descends (prefixWord ++ tailWord_581615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581722 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4]
def baseStart_581722 : Nat := 118140960795 + 581722 * 2 ^ 59
def prefixEnd_581722 : Nat := 4983230072969 + 3 ^ 40 * 581722 * 2
def baseEnd_581722 : Nat := 298702993294878243699715

theorem tailTrace_581722 : CollatzResearch.WordTrace tailWord_581722 prefixEnd_581722 298702993294878243699715 := by
  unfold tailWord_581722
  simp only [CollatzResearch.WordTrace]
  refine ⟨5304286099632004763258855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14144762932352012702023613 5304286099632004763258855)
  ·
    refine ⟨7956429149448007144888283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5304286099632004763258855 7956429149448007144888283)
    ·
      refine ⟨11934643724172010717332425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7956429149448007144888283 11934643724172010717332425)
      ·
        refine ⟨8950982793129008037999319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11934643724172010717332425 8950982793129008037999319)
        ·
          refine ⟨13426474189693512056998979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8950982793129008037999319 13426474189693512056998979)
          ·
            refine ⟨20139711284540268085498469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13426474189693512056998979 20139711284540268085498469)
            ·
              refine ⟨3776195865851300266030963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20139711284540268085498469 3776195865851300266030963)
              ·
                refine ⟨5664293798776950399046445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3776195865851300266030963 5664293798776950399046445)
                ·
                  refine ⟨2124110174541356399642417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5664293798776950399046445 2124110174541356399642417)
                  ·
                    refine ⟨1593082630906017299731813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2124110174541356399642417 1593082630906017299731813)
                    ·
                      refine ⟨298702993294878243699715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1593082630906017299731813 298702993294878243699715)
                      ·
                        rfl

theorem cell23_581722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_581722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581722 prefixEnd_581722 := by exact prefixLift 581722
  have htrace : WordTrace (prefixWord ++ tailWord_581722) baseStart_581722 baseEnd_581722 := by
    simpa [prefixWord, tailWord_581722, baseEnd_581722] using wordTrace_append hprefix tailTrace_581722
  have hstable : (prefixWord ++ tailWord_581722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581722).length < 2 ^ (prefixWord ++ tailWord_581722).sum := by decide
  have hdescent : baseEnd_581722 < baseStart_581722 := by decide
  rcases family_descends (prefixWord ++ tailWord_581722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581743 : List Nat := [1, 1, 2, 1, 3, 6, 1, 1, 3, 2, 2]
def baseStart_581743 : Nat := 118140960795 + 581743 * 2 ^ 59
def prefixEnd_581743 : Nat := 4983230072969 + 3 ^ 40 * 581743 * 2
def baseEnd_581743 : Nat := 298713776388622661537119

theorem tailTrace_581743 : CollatzResearch.WordTrace tailWord_581743 prefixEnd_581743 298713776388622661537119 := by
  unfold tailWord_581743
  simp only [CollatzResearch.WordTrace]
  refine ⟨21217910331451939639549883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14145273554301293093033255 21217910331451939639549883)
  ·
    refine ⟨31826865497177909459324825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21217910331451939639549883 31826865497177909459324825)
    ·
      refine ⟨23870149122883432094493619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31826865497177909459324825 23870149122883432094493619)
      ·
        refine ⟨35805223684325148141740429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23870149122883432094493619 35805223684325148141740429)
        ·
          refine ⟨13426958881621930553152661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35805223684325148141740429 13426958881621930553152661)
          ·
            refine ⟨629388697576027994679031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13426958881621930553152661 629388697576027994679031)
            ·
              refine ⟨944083046364041992018547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 629388697576027994679031 944083046364041992018547)
              ·
                refine ⟨1416124569546062988027821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 944083046364041992018547 1416124569546062988027821)
                ·
                  refine ⟨531046713579773620510433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1416124569546062988027821 531046713579773620510433)
                  ·
                    refine ⟨398285035184830215382825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 531046713579773620510433 398285035184830215382825)
                    ·
                      refine ⟨298713776388622661537119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 398285035184830215382825 298713776388622661537119)
                      ·
                        rfl

theorem cell23_581743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 2, 2].length) (baseStart_581743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581743 prefixEnd_581743 := by exact prefixLift 581743
  have htrace : WordTrace (prefixWord ++ tailWord_581743) baseStart_581743 baseEnd_581743 := by
    simpa [prefixWord, tailWord_581743, baseEnd_581743] using wordTrace_append hprefix tailTrace_581743
  have hstable : (prefixWord ++ tailWord_581743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581743).length < 2 ^ (prefixWord ++ tailWord_581743).sum := by decide
  have hdescent : baseEnd_581743 < baseStart_581743 := by decide
  rcases family_descends (prefixWord ++ tailWord_581743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581753 : List Nat := [1, 2, 1, 3, 4, 3, 2, 1, 2, 4]
def baseStart_581753 : Nat := 118140960795 + 581753 * 2 ^ 59
def prefixEnd_581753 : Nat := 4983230072969 + 3 ^ 40 * 581753 * 2
def baseEnd_581753 : Nat := 99572970398389207470691

theorem tailTrace_581753 : CollatzResearch.WordTrace tailWord_581753 prefixEnd_581753 99572970398389207470691 := by
  unfold tailWord_581753
  simp only [CollatzResearch.WordTrace]
  refine ⟨21218275061415711347413913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14145516707610474231609275 21218275061415711347413913)
  ·
    refine ⟨15913706296061783510560435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21218275061415711347413913 15913706296061783510560435)
    ·
      refine ⟨23870559444092675265840653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15913706296061783510560435 23870559444092675265840653)
      ·
        refine ⟨8951459791534753224690245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23870559444092675265840653 8951459791534753224690245)
        ·
          refine ⟨1678398710912766229629421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8951459791534753224690245 1678398710912766229629421)
          ·
            refine ⟨629399516592287336111033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1678398710912766229629421 629399516592287336111033)
            ·
              refine ⟨472049637444215502083275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 629399516592287336111033 472049637444215502083275)
              ·
                refine ⟨708074456166323253124913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 472049637444215502083275 708074456166323253124913)
                ·
                  refine ⟨531055842124742439843685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 708074456166323253124913 531055842124742439843685)
                  ·
                    refine ⟨99572970398389207470691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 531055842124742439843685 99572970398389207470691)
                    ·
                      rfl

theorem cell23_581753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 2, 4].length) (baseStart_581753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581753 prefixEnd_581753 := by exact prefixLift 581753
  have htrace : WordTrace (prefixWord ++ tailWord_581753) baseStart_581753 baseEnd_581753 := by
    simpa [prefixWord, tailWord_581753, baseEnd_581753] using wordTrace_append hprefix tailTrace_581753
  have hstable : (prefixWord ++ tailWord_581753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581753).length < 2 ^ (prefixWord ++ tailWord_581753).sum := by decide
  have hdescent : baseEnd_581753 < baseStart_581753 := by decide
  rcases family_descends (prefixWord ++ tailWord_581753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581780 : List Nat := [2, 4, 2, 3, 2, 1, 1, 1, 1, 1, 5]
def baseStart_581780 : Nat := 118140960795 + 581780 * 2 ^ 59
def prefixEnd_581780 : Nat := 4983230072969 + 3 ^ 40 * 581780 * 2
def baseEnd_581780 : Nat := 298732775172839016774449

theorem tailTrace_581780 : CollatzResearch.WordTrace tailWord_581780 prefixEnd_581780 298732775172839016774449 := by
  unfold tailWord_581780
  simp only [CollatzResearch.WordTrace]
  refine ⟨10609629916158947479323397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14146173221545263305764529 10609629916158947479323397)
  ·
    refine ⟨1989305609279802652373137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10609629916158947479323397 1989305609279802652373137)
    ·
      refine ⟨1491979206959851989279853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1989305609279802652373137 1491979206959851989279853)
      ·
        refine ⟨559492202609944495979945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1491979206959851989279853 559492202609944495979945)
        ·
          refine ⟨419619151957458371984959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 559492202609944495979945 419619151957458371984959)
          ·
            refine ⟨629428727936187557977439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419619151957458371984959 629428727936187557977439)
            ·
              refine ⟨944143091904281336966159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 629428727936187557977439 944143091904281336966159)
              ·
                refine ⟨1416214637856422005449239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 944143091904281336966159 1416214637856422005449239)
                ·
                  refine ⟨2124321956784633008173859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1416214637856422005449239 2124321956784633008173859)
                  ·
                    refine ⟨3186482935176949512260789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2124321956784633008173859 3186482935176949512260789)
                    ·
                      refine ⟨298732775172839016774449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3186482935176949512260789 298732775172839016774449)
                      ·
                        rfl

theorem cell23_581780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_581780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581780 prefixEnd_581780 := by exact prefixLift 581780
  have htrace : WordTrace (prefixWord ++ tailWord_581780) baseStart_581780 baseEnd_581780 := by
    simpa [prefixWord, tailWord_581780, baseEnd_581780] using wordTrace_append hprefix tailTrace_581780
  have hstable : (prefixWord ++ tailWord_581780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581780).length < 2 ^ (prefixWord ++ tailWord_581780).sum := by decide
  have hdescent : baseEnd_581780 < baseStart_581780 := by decide
  rcases family_descends (prefixWord ++ tailWord_581780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581793 : List Nat := [1, 2, 3, 3, 1, 3, 2, 2, 2, 1, 3]
def baseStart_581793 : Nat := 118140960795 + 581793 * 2 ^ 59
def prefixEnd_581793 : Nat := 4983230072969 + 3 ^ 40 * 581793 * 2
def baseEnd_581793 : Nat := 298739450421347465911889

theorem tailTrace_581793 : CollatzResearch.WordTrace tailWord_581793 prefixEnd_581793 298739450421347465911889 := by
  unfold tailWord_581793
  simp only [CollatzResearch.WordTrace]
  refine ⟨21219733981270798178870033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14146489320847198785913355 21219733981270798178870033)
  ·
    refine ⟨15914800485953098634152525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21219733981270798178870033 15914800485953098634152525)
    ·
      refine ⟨5968050182232411987807197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15914800485953098634152525 5968050182232411987807197)
      ·
        refine ⟨2238018818337154495427699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5968050182232411987807197 2238018818337154495427699)
        ·
          refine ⟨3357028227505731743141549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2238018818337154495427699 3357028227505731743141549)
          ·
            refine ⟨1258885585314649403678081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3357028227505731743141549 1258885585314649403678081)
            ·
              refine ⟨944164188985987052758561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1258885585314649403678081 944164188985987052758561)
              ·
                refine ⟨708123141739490289568921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 944164188985987052758561 708123141739490289568921)
                ·
                  refine ⟨531092356304617717176691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 708123141739490289568921 531092356304617717176691)
                  ·
                    refine ⟨796638534456926575765037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 531092356304617717176691 796638534456926575765037)
                    ·
                      refine ⟨298739450421347465911889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 796638534456926575765037 298739450421347465911889)
                      ·
                        rfl

theorem cell23_581793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_581793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581793 prefixEnd_581793 := by exact prefixLift 581793
  have htrace : WordTrace (prefixWord ++ tailWord_581793) baseStart_581793 baseEnd_581793 := by
    simpa [prefixWord, tailWord_581793, baseEnd_581793] using wordTrace_append hprefix tailTrace_581793
  have hstable : (prefixWord ++ tailWord_581793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581793).length < 2 ^ (prefixWord ++ tailWord_581793).sum := by decide
  have hdescent : baseEnd_581793 < baseStart_581793 := by decide
  rcases family_descends (prefixWord ++ tailWord_581793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581794 : List Nat := [3, 3, 1, 3, 1, 3, 2, 2, 1, 2, 2]
def baseStart_581794 : Nat := 118140960795 + 581794 * 2 ^ 59
def prefixEnd_581794 : Nat := 4983230072969 + 3 ^ 40 * 581794 * 2
def baseEnd_581794 : Nat := 298739963902001961999385

theorem tailTrace_581794 : CollatzResearch.WordTrace tailWord_581794 prefixEnd_581794 298739963902001961999385 := by
  unfold tailWord_581794
  simp only [CollatzResearch.WordTrace]
  refine ⟨5304942613566793837414109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14146513636178116899770957 5304942613566793837414109)
  ·
    refine ⟨1989353480087547689030291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5304942613566793837414109 1989353480087547689030291)
    ·
      refine ⟨2984030220131321533545437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1989353480087547689030291 2984030220131321533545437)
      ·
        refine ⟨1119011332549245575079539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2984030220131321533545437 1119011332549245575079539)
        ·
          refine ⟨1678516998823868362619309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1119011332549245575079539 1678516998823868362619309)
          ·
            refine ⟨629443874558950635982241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1678516998823868362619309 629443874558950635982241)
            ·
              refine ⟨472082905919212976986681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 629443874558950635982241 472082905919212976986681)
              ·
                refine ⟨354062179439409732740011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 472082905919212976986681 354062179439409732740011)
                ·
                  refine ⟨531093269159114599110017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 354062179439409732740011 531093269159114599110017)
                  ·
                    refine ⟨398319951869335949332513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 531093269159114599110017 398319951869335949332513)
                    ·
                      refine ⟨298739963902001961999385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 398319951869335949332513 298739963902001961999385)
                      ·
                        rfl

theorem cell23_581794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_581794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581794 prefixEnd_581794 := by exact prefixLift 581794
  have htrace : WordTrace (prefixWord ++ tailWord_581794) baseStart_581794 baseEnd_581794 := by
    simpa [prefixWord, tailWord_581794, baseEnd_581794] using wordTrace_append hprefix tailTrace_581794
  have hstable : (prefixWord ++ tailWord_581794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581794).length < 2 ^ (prefixWord ++ tailWord_581794).sum := by decide
  have hdescent : baseEnd_581794 < baseStart_581794 := by decide
  rcases family_descends (prefixWord ++ tailWord_581794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581816 : List Nat := [2, 1, 2, 1, 2, 1, 6, 1, 1, 4, 2]
def baseStart_581816 : Nat := 118140960795 + 581816 * 2 ^ 59
def prefixEnd_581816 : Nat := 4983230072969 + 3 ^ 40 * 581816 * 2
def baseEnd_581816 : Nat := 298751260476400875924283

theorem tailTrace_581816 : CollatzResearch.WordTrace tailWord_581816 prefixEnd_581816 298751260476400875924283 := by
  unfold tailWord_581816
  simp only [CollatzResearch.WordTrace]
  refine ⟨10610286430093736553478651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14147048573458315404638201 10610286430093736553478651)
  ·
    refine ⟨15915429645140604830217977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10610286430093736553478651 15915429645140604830217977)
    ·
      refine ⟨11936572233855453622663483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15915429645140604830217977 11936572233855453622663483)
      ·
        refine ⟨17904858350783180433995225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11936572233855453622663483 17904858350783180433995225)
        ·
          refine ⟨13428643763087385325496419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17904858350783180433995225 13428643763087385325496419)
          ·
            refine ⟨20142965644631077988244629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13428643763087385325496419 20142965644631077988244629)
            ·
              refine ⟨944201514592081780698967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20142965644631077988244629 944201514592081780698967)
              ·
                refine ⟨1416302271888122671048451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 944201514592081780698967 1416302271888122671048451)
                ·
                  refine ⟨2124453407832184006572677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1416302271888122671048451 2124453407832184006572677)
                  ·
                    refine ⟨398335013968534501232377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2124453407832184006572677 398335013968534501232377)
                    ·
                      refine ⟨298751260476400875924283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 398335013968534501232377 298751260476400875924283)
                      ·
                        rfl

theorem cell23_581816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 1, 4, 2].length) (baseStart_581816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581816 prefixEnd_581816 := by exact prefixLift 581816
  have htrace : WordTrace (prefixWord ++ tailWord_581816) baseStart_581816 baseEnd_581816 := by
    simpa [prefixWord, tailWord_581816, baseEnd_581816] using wordTrace_append hprefix tailTrace_581816
  have hstable : (prefixWord ++ tailWord_581816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581816).length < 2 ^ (prefixWord ++ tailWord_581816).sum := by decide
  have hdescent : baseEnd_581816 < baseStart_581816 := by decide
  rcases family_descends (prefixWord ++ tailWord_581816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581832 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 1, 2, 7]
def baseStart_581832 : Nat := 118140960795 + 581832 * 2 ^ 59
def prefixEnd_581832 : Nat := 4983230072969 + 3 ^ 40 * 581832 * 2
def baseEnd_581832 : Nat := 298759476166872813324209

theorem tailTrace_581832 : CollatzResearch.WordTrace tailWord_581832 prefixEnd_581832 298759476166872813324209 := by
  unfold tailWord_581832
  simp only [CollatzResearch.WordTrace]
  refine ⟨10610578214064753919769875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14147437618753005226359833 10610578214064753919769875)
  ·
    refine ⟨15915867321097130879654813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10610578214064753919769875 15915867321097130879654813)
    ·
      refine ⟨5968450245411424079870555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15915867321097130879654813 5968450245411424079870555)
      ·
        refine ⟨8952675368117136119805833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5968450245411424079870555 8952675368117136119805833)
        ·
          refine ⟨6714506526087852089854375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8952675368117136119805833 6714506526087852089854375)
          ·
            refine ⟨10071759789131778134781563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6714506526087852089854375 10071759789131778134781563)
            ·
              refine ⟨15107639683697667202172345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10071759789131778134781563 15107639683697667202172345)
              ·
                refine ⟨11330729762773250401629259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15107639683697667202172345 11330729762773250401629259)
                ·
                  refine ⟨16996094644159875602443889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11330729762773250401629259 16996094644159875602443889)
                  ·
                    refine ⟨12747070983119906701832917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16996094644159875602443889 12747070983119906701832917)
                    ·
                      refine ⟨298759476166872813324209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 12747070983119906701832917 298759476166872813324209)
                      ·
                        rfl

theorem cell23_581832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_581832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581832 prefixEnd_581832 := by exact prefixLift 581832
  have htrace : WordTrace (prefixWord ++ tailWord_581832) baseStart_581832 baseEnd_581832 := by
    simpa [prefixWord, tailWord_581832, baseEnd_581832] using wordTrace_append hprefix tailTrace_581832
  have hstable : (prefixWord ++ tailWord_581832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581832).length < 2 ^ (prefixWord ++ tailWord_581832).sum := by decide
  have hdescent : baseEnd_581832 < baseStart_581832 := by decide
  rcases family_descends (prefixWord ++ tailWord_581832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581849 : List Nat := [1, 2, 1, 2, 3, 1, 3, 2, 2, 3, 3]
def baseStart_581849 : Nat := 118140960795 + 581849 * 2 ^ 59
def prefixEnd_581849 : Nat := 4983230072969 + 3 ^ 40 * 581849 * 2
def baseEnd_581849 : Nat := 298768205337999246811631

theorem tailTrace_581849 : CollatzResearch.WordTrace tailWord_581849 prefixEnd_581849 298768205337999246811631 := by
  unfold tailWord_581849
  simp only [CollatzResearch.WordTrace]
  refine ⟨21221776469067919742908601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14147850979378613161939067 21221776469067919742908601)
  ·
    refine ⟨15916332351800939807181451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21221776469067919742908601 15916332351800939807181451)
    ·
      refine ⟨23874498527701409710772177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15916332351800939807181451 23874498527701409710772177)
      ·
        refine ⟨17905873895776057283079133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23874498527701409710772177 17905873895776057283079133)
        ·
          refine ⟨6714702710916021481154675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17905873895776057283079133 6714702710916021481154675)
          ·
            refine ⟨10072054066374032221732013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6714702710916021481154675 10072054066374032221732013)
            ·
              refine ⟨3777020274890262083149505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10072054066374032221732013 3777020274890262083149505)
              ·
                refine ⟨2832765206167696562362129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3777020274890262083149505 2832765206167696562362129)
                ·
                  refine ⟨2124573904625772421771597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2832765206167696562362129 2124573904625772421771597)
                  ·
                    refine ⟨796715214234664658164349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2124573904625772421771597 796715214234664658164349)
                    ·
                      refine ⟨298768205337999246811631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 796715214234664658164349 298768205337999246811631)
                      ·
                        rfl

theorem cell23_581849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 3, 3].length) (baseStart_581849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581849 prefixEnd_581849 := by exact prefixLift 581849
  have htrace : WordTrace (prefixWord ++ tailWord_581849) baseStart_581849 baseEnd_581849 := by
    simpa [prefixWord, tailWord_581849, baseEnd_581849] using wordTrace_append hprefix tailTrace_581849
  have hstable : (prefixWord ++ tailWord_581849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581849).length < 2 ^ (prefixWord ++ tailWord_581849).sum := by decide
  have hdescent : baseEnd_581849 < baseStart_581849 := by decide
  rcases family_descends (prefixWord ++ tailWord_581849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581886 : List Nat := [4, 2, 2, 1, 1, 1, 2, 3, 2, 5]
def baseStart_581886 : Nat := 118140960795 + 581886 * 2 ^ 59
def prefixEnd_581886 : Nat := 4983230072969 + 3 ^ 40 * 581886 * 2
def baseEnd_581886 : Nat := 99595734707405200682987

theorem tailTrace_581886 : CollatzResearch.WordTrace tailWord_581886 prefixEnd_581886 99595734707405200682987 := by
  unfold tailWord_581886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2652890746241734382750689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14148750646622583374670341 2652890746241734382750689)
  ·
    refine ⟨1989668059681300787063017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2652890746241734382750689 1989668059681300787063017)
    ·
      refine ⟨1492251044760975590297263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1989668059681300787063017 1492251044760975590297263)
      ·
        refine ⟨2238376567141463385445895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1492251044760975590297263 2238376567141463385445895)
        ·
          refine ⟨3357564850712195078168843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2238376567141463385445895 3357564850712195078168843)
          ·
            refine ⟨5036347276068292617253265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3357564850712195078168843 5036347276068292617253265)
            ·
              refine ⟨3777260457051219462939949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5036347276068292617253265 3777260457051219462939949)
              ·
                refine ⟨1416472671394207298602481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3777260457051219462939949 1416472671394207298602481)
                ·
                  refine ⟨1062354503545655473951861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1416472671394207298602481 1062354503545655473951861)
                  ·
                    refine ⟨99595734707405200682987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1062354503545655473951861 99595734707405200682987)
                    ·
                      rfl

theorem cell23_581886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_581886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581886 prefixEnd_581886 := by exact prefixLift 581886
  have htrace : WordTrace (prefixWord ++ tailWord_581886) baseStart_581886 baseEnd_581886 := by
    simpa [prefixWord, tailWord_581886, baseEnd_581886] using wordTrace_append hprefix tailTrace_581886
  have hstable : (prefixWord ++ tailWord_581886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581886).length < 2 ^ (prefixWord ++ tailWord_581886).sum := by decide
  have hdescent : baseEnd_581886 < baseStart_581886 := by decide
  rcases family_descends (prefixWord ++ tailWord_581886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581889 : List Nat := [1, 2, 4, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_581889 : Nat := 118140960795 + 581889 * 2 ^ 59
def prefixEnd_581889 : Nat := 4983230072969 + 3 ^ 40 * 581889 * 2
def baseEnd_581889 : Nat := 298788744564179090311447

theorem tailTrace_581889 : CollatzResearch.WordTrace tailWord_581889 prefixEnd_581889 298788744564179090311447 := by
  unfold tailWord_581889
  simp only [CollatzResearch.WordTrace]
  refine ⟨21223235388923006574364721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14148823592615337716243147 21223235388923006574364721)
  ·
    refine ⟨15917426541692254930773541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21223235388923006574364721 15917426541692254930773541)
    ·
      refine ⟨2984517476567297799520039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15917426541692254930773541 2984517476567297799520039)
      ·
        refine ⟨4476776214850946699280059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2984517476567297799520039 4476776214850946699280059)
        ·
          refine ⟨6715164322276420048920089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4476776214850946699280059 6715164322276420048920089)
          ·
            refine ⟨5036373241707315036690067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6715164322276420048920089 5036373241707315036690067)
            ·
              refine ⟨7554559862560972555035101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5036373241707315036690067 7554559862560972555035101)
              ·
                refine ⟨2832959948460364708138163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7554559862560972555035101 2832959948460364708138163)
                ·
                  refine ⟨4249439922690547062207245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2832959948460364708138163 4249439922690547062207245)
                  ·
                    refine ⟨1593539971008955148327717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4249439922690547062207245 1593539971008955148327717)
                    ·
                      refine ⟨298788744564179090311447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1593539971008955148327717 298788744564179090311447)
                      ·
                        rfl

theorem cell23_581889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_581889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581889 prefixEnd_581889 := by exact prefixLift 581889
  have htrace : WordTrace (prefixWord ++ tailWord_581889) baseStart_581889 baseEnd_581889 := by
    simpa [prefixWord, tailWord_581889, baseEnd_581889] using wordTrace_append hprefix tailTrace_581889
  have hstable : (prefixWord ++ tailWord_581889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581889).length < 2 ^ (prefixWord ++ tailWord_581889).sum := by decide
  have hdescent : baseEnd_581889 < baseStart_581889 := by decide
  rcases family_descends (prefixWord ++ tailWord_581889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581890 : List Nat := [3, 4, 1, 1, 2, 3, 1, 3, 5]
def baseStart_581890 : Nat := 118140960795 + 581890 * 2 ^ 59
def prefixEnd_581890 : Nat := 4983230072969 + 3 ^ 40 * 581890 * 2
def baseEnd_581890 : Nat := 33198806449425954044327

theorem tailTrace_581890 : CollatzResearch.WordTrace tailWord_581890 prefixEnd_581890 33198806449425954044327 := by
  unfold tailWord_581890
  simp only [CollatzResearch.WordTrace]
  refine ⟨5305817965479845936287781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14148847907946255830100749 5305817965479845936287781)
  ·
    refine ⟨994840868527471113053959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5305817965479845936287781 994840868527471113053959)
    ·
      refine ⟨1492261302791206669580939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 994840868527471113053959 1492261302791206669580939)
      ·
        refine ⟨2238391954186810004371409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1492261302791206669580939 2238391954186810004371409)
        ·
          refine ⟨1678793965640107503278557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2238391954186810004371409 1678793965640107503278557)
          ·
            refine ⟨629547737115040313729459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1678793965640107503278557 629547737115040313729459)
            ·
              refine ⟨944321605672560470594189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 629547737115040313729459 944321605672560470594189)
              ·
                refine ⟨354120602127210176472821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 944321605672560470594189 354120602127210176472821)
                ·
                  refine ⟨33198806449425954044327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 354120602127210176472821 33198806449425954044327)
                  ·
                    rfl

theorem cell23_581890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_581890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581890 prefixEnd_581890 := by exact prefixLift 581890
  have htrace : WordTrace (prefixWord ++ tailWord_581890) baseStart_581890 baseEnd_581890 := by
    simpa [prefixWord, tailWord_581890, baseEnd_581890] using wordTrace_append hprefix tailTrace_581890
  have hstable : (prefixWord ++ tailWord_581890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581890).length < 2 ^ (prefixWord ++ tailWord_581890).sum := by decide
  have hdescent : baseEnd_581890 < baseStart_581890 := by decide
  rcases family_descends (prefixWord ++ tailWord_581890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_581999 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 5]
def baseStart_581999 : Nat := 118140960795 + 581999 * 2 ^ 59
def prefixEnd_581999 : Nat := 4983230072969 + 3 ^ 40 * 581999 * 2
def baseEnd_581999 : Nat := 298845227436173659935941

theorem tailTrace_581999 : CollatzResearch.WordTrace tailWord_581999 prefixEnd_581999 298845227436173659935941 := by
  unfold tailWord_581999
  simp only [CollatzResearch.WordTrace]
  refine ⟨21227247418524495360869051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14151498279016330240579367 21227247418524495360869051)
  ·
    refine ⟨31840871127786743041303577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21227247418524495360869051 31840871127786743041303577)
    ·
      refine ⟨23880653345840057280977683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31840871127786743041303577 23880653345840057280977683)
      ·
        refine ⟨35820980018760085921466525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23880653345840057280977683 35820980018760085921466525)
        ·
          refine ⟨13432867507035032220549947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35820980018760085921466525 13432867507035032220549947)
          ·
            refine ⟨20149301260552548330824921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13432867507035032220549947 20149301260552548330824921)
            ·
              refine ⟨15111975945414411248118691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20149301260552548330824921 15111975945414411248118691)
              ·
                refine ⟨22667963918121616872178037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15111975945414411248118691 22667963918121616872178037)
                ·
                  refine ⟨2125121617323901581766691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22667963918121616872178037 2125121617323901581766691)
                  ·
                    refine ⟨3187682425985852372650037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2125121617323901581766691 3187682425985852372650037)
                    ·
                      refine ⟨298845227436173659935941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3187682425985852372650037 298845227436173659935941)
                      ·
                        rfl

theorem cell23_581999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 5].length) (baseStart_581999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_581999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_581999 prefixEnd_581999 := by exact prefixLift 581999
  have htrace : WordTrace (prefixWord ++ tailWord_581999) baseStart_581999 baseEnd_581999 := by
    simpa [prefixWord, tailWord_581999, baseEnd_581999] using wordTrace_append hprefix tailTrace_581999
  have hstable : (prefixWord ++ tailWord_581999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_581999).length < 2 ^ (prefixWord ++ tailWord_581999).sum := by decide
  have hdescent : baseEnd_581999 < baseStart_581999 := by decide
  rcases family_descends (prefixWord ++ tailWord_581999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582000 : List Nat := [2, 1, 1, 1, 4, 5, 1, 1, 2, 3, 2]
def baseStart_582000 : Nat := 118140960795 + 582000 * 2 ^ 59
def prefixEnd_582000 : Nat := 4983230072969 + 3 ^ 40 * 582000 * 2
def baseEnd_582000 : Nat := 298845740916828156023437

theorem tailTrace_582000 : CollatzResearch.WordTrace tailWord_582000 prefixEnd_582000 298845740916828156023437 := by
  unfold tailWord_582000
  simp only [CollatzResearch.WordTrace]
  refine ⟨10613641945760436265827727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14151522594347248354436969 10613641945760436265827727)
  ·
    refine ⟨15920462918640654398741591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10613641945760436265827727 15920462918640654398741591)
    ·
      refine ⟨23880694377960981598112387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15920462918640654398741591 23880694377960981598112387)
      ·
        refine ⟨35821041566941472397168581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23880694377960981598112387 35821041566941472397168581)
        ·
          refine ⟨6716445293801526074469109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35821041566941472397168581 6716445293801526074469109)
          ·
            refine ⟨629666746293893069481479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6716445293801526074469109 629666746293893069481479)
            ·
              refine ⟨944500119440839604222219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 629666746293893069481479 944500119440839604222219)
              ·
                refine ⟨1416750179161259406333329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 944500119440839604222219 1416750179161259406333329)
                ·
                  refine ⟨1062562634370944554749997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1416750179161259406333329 1062562634370944554749997)
                  ·
                    refine ⟨398460987889104208031249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1062562634370944554749997 398460987889104208031249)
                    ·
                      refine ⟨298845740916828156023437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 398460987889104208031249 298845740916828156023437)
                      ·
                        rfl

theorem cell23_582000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 2, 3, 2].length) (baseStart_582000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582000 prefixEnd_582000 := by exact prefixLift 582000
  have htrace : WordTrace (prefixWord ++ tailWord_582000) baseStart_582000 baseEnd_582000 := by
    simpa [prefixWord, tailWord_582000, baseEnd_582000] using wordTrace_append hprefix tailTrace_582000
  have hstable : (prefixWord ++ tailWord_582000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582000).length < 2 ^ (prefixWord ++ tailWord_582000).sum := by decide
  have hdescent : baseEnd_582000 < baseStart_582000 := by decide
  rcases family_descends (prefixWord ++ tailWord_582000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582009 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 3, 1, 6]
def baseStart_582009 : Nat := 118140960795 + 582009 * 2 ^ 59
def prefixEnd_582009 : Nat := 4983230072969 + 3 ^ 40 * 582009 * 2
def baseEnd_582009 : Nat := 298850362242718620810895

theorem tailTrace_582009 : CollatzResearch.WordTrace tailWord_582009 prefixEnd_582009 298850362242718620810895 := by
  unfold tailWord_582009
  simp only [CollatzResearch.WordTrace]
  refine ⟨21227612148488267068733081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14151741432325511379155387 21227612148488267068733081)
  ·
    refine ⟨15920709111366200301549811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21227612148488267068733081 15920709111366200301549811)
    ·
      refine ⟨23881063667049300452324717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15920709111366200301549811 23881063667049300452324717)
      ·
        refine ⟨8955398875143487669621769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23881063667049300452324717 8955398875143487669621769)
        ·
          refine ⟨6716549156357615752216327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8955398875143487669621769 6716549156357615752216327)
          ·
            refine ⟨10074823734536423628324491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6716549156357615752216327 10074823734536423628324491)
            ·
              refine ⟨15112235601804635442486737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10074823734536423628324491 15112235601804635442486737)
              ·
                refine ⟨11334176701353476581865053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15112235601804635442486737 11334176701353476581865053)
                ·
                  refine ⟨4250316263007553718199395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11334176701353476581865053 4250316263007553718199395)
                  ·
                    refine ⟨6375474394511330577299093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4250316263007553718199395 6375474394511330577299093)
                    ·
                      refine ⟨298850362242718620810895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6375474394511330577299093 298850362242718620810895)
                      ·
                        rfl

theorem cell23_582009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_582009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582009 prefixEnd_582009 := by exact prefixLift 582009
  have htrace : WordTrace (prefixWord ++ tailWord_582009) baseStart_582009 baseEnd_582009 := by
    simpa [prefixWord, tailWord_582009, baseEnd_582009] using wordTrace_append hprefix tailTrace_582009
  have hstable : (prefixWord ++ tailWord_582009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582009).length < 2 ^ (prefixWord ++ tailWord_582009).sum := by decide
  have hdescent : baseEnd_582009 < baseStart_582009 := by decide
  rcases family_descends (prefixWord ++ tailWord_582009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582013 : List Nat := [1, 4, 1, 1, 2, 4, 1, 3, 1, 1, 4]
def baseStart_582013 : Nat := 118140960795 + 582013 * 2 ^ 59
def prefixEnd_582013 : Nat := 4983230072969 + 3 ^ 40 * 582013 * 2
def baseEnd_582013 : Nat := 298852416165336605160877

theorem tailTrace_582013 : CollatzResearch.WordTrace tailWord_582013 prefixEnd_582013 298852416165336605160877 := by
  unfold tailWord_582013
  simp only [CollatzResearch.WordTrace]
  refine ⟨21227758040473775751878693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14151838693649183834585795 21227758040473775751878693)
  ·
    refine ⟨3980204632588832953477255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21227758040473775751878693 3980204632588832953477255)
    ·
      refine ⟨5970306948883249430215883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3980204632588832953477255 5970306948883249430215883)
      ·
        refine ⟨8955460423324874145323825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5970306948883249430215883 8955460423324874145323825)
        ·
          refine ⟨6716595317493655608992869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8955460423324874145323825 6716595317493655608992869)
          ·
            refine ⟨1259361622030060426686163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6716595317493655608992869 1259361622030060426686163)
            ·
              refine ⟨1889042433045090640029245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1259361622030060426686163 1889042433045090640029245)
              ·
                refine ⟨708390912391908990010967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1889042433045090640029245 708390912391908990010967)
                ·
                  refine ⟨1062586368587863485016451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 708390912391908990010967 1062586368587863485016451)
                  ·
                    refine ⟨1593879552881795227524677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1062586368587863485016451 1593879552881795227524677)
                    ·
                      refine ⟨298852416165336605160877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1593879552881795227524677 298852416165336605160877)
                      ·
                        rfl

theorem cell23_582013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_582013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582013 prefixEnd_582013 := by exact prefixLift 582013
  have htrace : WordTrace (prefixWord ++ tailWord_582013) baseStart_582013 baseEnd_582013 := by
    simpa [prefixWord, tailWord_582013, baseEnd_582013] using wordTrace_append hprefix tailTrace_582013
  have hstable : (prefixWord ++ tailWord_582013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582013).length < 2 ^ (prefixWord ++ tailWord_582013).sum := by decide
  have hdescent : baseEnd_582013 < baseStart_582013 := by decide
  rcases family_descends (prefixWord ++ tailWord_582013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582050 : List Nat := [3, 3, 1, 2, 1, 1, 4, 2, 1, 2, 3]
def baseStart_582050 : Nat := 118140960795 + 582050 * 2 ^ 59
def prefixEnd_582050 : Nat := 4983230072969 + 3 ^ 40 * 582050 * 2
def baseEnd_582050 : Nat := 298871414949552960398207

theorem tailTrace_582050 : CollatzResearch.WordTrace tailWord_582050 prefixEnd_582050 298871414949552960398207 := by
  unfold tailWord_582050
  simp only [CollatzResearch.WordTrace]
  refine ⟨5307276885334932767743901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14152738360893154047317069 5307276885334932767743901)
  ·
    refine ⟨1990228832000599787903963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5307276885334932767743901 1990228832000599787903963)
    ·
      refine ⟨2985343248000899681855945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1990228832000599787903963 2985343248000899681855945)
      ·
        refine ⟨2239007436000674761391959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2985343248000899681855945 2239007436000674761391959)
        ·
          refine ⟨3358511154001012142087939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2239007436000674761391959 3358511154001012142087939)
          ·
            refine ⟨5037766731001518213131909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3358511154001012142087939 5037766731001518213131909)
            ·
              refine ⟨944581262062784664962233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5037766731001518213131909 944581262062784664962233)
              ·
                refine ⟨708435946547088498721675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 944581262062784664962233 708435946547088498721675)
                ·
                  refine ⟨1062653919820632748082513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 708435946547088498721675 1062653919820632748082513)
                  ·
                    refine ⟨796990439865474561061885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1062653919820632748082513 796990439865474561061885)
                    ·
                      refine ⟨298871414949552960398207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 796990439865474561061885 298871414949552960398207)
                      ·
                        rfl

theorem cell23_582050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_582050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582050 prefixEnd_582050 := by exact prefixLift 582050
  have htrace : WordTrace (prefixWord ++ tailWord_582050) baseStart_582050 baseEnd_582050 := by
    simpa [prefixWord, tailWord_582050, baseEnd_582050] using wordTrace_append hprefix tailTrace_582050
  have hstable : (prefixWord ++ tailWord_582050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582050).length < 2 ^ (prefixWord ++ tailWord_582050).sum := by decide
  have hdescent : baseEnd_582050 < baseStart_582050 := by decide
  rcases family_descends (prefixWord ++ tailWord_582050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582058 : List Nat := [3, 1, 6, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_582058 : Nat := 118140960795 + 582058 * 2 ^ 59
def prefixEnd_582058 : Nat := 4983230072969 + 3 ^ 40 * 582058 * 2
def baseEnd_582058 : Nat := 298875522794788929098171

theorem tailTrace_582058 : CollatzResearch.WordTrace tailWord_582058 prefixEnd_582058 298875522794788929098171 := by
  unfold tailWord_582058
  simp only [CollatzResearch.WordTrace]
  refine ⟨5307349831327687109316707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14152932883540498958177885 5307349831327687109316707)
  ·
    refine ⟨7961024746991530663975061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5307349831327687109316707 7961024746991530663975061)
    ·
      refine ⟨373173035015227999873831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7961024746991530663975061 373173035015227999873831)
      ·
        refine ⟨559759552522841999810747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373173035015227999873831 559759552522841999810747)
        ·
          refine ⟨839639328784262999716121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 559759552522841999810747 839639328784262999716121)
          ·
            refine ⟨629729496588197249787091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 839639328784262999716121 629729496588197249787091)
            ·
              refine ⟨944594244882295874680637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 629729496588197249787091 944594244882295874680637)
              ·
                refine ⟨354222841830860953005239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 944594244882295874680637 354222841830860953005239)
                ·
                  refine ⟨531334262746291429507859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 354222841830860953005239 531334262746291429507859)
                  ·
                    refine ⟨797001394119437144261789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 531334262746291429507859 797001394119437144261789)
                    ·
                      refine ⟨298875522794788929098171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 797001394119437144261789 298875522794788929098171)
                      ·
                        rfl

theorem cell23_582058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_582058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582058 prefixEnd_582058 := by exact prefixLift 582058
  have htrace : WordTrace (prefixWord ++ tailWord_582058) baseStart_582058 baseEnd_582058 := by
    simpa [prefixWord, tailWord_582058, baseEnd_582058] using wordTrace_append hprefix tailTrace_582058
  have hstable : (prefixWord ++ tailWord_582058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582058).length < 2 ^ (prefixWord ++ tailWord_582058).sum := by decide
  have hdescent : baseEnd_582058 < baseStart_582058 := by decide
  rcases family_descends (prefixWord ++ tailWord_582058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582106 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5]
def baseStart_582106 : Nat := 118140960795 + 582106 * 2 ^ 59
def prefixEnd_582106 : Nat := 4983230072969 + 3 ^ 40 * 582106 * 2
def baseEnd_582106 : Nat := 298900169866204741297949

theorem tailTrace_582106 : CollatzResearch.WordTrace tailWord_582106 prefixEnd_582106 298900169866204741297949 := by
  unfold tailWord_582106
  simp only [CollatzResearch.WordTrace]
  refine ⟨5307787507284213158753543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14154100019424568423342781 5307787507284213158753543)
  ·
    refine ⟨7961681260926319738130315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5307787507284213158753543 7961681260926319738130315)
    ·
      refine ⟨11942521891389479607195473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7961681260926319738130315 11942521891389479607195473)
      ·
        refine ⟨8956891418542109705396605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11942521891389479607195473 8956891418542109705396605)
        ·
          refine ⟨3358834281953291139523727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8956891418542109705396605 3358834281953291139523727)
          ·
            refine ⟨5038251422929936709285591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3358834281953291139523727 5038251422929936709285591)
            ·
              refine ⟨7557377134394905063928387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5038251422929936709285591 7557377134394905063928387)
              ·
                refine ⟨11336065701592357595892581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7557377134394905063928387 11336065701592357595892581)
                ·
                  refine ⟨2125512319048567049229859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11336065701592357595892581 2125512319048567049229859)
                  ·
                    refine ⟨3188268478572850573844789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2125512319048567049229859 3188268478572850573844789)
                    ·
                      refine ⟨298900169866204741297949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3188268478572850573844789 298900169866204741297949)
                      ·
                        rfl

theorem cell23_582106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_582106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582106 prefixEnd_582106 := by exact prefixLift 582106
  have htrace : WordTrace (prefixWord ++ tailWord_582106) baseStart_582106 baseEnd_582106 := by
    simpa [prefixWord, tailWord_582106, baseEnd_582106] using wordTrace_append hprefix tailTrace_582106
  have hstable : (prefixWord ++ tailWord_582106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582106).length < 2 ^ (prefixWord ++ tailWord_582106).sum := by decide
  have hdescent : baseEnd_582106 < baseStart_582106 := by decide
  rcases family_descends (prefixWord ++ tailWord_582106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582116 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 6, 2, 4]
def baseStart_582116 : Nat := 118140960795 + 582116 * 2 ^ 59
def prefixEnd_582116 : Nat := 4983230072969 + 3 ^ 40 * 582116 * 2
def baseEnd_582116 : Nat := 298905304672749702172903

theorem tailTrace_582116 : CollatzResearch.WordTrace tailWord_582116 prefixEnd_582116 298905304672749702172903 := by
  unfold tailWord_582116
  simp only [CollatzResearch.WordTrace]
  refine ⟨10615757379550312171439101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14154343172733749561918801 10615757379550312171439101)
  ·
    refine ⟨3980909017331367064289663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10615757379550312171439101 3980909017331367064289663)
    ·
      refine ⟨5971363525997050596434495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3980909017331367064289663 5971363525997050596434495)
      ·
        refine ⟨8957045288995575894651743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5971363525997050596434495 8957045288995575894651743)
        ·
          refine ⟨13435567933493363841977615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8957045288995575894651743 13435567933493363841977615)
          ·
            refine ⟨20153351900240045762966423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13435567933493363841977615 20153351900240045762966423)
            ·
              refine ⟨30230027850360068644449635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20153351900240045762966423 30230027850360068644449635)
              ·
                refine ⟨45345041775540102966674453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30230027850360068644449635 45345041775540102966674453)
                ·
                  refine ⟨2125548833228442326562865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45345041775540102966674453 2125548833228442326562865)
                  ·
                    refine ⟨1594161624921331744922149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2125548833228442326562865 1594161624921331744922149)
                    ·
                      refine ⟨298905304672749702172903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1594161624921331744922149 298905304672749702172903)
                      ·
                        rfl

theorem cell23_582116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_582116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582116 prefixEnd_582116 := by exact prefixLift 582116
  have htrace : WordTrace (prefixWord ++ tailWord_582116) baseStart_582116 baseEnd_582116 := by
    simpa [prefixWord, tailWord_582116, baseEnd_582116] using wordTrace_append hprefix tailTrace_582116
  have hstable : (prefixWord ++ tailWord_582116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582116).length < 2 ^ (prefixWord ++ tailWord_582116).sum := by decide
  have hdescent : baseEnd_582116 < baseStart_582116 := by decide
  rcases family_descends (prefixWord ++ tailWord_582116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582120 : List Nat := [2, 1, 4, 1, 1, 4, 1, 2, 1, 4, 2]
def baseStart_582120 : Nat := 118140960795 + 582120 * 2 ^ 59
def prefixEnd_582120 : Nat := 4983230072969 + 3 ^ 40 * 582120 * 2
def baseEnd_582120 : Nat := 298907358595367686522885

theorem tailTrace_582120 : CollatzResearch.WordTrace tailWord_582120 prefixEnd_582120 298907358595367686522885 := by
  unfold tailWord_582120
  simp only [CollatzResearch.WordTrace]
  refine ⟨10615830325543066513011907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14154440434057422017349209 10615830325543066513011907)
  ·
    refine ⟨15923745488314599769517861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10615830325543066513011907 15923745488314599769517861)
    ·
      refine ⟨2985702279058987456784599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15923745488314599769517861 2985702279058987456784599)
      ·
        refine ⟨4478553418588481185176899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2985702279058987456784599 4478553418588481185176899)
        ·
          refine ⟨6717830127882721777765349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4478553418588481185176899 6717830127882721777765349)
          ·
            refine ⟨1259593148978010333331003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6717830127882721777765349 1259593148978010333331003)
            ·
              refine ⟨1889389723467015499996505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1259593148978010333331003 1889389723467015499996505)
              ·
                refine ⟨1417042292600261624997379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1889389723467015499996505 1417042292600261624997379)
                ·
                  refine ⟨2125563438900392437496069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1417042292600261624997379 2125563438900392437496069)
                  ·
                    refine ⟨398543144793823582030513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2125563438900392437496069 398543144793823582030513)
                    ·
                      refine ⟨298907358595367686522885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 398543144793823582030513 298907358595367686522885)
                      ·
                        rfl

theorem cell23_582120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_582120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582120 prefixEnd_582120 := by exact prefixLift 582120
  have htrace : WordTrace (prefixWord ++ tailWord_582120) baseStart_582120 baseEnd_582120 := by
    simpa [prefixWord, tailWord_582120, baseEnd_582120] using wordTrace_append hprefix tailTrace_582120
  have hstable : (prefixWord ++ tailWord_582120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582120).length < 2 ^ (prefixWord ++ tailWord_582120).sum := by decide
  have hdescent : baseEnd_582120 < baseStart_582120 := by decide
  rcases family_descends (prefixWord ++ tailWord_582120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582143 : List Nat := [1, 1, 2, 2, 1, 2, 5, 4, 5]
def baseStart_582143 : Nat := 118140960795 + 582143 * 2 ^ 59
def prefixEnd_582143 : Nat := 4983230072969 + 3 ^ 40 * 582143 * 2
def baseEnd_582143 : Nat := 33213240961157899615031

theorem tailTrace_582143 : CollatzResearch.WordTrace tailWord_582143 prefixEnd_582143 33213240961157899615031 := by
  unfold tailWord_582143
  simp only [CollatzResearch.WordTrace]
  refine ⟨21232499530002807954111083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14154999686668538636074055 21232499530002807954111083)
  ·
    refine ⟨31848749295004211931166625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21232499530002807954111083 31848749295004211931166625)
    ·
      refine ⟨23886561971253158948374969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31848749295004211931166625 23886561971253158948374969)
      ·
        refine ⟨17914921478439869211281227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23886561971253158948374969 17914921478439869211281227)
        ·
          refine ⟨26872382217659803816921841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17914921478439869211281227 26872382217659803816921841)
          ·
            refine ⟨20154286663244852862691381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26872382217659803816921841 20154286663244852862691381)
            ·
              refine ⟨1889464374679204955877317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20154286663244852862691381 1889464374679204955877317)
              ·
                refine ⟨354274570252350929226997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1889464374679204955877317 354274570252350929226997)
                ·
                  refine ⟨33213240961157899615031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 354274570252350929226997 33213240961157899615031)
                  ·
                    rfl

theorem cell23_582143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 5].length) (baseStart_582143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582143 prefixEnd_582143 := by exact prefixLift 582143
  have htrace : WordTrace (prefixWord ++ tailWord_582143) baseStart_582143 baseEnd_582143 := by
    simpa [prefixWord, tailWord_582143, baseEnd_582143] using wordTrace_append hprefix tailTrace_582143
  have hstable : (prefixWord ++ tailWord_582143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582143).length < 2 ^ (prefixWord ++ tailWord_582143).sum := by decide
  have hdescent : baseEnd_582143 < baseStart_582143 := by decide
  rcases family_descends (prefixWord ++ tailWord_582143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582163 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 2, 5, 2]
def baseStart_582163 : Nat := 118140960795 + 582163 * 2 ^ 59
def prefixEnd_582163 : Nat := 4983230072969 + 3 ^ 40 * 582163 * 2
def baseEnd_582163 : Nat := 298929438263511018285187

theorem tailTrace_582163 : CollatzResearch.WordTrace tailWord_582163 prefixEnd_582163 298929438263511018285187 := by
  unfold tailWord_582163
  simp only [CollatzResearch.WordTrace]
  refine ⟨21233228989930351369839143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14155485993286900913226095 21233228989930351369839143)
  ·
    refine ⟨31849843484895527054758715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21233228989930351369839143 31849843484895527054758715)
    ·
      refine ⟨47774765227343290582138073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31849843484895527054758715 47774765227343290582138073)
      ·
        refine ⟨35831073920507467936603555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47774765227343290582138073 35831073920507467936603555)
        ·
          refine ⟨53746610880761201904905333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35831073920507467936603555 53746610880761201904905333)
          ·
            refine ⟨5038744770071362678584875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53746610880761201904905333 5038744770071362678584875)
            ·
              refine ⟨7558117155107044017877313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5038744770071362678584875 7558117155107044017877313)
              ·
                refine ⟨5668587866330283013407985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7558117155107044017877313 5668587866330283013407985)
                ·
                  refine ⟨4251440899747712260055989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5668587866330283013407985 4251440899747712260055989)
                  ·
                    refine ⟨398572584351348024380249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4251440899747712260055989 398572584351348024380249)
                    ·
                      refine ⟨298929438263511018285187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 398572584351348024380249 298929438263511018285187)
                      ·
                        rfl

theorem cell23_582163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 5, 2].length) (baseStart_582163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582163 prefixEnd_582163 := by exact prefixLift 582163
  have htrace : WordTrace (prefixWord ++ tailWord_582163) baseStart_582163 baseEnd_582163 := by
    simpa [prefixWord, tailWord_582163, baseEnd_582163] using wordTrace_append hprefix tailTrace_582163
  have hstable : (prefixWord ++ tailWord_582163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582163).length < 2 ^ (prefixWord ++ tailWord_582163).sum := by decide
  have hdescent : baseEnd_582163 < baseStart_582163 := by decide
  rcases family_descends (prefixWord ++ tailWord_582163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582173 : List Nat := [1, 4, 2, 2, 1, 3, 1, 1, 1, 7]
def baseStart_582173 : Nat := 118140960795 + 582173 * 2 ^ 59
def prefixEnd_582173 : Nat := 4983230072969 + 3 ^ 40 * 582173 * 2
def baseEnd_582173 : Nat := 99644857690018659720047

theorem tailTrace_582173 : CollatzResearch.WordTrace tailWord_582173 prefixEnd_582173 99644857690018659720047 := by
  unfold tailWord_582173
  simp only [CollatzResearch.WordTrace]
  refine ⟨21233593719894123077703173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14155729146596082051802115 21233593719894123077703173)
  ·
    refine ⟨3981298822480148077069345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21233593719894123077703173 3981298822480148077069345)
    ·
      refine ⟨2985974116860111057802009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3981298822480148077069345 2985974116860111057802009)
      ·
        refine ⟨2239480587645083293351507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2985974116860111057802009 2239480587645083293351507)
        ·
          refine ⟨3359220881467624940027261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2239480587645083293351507 3359220881467624940027261)
          ·
            refine ⟨1259707830550359352510223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3359220881467624940027261 1259707830550359352510223)
            ·
              refine ⟨1889561745825539028765335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1259707830550359352510223 1889561745825539028765335)
              ·
                refine ⟨2834342618738308543148003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1889561745825539028765335 2834342618738308543148003)
                ·
                  refine ⟨4251513928107462814722005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2834342618738308543148003 4251513928107462814722005)
                  ·
                    refine ⟨99644857690018659720047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4251513928107462814722005 99644857690018659720047)
                    ·
                      rfl

theorem cell23_582173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_582173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582173 prefixEnd_582173 := by exact prefixLift 582173
  have htrace : WordTrace (prefixWord ++ tailWord_582173) baseStart_582173 baseEnd_582173 := by
    simpa [prefixWord, tailWord_582173, baseEnd_582173] using wordTrace_append hprefix tailTrace_582173
  have hstable : (prefixWord ++ tailWord_582173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582173).length < 2 ^ (prefixWord ++ tailWord_582173).sum := by decide
  have hdescent : baseEnd_582173 < baseStart_582173 := by decide
  rcases family_descends (prefixWord ++ tailWord_582173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582193 : List Nat := [1, 2, 2, 3, 1, 1, 2, 4, 2, 1, 4]
def baseStart_582193 : Nat := 118140960795 + 582193 * 2 ^ 59
def prefixEnd_582193 : Nat := 4983230072969 + 3 ^ 40 * 582193 * 2
def baseEnd_582193 : Nat := 298944842683145900910049

theorem tailTrace_582193 : CollatzResearch.WordTrace tailWord_582193 prefixEnd_582193 298944842683145900910049 := by
  unfold tailWord_582193
  simp only [CollatzResearch.WordTrace]
  refine ⟨21234323179821666493431233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14156215453214444328954155 21234323179821666493431233)
  ·
    refine ⟨15925742384866249870073425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21234323179821666493431233 15925742384866249870073425)
    ·
      refine ⟨11944306788649687402555069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15925742384866249870073425 11944306788649687402555069)
      ·
        refine ⟨4479115045743632775958151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11944306788649687402555069 4479115045743632775958151)
        ·
          refine ⟨6718672568615449163937227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4479115045743632775958151 6718672568615449163937227)
          ·
            refine ⟨10078008852923173745905841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6718672568615449163937227 10078008852923173745905841)
            ·
              refine ⟨7558506639692380309429381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10078008852923173745905841 7558506639692380309429381)
              ·
                refine ⟨1417219994942321308018009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7558506639692380309429381 1417219994942321308018009)
                ·
                  refine ⟨1062914996206740981013507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1417219994942321308018009 1062914996206740981013507)
                  ·
                    refine ⟨1594372494310111471520261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1062914996206740981013507 1594372494310111471520261)
                    ·
                      refine ⟨298944842683145900910049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1594372494310111471520261 298944842683145900910049)
                      ·
                        rfl

theorem cell23_582193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_582193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582193 prefixEnd_582193 := by exact prefixLift 582193
  have htrace : WordTrace (prefixWord ++ tailWord_582193) baseStart_582193 baseEnd_582193 := by
    simpa [prefixWord, tailWord_582193, baseEnd_582193] using wordTrace_append hprefix tailTrace_582193
  have hstable : (prefixWord ++ tailWord_582193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582193).length < 2 ^ (prefixWord ++ tailWord_582193).sum := by decide
  have hdescent : baseEnd_582193 < baseStart_582193 := by decide
  rcases family_descends (prefixWord ++ tailWord_582193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582213 : List Nat := [1, 3, 1, 1, 1, 5, 1, 2, 1, 4, 3]
def baseStart_582213 : Nat := 118140960795 + 582213 * 2 ^ 59
def prefixEnd_582213 : Nat := 4983230072969 + 3 ^ 40 * 582213 * 2
def baseEnd_582213 : Nat := 298955112296235822659957

theorem tailTrace_582213 : CollatzResearch.WordTrace tailWord_582213 prefixEnd_582213 298955112296235822659957 := by
  unfold tailWord_582213
  simp only [CollatzResearch.WordTrace]
  refine ⟨21235052639749209909159293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14156701759832806606106195 21235052639749209909159293)
  ·
    refine ⟨7963144739905953715934735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21235052639749209909159293 7963144739905953715934735)
    ·
      refine ⟨11944717109858930573902103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7963144739905953715934735 11944717109858930573902103)
      ·
        refine ⟨17917075664788395860853155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11944717109858930573902103 17917075664788395860853155)
        ·
          refine ⟨26875613497182593791279733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17917075664788395860853155 26875613497182593791279733)
          ·
            refine ⟨2519588765360868167932475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26875613497182593791279733 2519588765360868167932475)
            ·
              refine ⟨3779383148041302251898713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2519588765360868167932475 3779383148041302251898713)
              ·
                refine ⟨2834537361030976688924035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3779383148041302251898713 2834537361030976688924035)
                ·
                  refine ⟨4251806041546465033386053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2834537361030976688924035 4251806041546465033386053)
                  ·
                    refine ⟨797213632789962193759885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4251806041546465033386053 797213632789962193759885)
                    ·
                      refine ⟨298955112296235822659957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 797213632789962193759885 298955112296235822659957)
                      ·
                        rfl

theorem cell23_582213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 4, 3].length) (baseStart_582213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582213 prefixEnd_582213 := by exact prefixLift 582213
  have htrace : WordTrace (prefixWord ++ tailWord_582213) baseStart_582213 baseEnd_582213 := by
    simpa [prefixWord, tailWord_582213, baseEnd_582213] using wordTrace_append hprefix tailTrace_582213
  have hstable : (prefixWord ++ tailWord_582213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582213).length < 2 ^ (prefixWord ++ tailWord_582213).sum := by decide
  have hdescent : baseEnd_582213 < baseStart_582213 := by decide
  rcases family_descends (prefixWord ++ tailWord_582213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582323 : List Nat := [1, 1, 1, 2, 3, 4, 3, 8]
def baseStart_582323 : Nat := 118140960795 + 582323 * 2 ^ 59
def prefixEnd_582323 : Nat := 4983230072969 + 3 ^ 40 * 582323 * 2
def baseEnd_582323 : Nat := 11074503524749273788313

theorem tailTrace_582323 : CollatzResearch.WordTrace tailWord_582323 prefixEnd_582323 11074503524749273788313 := by
  unfold tailWord_582323
  simp only [CollatzResearch.WordTrace]
  refine ⟨21239064669350698695663623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14159376446233799130442415 21239064669350698695663623)
  ·
    refine ⟨31858597004026048043495435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21239064669350698695663623 31858597004026048043495435)
    ·
      refine ⟨47787895506039072065243153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31858597004026048043495435 47787895506039072065243153)
      ·
        refine ⟨35840921629529304048932365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47787895506039072065243153 35840921629529304048932365)
        ·
          refine ⟨13440345611073489018349637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35840921629529304048932365 13440345611073489018349637)
          ·
            refine ⟨2520064802076279190940557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13440345611073489018349637 2520064802076279190940557)
            ·
              refine ⟨945024300778604696602709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2520064802076279190940557 945024300778604696602709)
              ·
                refine ⟨11074503524749273788313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 945024300778604696602709 11074503524749273788313)
                ·
                  rfl

theorem cell23_582323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 8].length) (baseStart_582323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582323 prefixEnd_582323 := by exact prefixLift 582323
  have htrace : WordTrace (prefixWord ++ tailWord_582323) baseStart_582323 baseEnd_582323 := by
    simpa [prefixWord, tailWord_582323, baseEnd_582323] using wordTrace_append hprefix tailTrace_582323
  have hstable : (prefixWord ++ tailWord_582323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582323).length < 2 ^ (prefixWord ++ tailWord_582323).sum := by decide
  have hdescent : baseEnd_582323 < baseStart_582323 := by decide
  rcases family_descends (prefixWord ++ tailWord_582323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582330 : List Nat := [3, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4]
def baseStart_582330 : Nat := 118140960795 + 582330 * 2 ^ 59
def prefixEnd_582330 : Nat := 4983230072969 + 3 ^ 40 * 582330 * 2
def baseEnd_582330 : Nat := 299015189532811864896919

theorem tailTrace_582330 : CollatzResearch.WordTrace tailWord_582330 prefixEnd_582330 299015189532811864896919 := by
  unfold tailWord_582330
  simp only [CollatzResearch.WordTrace]
  refine ⟨5309829995081334722792111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14159546653550225927445629 5309829995081334722792111)
  ·
    refine ⟨7964744992622002084188167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5309829995081334722792111 7964744992622002084188167)
    ·
      refine ⟨11947117488933003126282251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7964744992622002084188167 11947117488933003126282251)
      ·
        refine ⟨17920676233399504689423377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11947117488933003126282251 17920676233399504689423377)
        ·
          refine ⟨13440507175049628517067533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17920676233399504689423377 13440507175049628517067533)
          ·
            refine ⟨5040190190643610693900325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13440507175049628517067533 5040190190643610693900325)
            ·
              refine ⟨945035660745677005106311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5040190190643610693900325 945035660745677005106311)
              ·
                refine ⟨1417553491118515507659467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 945035660745677005106311 1417553491118515507659467)
                ·
                  refine ⟨2126330236677773261489201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1417553491118515507659467 2126330236677773261489201)
                  ·
                    refine ⟨1594747677508329946116901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2126330236677773261489201 1594747677508329946116901)
                    ·
                      refine ⟨299015189532811864896919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1594747677508329946116901 299015189532811864896919)
                      ·
                        rfl

theorem cell23_582330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4].length) (baseStart_582330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582330 prefixEnd_582330 := by exact prefixLift 582330
  have htrace : WordTrace (prefixWord ++ tailWord_582330) baseStart_582330 baseEnd_582330 := by
    simpa [prefixWord, tailWord_582330, baseEnd_582330] using wordTrace_append hprefix tailTrace_582330
  have hstable : (prefixWord ++ tailWord_582330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582330).length < 2 ^ (prefixWord ++ tailWord_582330).sum := by decide
  have hdescent : baseEnd_582330 < baseStart_582330 := by decide
  rcases family_descends (prefixWord ++ tailWord_582330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582334 : List Nat := [4, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2]
def baseStart_582334 : Nat := 118140960795 + 582334 * 2 ^ 59
def prefixEnd_582334 : Nat := 4983230072969 + 3 ^ 40 * 582334 * 2
def baseEnd_582334 : Nat := 299017243455429849246901

theorem tailTrace_582334 : CollatzResearch.WordTrace tailWord_582334 prefixEnd_582334 299017243455429849246901 := by
  unfold tailWord_582334
  simp only [CollatzResearch.WordTrace]
  refine ⟨2654933234038855946789257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14159643914873898382876037 2654933234038855946789257)
  ·
    refine ⟨1991199925529141960091943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2654933234038855946789257 1991199925529141960091943)
    ·
      refine ⟨2986799888293712940137915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1991199925529141960091943 2986799888293712940137915)
      ·
        refine ⟨4480199832440569410206873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2986799888293712940137915 4480199832440569410206873)
        ·
          refine ⟨3360149874330427057655155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4480199832440569410206873 3360149874330427057655155)
          ·
            refine ⟨5040224811495640586482733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3360149874330427057655155 5040224811495640586482733)
            ·
              refine ⟨1890084304310865219931025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5040224811495640586482733 1890084304310865219931025)
              ·
                refine ⟨1417563228233148914948269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1890084304310865219931025 1417563228233148914948269)
                ·
                  refine ⟨531586210587430843105601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1417563228233148914948269 531586210587430843105601)
                  ·
                    refine ⟨398689657940573132329201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 531586210587430843105601 398689657940573132329201)
                    ·
                      refine ⟨299017243455429849246901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 398689657940573132329201 299017243455429849246901)
                      ·
                        rfl

theorem cell23_582334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_582334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582334 prefixEnd_582334 := by exact prefixLift 582334
  have htrace : WordTrace (prefixWord ++ tailWord_582334) baseStart_582334 baseEnd_582334 := by
    simpa [prefixWord, tailWord_582334, baseEnd_582334] using wordTrace_append hprefix tailTrace_582334
  have hstable : (prefixWord ++ tailWord_582334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582334).length < 2 ^ (prefixWord ++ tailWord_582334).sum := by decide
  have hdescent : baseEnd_582334 < baseStart_582334 := by decide
  rcases family_descends (prefixWord ++ tailWord_582334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582354 : List Nat := [3, 2, 2, 2, 3, 1, 1, 3, 1, 2, 3]
def baseStart_582354 : Nat := 118140960795 + 582354 * 2 ^ 59
def prefixEnd_582354 : Nat := 4983230072969 + 3 ^ 40 * 582354 * 2
def baseEnd_582354 : Nat := 299027513068519770996809

theorem tailTrace_582354 : CollatzResearch.WordTrace tailWord_582354 prefixEnd_582354 299027513068519770996809 := by
  unfold tailWord_582354
  simp only [CollatzResearch.WordTrace]
  refine ⟨5310048833059597747510529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14160130221492260660028077 5310048833059597747510529)
  ·
    refine ⟨3982536624794698310632897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5310048833059597747510529 3982536624794698310632897)
    ·
      refine ⟨2986902468596023732974673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3982536624794698310632897 2986902468596023732974673)
      ·
        refine ⟨2240176851447017799731005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2986902468596023732974673 2240176851447017799731005)
        ·
          refine ⟨840066319292631674899127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2240176851447017799731005 840066319292631674899127)
          ·
            refine ⟨1260099478938947512348691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 840066319292631674899127 1260099478938947512348691)
            ·
              refine ⟨1890149218408421268523037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1260099478938947512348691 1890149218408421268523037)
              ·
                refine ⟨708805956903157975696139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1890149218408421268523037 708805956903157975696139)
                ·
                  refine ⟨1063208935354736963544209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 708805956903157975696139 1063208935354736963544209)
                  ·
                    refine ⟨797406701516052722658157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1063208935354736963544209 797406701516052722658157)
                    ·
                      refine ⟨299027513068519770996809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 797406701516052722658157 299027513068519770996809)
                      ·
                        rfl

theorem cell23_582354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_582354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582354 prefixEnd_582354 := by exact prefixLift 582354
  have htrace : WordTrace (prefixWord ++ tailWord_582354) baseStart_582354 baseEnd_582354 := by
    simpa [prefixWord, tailWord_582354, baseEnd_582354] using wordTrace_append hprefix tailTrace_582354
  have hstable : (prefixWord ++ tailWord_582354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582354).length < 2 ^ (prefixWord ++ tailWord_582354).sum := by decide
  have hdescent : baseEnd_582354 < baseStart_582354 := by decide
  rcases family_descends (prefixWord ++ tailWord_582354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582367 : List Nat := [1, 1, 2, 3, 2, 4, 1, 1, 4, 1, 3]
def baseStart_582367 : Nat := 118140960795 + 582367 * 2 ^ 59
def prefixEnd_582367 : Nat := 4983230072969 + 3 ^ 40 * 582367 * 2
def baseEnd_582367 : Nat := 299034188317028220134249

theorem tailTrace_582367 : CollatzResearch.WordTrace tailWord_582367 prefixEnd_582367 299034188317028220134249 := by
  unfold tailWord_582367
  simp only [CollatzResearch.WordTrace]
  refine ⟨21240669481191294210265355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14160446320794196140176903 21240669481191294210265355)
  ·
    refine ⟨31861004221786941315398033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21240669481191294210265355 31861004221786941315398033)
    ·
      refine ⟨23895753166340205986548525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31861004221786941315398033 23895753166340205986548525)
      ·
        refine ⟨8960907437377577244955697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23895753166340205986548525 8960907437377577244955697)
        ·
          refine ⟨6720680578033182933716773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8960907437377577244955697 6720680578033182933716773)
          ·
            refine ⟨1260127608381221800071895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6720680578033182933716773 1260127608381221800071895)
            ·
              refine ⟨1890191412571832700107843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1260127608381221800071895 1890191412571832700107843)
              ·
                refine ⟨2835287118857749050161765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1890191412571832700107843 2835287118857749050161765)
                ·
                  refine ⟨531616334785827946905331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2835287118857749050161765 531616334785827946905331)
                  ·
                    refine ⟨797424502178741920357997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 531616334785827946905331 797424502178741920357997)
                    ·
                      refine ⟨299034188317028220134249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 797424502178741920357997 299034188317028220134249)
                      ·
                        rfl

theorem cell23_582367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_582367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582367 prefixEnd_582367 := by exact prefixLift 582367
  have htrace : WordTrace (prefixWord ++ tailWord_582367) baseStart_582367 baseEnd_582367 := by
    simpa [prefixWord, tailWord_582367, baseEnd_582367] using wordTrace_append hprefix tailTrace_582367
  have hstable : (prefixWord ++ tailWord_582367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582367).length < 2 ^ (prefixWord ++ tailWord_582367).sum := by decide
  have hdescent : baseEnd_582367 < baseStart_582367 := by decide
  rcases family_descends (prefixWord ++ tailWord_582367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582384 : List Nat := [2, 1, 1, 1, 3, 1, 7, 1, 2, 1, 3]
def baseStart_582384 : Nat := 118140960795 + 582384 * 2 ^ 59
def prefixEnd_582384 : Nat := 4983230072969 + 3 ^ 40 * 582384 * 2
def baseEnd_582384 : Nat := 299042917488154653621671

theorem tailTrace_582384 : CollatzResearch.WordTrace tailWord_582384 prefixEnd_582384 299042917488154653621671 := by
  unfold tailWord_582384
  simp only [CollatzResearch.WordTrace]
  refine ⟨10620644761064853056817103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14160859681419804075756137 10620644761064853056817103)
  ·
    refine ⟨15930967141597279585225655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10620644761064853056817103 15930967141597279585225655)
    ·
      refine ⟨23896450712395919377838483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15930967141597279585225655 23896450712395919377838483)
      ·
        refine ⟨35844676068593879066757725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23896450712395919377838483 35844676068593879066757725)
        ·
          refine ⟨13441753525722704650034147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35844676068593879066757725 13441753525722704650034147)
          ·
            refine ⟨20162630288584056975051221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13441753525722704650034147 20162630288584056975051221)
            ·
              refine ⟨472561647388688835352763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 20162630288584056975051221 472561647388688835352763)
              ·
                refine ⟨708842471083033253029145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 472561647388688835352763 708842471083033253029145)
                ·
                  refine ⟨531631853312274939771859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 708842471083033253029145 531631853312274939771859)
                  ·
                    refine ⟨797447779968412409657789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 531631853312274939771859 797447779968412409657789)
                    ·
                      refine ⟨299042917488154653621671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 797447779968412409657789 299042917488154653621671)
                      ·
                        rfl

theorem cell23_582384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 2, 1, 3].length) (baseStart_582384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582384 prefixEnd_582384 := by exact prefixLift 582384
  have htrace : WordTrace (prefixWord ++ tailWord_582384) baseStart_582384 baseEnd_582384 := by
    simpa [prefixWord, tailWord_582384, baseEnd_582384] using wordTrace_append hprefix tailTrace_582384
  have hstable : (prefixWord ++ tailWord_582384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582384).length < 2 ^ (prefixWord ++ tailWord_582384).sum := by decide
  have hdescent : baseEnd_582384 < baseStart_582384 := by decide
  rcases family_descends (prefixWord ++ tailWord_582384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582388 : List Nat := [2, 6, 1, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_582388 : Nat := 118140960795 + 582388 * 2 ^ 59
def prefixEnd_582388 : Nat := 4983230072969 + 3 ^ 40 * 582388 * 2
def baseEnd_582388 : Nat := 299044971410772637971653

theorem tailTrace_582388 : CollatzResearch.WordTrace tailWord_582388 prefixEnd_582388 299044971410772637971653 := by
  unfold tailWord_582388
  simp only [CollatzResearch.WordTrace]
  refine ⟨10620717707057607398389909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14160956942743476531186545 10620717707057607398389909)
  ·
    refine ⟨497846142518325346799527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10620717707057607398389909 497846142518325346799527)
    ·
      refine ⟨746769213777488020199291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 497846142518325346799527 746769213777488020199291)
      ·
        refine ⟨1120153820666232030298937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 746769213777488020199291 1120153820666232030298937)
        ·
          refine ⟨840115365499674022724203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1120153820666232030298937 840115365499674022724203)
          ·
            refine ⟨1260173048249511034086305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 840115365499674022724203 1260173048249511034086305)
            ·
              refine ⟨945129786187133275564729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1260173048249511034086305 945129786187133275564729)
              ·
                refine ⟨708847339640349956673547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 945129786187133275564729 708847339640349956673547)
                ·
                  refine ⟨1063271009460524935010321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 708847339640349956673547 1063271009460524935010321)
                  ·
                    refine ⟨797453257095393701257741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1063271009460524935010321 797453257095393701257741)
                    ·
                      refine ⟨299044971410772637971653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 797453257095393701257741 299044971410772637971653)
                      ·
                        rfl

theorem cell23_582388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_582388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582388 prefixEnd_582388 := by exact prefixLift 582388
  have htrace : WordTrace (prefixWord ++ tailWord_582388) baseStart_582388 baseEnd_582388 := by
    simpa [prefixWord, tailWord_582388, baseEnd_582388] using wordTrace_append hprefix tailTrace_582388
  have hstable : (prefixWord ++ tailWord_582388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582388).length < 2 ^ (prefixWord ++ tailWord_582388).sum := by decide
  have hdescent : baseEnd_582388 < baseStart_582388 := by decide
  rcases family_descends (prefixWord ++ tailWord_582388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582393 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 3, 3, 5]
def baseStart_582393 : Nat := 118140960795 + 582393 * 2 ^ 59
def prefixEnd_582393 : Nat := 4983230072969 + 3 ^ 40 * 582393 * 2
def baseEnd_582393 : Nat := 299047538814045118409129

theorem tailTrace_582393 : CollatzResearch.WordTrace tailWord_582393 prefixEnd_582393 299047538814045118409129 := by
  unfold tailWord_582393
  simp only [CollatzResearch.WordTrace]
  refine ⟨21241617779097100650711833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14161078519398067100474555 21241617779097100650711833)
  ·
    refine ⟨15931213334322825488033875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21241617779097100650711833 15931213334322825488033875)
    ·
      refine ⟨23896820001484238232050813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15931213334322825488033875 23896820001484238232050813)
      ·
        refine ⟨8961307500556589337019055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23896820001484238232050813 8961307500556589337019055)
        ·
          refine ⟨13441961250834884005528583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8961307500556589337019055 13441961250834884005528583)
          ·
            refine ⟨20162941876252326008292875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13441961250834884005528583 20162941876252326008292875)
            ·
              refine ⟨30244412814378489012439313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20162941876252326008292875 30244412814378489012439313)
              ·
                refine ⟨22683309610783866759329485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30244412814378489012439313 22683309610783866759329485)
                ·
                  refine ⟨8506241104043950034748557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22683309610783866759329485 8506241104043950034748557)
                  ·
                    refine ⟨3189840414016481263030709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8506241104043950034748557 3189840414016481263030709)
                    ·
                      refine ⟨299047538814045118409129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3189840414016481263030709 299047538814045118409129)
                      ·
                        rfl

theorem cell23_582393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_582393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582393 prefixEnd_582393 := by exact prefixLift 582393
  have htrace : WordTrace (prefixWord ++ tailWord_582393) baseStart_582393 baseEnd_582393 := by
    simpa [prefixWord, tailWord_582393, baseEnd_582393] using wordTrace_append hprefix tailTrace_582393
  have hstable : (prefixWord ++ tailWord_582393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582393).length < 2 ^ (prefixWord ++ tailWord_582393).sum := by decide
  have hdescent : baseEnd_582393 < baseStart_582393 := by decide
  rcases family_descends (prefixWord ++ tailWord_582393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582410 : List Nat := [3, 1, 2, 2, 1, 2, 3, 1, 2, 1, 5]
def baseStart_582410 : Nat := 118140960795 + 582410 * 2 ^ 59
def prefixEnd_582410 : Nat := 4983230072969 + 3 ^ 40 * 582410 * 2
def baseEnd_582410 : Nat := 299056267985171551896551

theorem tailTrace_582410 : CollatzResearch.WordTrace tailWord_582410 prefixEnd_582410 299056267985171551896551 := by
  unfold tailWord_582410
  simp only [CollatzResearch.WordTrace]
  refine ⟨5310559455008878138520171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14161491880023675036053789 5310559455008878138520171)
  ·
    refine ⟨7965839182513317207780257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5310559455008878138520171 7965839182513317207780257)
    ·
      refine ⟨5974379386884987905835193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7965839182513317207780257 5974379386884987905835193)
      ·
        refine ⟨4480784540163740929376395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5974379386884987905835193 4480784540163740929376395)
        ·
          refine ⟨6721176810245611394064593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4480784540163740929376395 6721176810245611394064593)
          ·
            refine ⟨5040882607684208545548445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6721176810245611394064593 5040882607684208545548445)
            ·
              refine ⟨1890330977881578204580667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5040882607684208545548445 1890330977881578204580667)
              ·
                refine ⟨2835496466822367306871001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1890330977881578204580667 2835496466822367306871001)
                ·
                  refine ⟨2126622350116775480153251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2835496466822367306871001 2126622350116775480153251)
                  ·
                    refine ⟨3189933525175163220229877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2126622350116775480153251 3189933525175163220229877)
                    ·
                      refine ⟨299056267985171551896551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3189933525175163220229877 299056267985171551896551)
                      ·
                        rfl

theorem cell23_582410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_582410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582410 prefixEnd_582410 := by exact prefixLift 582410
  have htrace : WordTrace (prefixWord ++ tailWord_582410) baseStart_582410 baseEnd_582410 := by
    simpa [prefixWord, tailWord_582410, baseEnd_582410] using wordTrace_append hprefix tailTrace_582410
  have hstable : (prefixWord ++ tailWord_582410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582410).length < 2 ^ (prefixWord ++ tailWord_582410).sum := by decide
  have hdescent : baseEnd_582410 < baseStart_582410 := by decide
  rcases family_descends (prefixWord ++ tailWord_582410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582424 : List Nat := [2, 1, 2, 3, 1, 1, 1, 6, 2, 2, 2]
def baseStart_582424 : Nat := 118140960795 + 582424 * 2 ^ 59
def prefixEnd_582424 : Nat := 4983230072969 + 3 ^ 40 * 582424 * 2
def baseEnd_582424 : Nat := 299063456714334497121487

theorem tailTrace_582424 : CollatzResearch.WordTrace tailWord_582424 prefixEnd_582424 299063456714334497121487 := by
  unfold tailWord_582424
  simp only [CollatzResearch.WordTrace]
  refine ⟨10621374220992396472545163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14161832294656528630060217 10621374220992396472545163)
  ·
    refine ⟨15932061331488594708817745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10621374220992396472545163 15932061331488594708817745)
    ·
      refine ⟨11949045998616446031613309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15932061331488594708817745 11949045998616446031613309)
      ·
        refine ⟨4480892249481167261854991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11949045998616446031613309 4480892249481167261854991)
        ·
          refine ⟨6721338374221750892782487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4480892249481167261854991 6721338374221750892782487)
          ·
            refine ⟨10082007561332626339173731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6721338374221750892782487 10082007561332626339173731)
            ·
              refine ⟨15123011341998939508760597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10082007561332626339173731 15123011341998939508760597)
              ·
                refine ⟨708891156656200289473153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15123011341998939508760597 708891156656200289473153)
                ·
                  refine ⟨531668367492150217104865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 708891156656200289473153 531668367492150217104865)
                  ·
                    refine ⟨398751275619112662828649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 531668367492150217104865 398751275619112662828649)
                    ·
                      refine ⟨299063456714334497121487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 398751275619112662828649 299063456714334497121487)
                      ·
                        rfl

theorem cell23_582424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_582424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582424 prefixEnd_582424 := by exact prefixLift 582424
  have htrace : WordTrace (prefixWord ++ tailWord_582424) baseStart_582424 baseEnd_582424 := by
    simpa [prefixWord, tailWord_582424, baseEnd_582424] using wordTrace_append hprefix tailTrace_582424
  have hstable : (prefixWord ++ tailWord_582424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582424).length < 2 ^ (prefixWord ++ tailWord_582424).sum := by decide
  have hdescent : baseEnd_582424 < baseStart_582424 := by decide
  rcases family_descends (prefixWord ++ tailWord_582424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582445 : List Nat := [1, 5, 3, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_582445 : Nat := 118140960795 + 582445 * 2 ^ 59
def prefixEnd_582445 : Nat := 4983230072969 + 3 ^ 40 * 582445 * 2
def baseEnd_582445 : Nat := 299074239808078914958891

theorem tailTrace_582445 : CollatzResearch.WordTrace tailWord_582445 prefixEnd_582445 299074239808078914958891 := by
  unfold tailWord_582445
  simp only [CollatzResearch.WordTrace]
  refine ⟨21243514374908713531604789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14162342916605809021069859 21243514374908713531604789)
  ·
    refine ⟨1991579472647691893587949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21243514374908713531604789 1991579472647691893587949)
    ·
      refine ⟨746842302242884460095481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1991579472647691893587949 746842302242884460095481)
      ·
        refine ⟨560131726682163345071611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 746842302242884460095481 560131726682163345071611)
        ·
          refine ⟨840197590023245017607417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560131726682163345071611 840197590023245017607417)
          ·
            refine ⟨630148192517433763205563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 840197590023245017607417 630148192517433763205563)
            ·
              refine ⟨945222288776150644808345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 630148192517433763205563 945222288776150644808345)
              ·
                refine ⟨708916716582112983606259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 945222288776150644808345 708916716582112983606259)
                ·
                  refine ⟨1063375074873169475409389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 708916716582112983606259 1063375074873169475409389)
                  ·
                    refine ⟨398765653077438553278521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1063375074873169475409389 398765653077438553278521)
                    ·
                      refine ⟨299074239808078914958891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 398765653077438553278521 299074239808078914958891)
                      ·
                        rfl

theorem cell23_582445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_582445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582445 prefixEnd_582445 := by exact prefixLift 582445
  have htrace : WordTrace (prefixWord ++ tailWord_582445) baseStart_582445 baseEnd_582445 := by
    simpa [prefixWord, tailWord_582445, baseEnd_582445] using wordTrace_append hprefix tailTrace_582445
  have hstable : (prefixWord ++ tailWord_582445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582445).length < 2 ^ (prefixWord ++ tailWord_582445).sum := by decide
  have hdescent : baseEnd_582445 < baseStart_582445 := by decide
  rcases family_descends (prefixWord ++ tailWord_582445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582481 : List Nat := [1, 2, 2, 1, 6, 2, 2, 2, 5]
def baseStart_582481 : Nat := 118140960795 + 582481 * 2 ^ 59
def prefixEnd_582481 : Nat := 4983230072969 + 3 ^ 40 * 582481 * 2
def baseEnd_582481 : Nat := 33232525012404530456525

theorem tailTrace_582481 : CollatzResearch.WordTrace tailWord_582481 prefixEnd_582481 33232525012404530456525 := by
  unfold tailWord_582481
  simp only [CollatzResearch.WordTrace]
  refine ⟨21244827402778291679915297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14163218268518861119943531 21244827402778291679915297)
  ·
    refine ⟨15933620552083718759936473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21244827402778291679915297 15933620552083718759936473)
    ·
      refine ⟨11950215414062789069952355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15933620552083718759936473 11950215414062789069952355)
      ·
        refine ⟨17925323121094183604928533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11950215414062789069952355 17925323121094183604928533)
        ·
          refine ⟨840249521301289856481025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17925323121094183604928533 840249521301289856481025)
          ·
            refine ⟨630187140975967392360769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 840249521301289856481025 630187140975967392360769)
            ·
              refine ⟨472640355731975544270577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 630187140975967392360769 472640355731975544270577)
              ·
                refine ⟨354480266798981658202933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 472640355731975544270577 354480266798981658202933)
                ·
                  refine ⟨33232525012404530456525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 354480266798981658202933 33232525012404530456525)
                  ·
                    rfl

theorem cell23_582481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 5].length) (baseStart_582481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582481 prefixEnd_582481 := by exact prefixLift 582481
  have htrace : WordTrace (prefixWord ++ tailWord_582481) baseStart_582481 baseEnd_582481 := by
    simpa [prefixWord, tailWord_582481, baseEnd_582481] using wordTrace_append hprefix tailTrace_582481
  have hstable : (prefixWord ++ tailWord_582481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582481).length < 2 ^ (prefixWord ++ tailWord_582481).sum := by decide
  have hdescent : baseEnd_582481 < baseStart_582481 := by decide
  rcases family_descends (prefixWord ++ tailWord_582481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582537 : List Nat := [1, 2, 1, 1, 5, 2, 3, 2, 6]
def baseStart_582537 : Nat := 118140960795 + 582537 * 2 ^ 59
def prefixEnd_582537 : Nat := 4983230072969 + 3 ^ 40 * 582537 * 2
def baseEnd_582537 : Nat := 33235720003143617223163

theorem tailTrace_582537 : CollatzResearch.WordTrace tailWord_582537 prefixEnd_582537 33235720003143617223163 := by
  unfold tailWord_582537
  simp only [CollatzResearch.WordTrace]
  refine ⟨21246869890575413243953865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14164579927050275495969243 21246869890575413243953865)
  ·
    refine ⟨15935152417931559932965399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21246869890575413243953865 15935152417931559932965399)
    ·
      refine ⟨23902728626897339899448099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15935152417931559932965399 23902728626897339899448099)
      ·
        refine ⟨35854092940346009849172149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23902728626897339899448099 35854092940346009849172149)
        ·
          refine ⟨3361321213157438423359889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35854092940346009849172149 3361321213157438423359889)
          ·
            refine ⟨2520990909868078817519917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3361321213157438423359889 2520990909868078817519917)
            ·
              refine ⟨945371591200529556569969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2520990909868078817519917 945371591200529556569969)
              ·
                refine ⟨709028693400397167427477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 945371591200529556569969 709028693400397167427477)
                ·
                  refine ⟨33235720003143617223163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 709028693400397167427477 33235720003143617223163)
                  ·
                    rfl

theorem cell23_582537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 6].length) (baseStart_582537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582537 prefixEnd_582537 := by exact prefixLift 582537
  have htrace : WordTrace (prefixWord ++ tailWord_582537) baseStart_582537 baseEnd_582537 := by
    simpa [prefixWord, tailWord_582537, baseEnd_582537] using wordTrace_append hprefix tailTrace_582537
  have hstable : (prefixWord ++ tailWord_582537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582537).length < 2 ^ (prefixWord ++ tailWord_582537).sum := by decide
  have hdescent : baseEnd_582537 < baseStart_582537 := by decide
  rcases family_descends (prefixWord ++ tailWord_582537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582540 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 1, 2, 6]
def baseStart_582540 : Nat := 118140960795 + 582540 * 2 ^ 59
def prefixEnd_582540 : Nat := 4983230072969 + 3 ^ 40 * 582540 * 2
def baseEnd_582540 : Nat := 299123020470256043270953

theorem tailTrace_582540 : CollatzResearch.WordTrace tailWord_582540 prefixEnd_582540 299123020470256043270953 := by
  unfold tailWord_582540
  simp only [CollatzResearch.WordTrace]
  refine ⟨10623489654782272378156537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14164652873043029837542049 10623489654782272378156537)
  ·
    refine ⟨7967617241086704283617403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10623489654782272378156537 7967617241086704283617403)
    ·
      refine ⟨11951425861630056425426105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7967617241086704283617403 11951425861630056425426105)
      ·
        refine ⟨8963569396222542319069579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11951425861630056425426105 8963569396222542319069579)
        ·
          refine ⟨13445354094333813478604369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8963569396222542319069579 13445354094333813478604369)
          ·
            refine ⟨10084015570750360108953277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13445354094333813478604369 10084015570750360108953277)
            ·
              refine ⟨3781505839031385040857479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10084015570750360108953277 3781505839031385040857479)
              ·
                refine ⟨5672258758547077561286219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3781505839031385040857479 5672258758547077561286219)
                ·
                  refine ⟨8508388137820616341929329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5672258758547077561286219 8508388137820616341929329)
                  ·
                    refine ⟨6381291103365462256446997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8508388137820616341929329 6381291103365462256446997)
                    ·
                      refine ⟨299123020470256043270953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6381291103365462256446997 299123020470256043270953)
                      ·
                        rfl

theorem cell23_582540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_582540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582540 prefixEnd_582540 := by exact prefixLift 582540
  have htrace : WordTrace (prefixWord ++ tailWord_582540) baseStart_582540 baseEnd_582540 := by
    simpa [prefixWord, tailWord_582540, baseEnd_582540] using wordTrace_append hprefix tailTrace_582540
  have hstable : (prefixWord ++ tailWord_582540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582540).length < 2 ^ (prefixWord ++ tailWord_582540).sum := by decide
  have hdescent : baseEnd_582540 < baseStart_582540 := by decide
  rcases family_descends (prefixWord ++ tailWord_582540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582560 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 7]
def baseStart_582560 : Nat := 118140960795 + 582560 * 2 ^ 59
def prefixEnd_582560 : Nat := 4983230072969 + 3 ^ 40 * 582560 * 2
def baseEnd_582560 : Nat := 299133290083345965020861

theorem tailTrace_582560 : CollatzResearch.WordTrace tailWord_582560 prefixEnd_582560 299133290083345965020861 := by
  unfold tailWord_582560
  simp only [CollatzResearch.WordTrace]
  refine ⟨10623854384746044086020567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14165139179661392114694089 10623854384746044086020567)
  ·
    refine ⟨15935781577119066129030851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10623854384746044086020567 15935781577119066129030851)
    ·
      refine ⟨23903672365678599193546277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15935781577119066129030851 23903672365678599193546277)
      ·
        refine ⟨4481938568564737348789927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23903672365678599193546277 4481938568564737348789927)
        ·
          refine ⟨6722907852847106023184891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4481938568564737348789927 6722907852847106023184891)
          ·
            refine ⟨10084361779270659034777337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6722907852847106023184891 10084361779270659034777337)
            ·
              refine ⟨7563271334452994276083003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10084361779270659034777337 7563271334452994276083003)
              ·
                refine ⟨11344907001679491414124505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7563271334452994276083003 11344907001679491414124505)
                ·
                  refine ⟨8508680251259618560593379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11344907001679491414124505 8508680251259618560593379)
                  ·
                    refine ⟨12763020376889427840890069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8508680251259618560593379 12763020376889427840890069)
                    ·
                      refine ⟨299133290083345965020861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 12763020376889427840890069 299133290083345965020861)
                      ·
                        rfl

theorem cell23_582560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_582560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582560 prefixEnd_582560 := by exact prefixLift 582560
  have htrace : WordTrace (prefixWord ++ tailWord_582560) baseStart_582560 baseEnd_582560 := by
    simpa [prefixWord, tailWord_582560, baseEnd_582560] using wordTrace_append hprefix tailTrace_582560
  have hstable : (prefixWord ++ tailWord_582560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582560).length < 2 ^ (prefixWord ++ tailWord_582560).sum := by decide
  have hdescent : baseEnd_582560 < baseStart_582560 := by decide
  rcases family_descends (prefixWord ++ tailWord_582560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582564 : List Nat := [2, 3, 1, 2, 1, 2, 1, 4, 3, 1, 3]
def baseStart_582564 : Nat := 118140960795 + 582564 * 2 ^ 59
def prefixEnd_582564 : Nat := 4983230072969 + 3 ^ 40 * 582564 * 2
def baseEnd_582564 : Nat := 299135344005963949370843

theorem tailTrace_582564 : CollatzResearch.WordTrace tailWord_582564 prefixEnd_582564 299135344005963949370843 := by
  unfold tailWord_582564
  simp only [CollatzResearch.WordTrace]
  refine ⟨10623927330738798427593373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14165236440985064570124497 10623927330738798427593373)
  ·
    refine ⟨3983972749027049410347515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10623927330738798427593373 3983972749027049410347515)
    ·
      refine ⟨5975959123540574115521273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3983972749027049410347515 5975959123540574115521273)
      ·
        refine ⟨4481969342655430586640955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5975959123540574115521273 4481969342655430586640955)
        ·
          refine ⟨6722954013983145879961433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4481969342655430586640955 6722954013983145879961433)
          ·
            refine ⟨5042215510487359409971075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6722954013983145879961433 5042215510487359409971075)
            ·
              refine ⟨7563323265731039114956613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5042215510487359409971075 7563323265731039114956613)
              ·
                refine ⟨1418123112324569834054365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7563323265731039114956613 1418123112324569834054365)
                ·
                  refine ⟨531796167121713687770387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1418123112324569834054365 531796167121713687770387)
                  ·
                    refine ⟨797694250682570531655581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 531796167121713687770387 797694250682570531655581)
                    ·
                      refine ⟨299135344005963949370843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 797694250682570531655581 299135344005963949370843)
                      ·
                        rfl

theorem cell23_582564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_582564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582564 prefixEnd_582564 := by exact prefixLift 582564
  have htrace : WordTrace (prefixWord ++ tailWord_582564) baseStart_582564 baseEnd_582564 := by
    simpa [prefixWord, tailWord_582564, baseEnd_582564] using wordTrace_append hprefix tailTrace_582564
  have hstable : (prefixWord ++ tailWord_582564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582564).length < 2 ^ (prefixWord ++ tailWord_582564).sum := by decide
  have hdescent : baseEnd_582564 < baseStart_582564 := by decide
  rcases family_descends (prefixWord ++ tailWord_582564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582587 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 4, 6, 2]
def baseStart_582587 : Nat := 118140960795 + 582587 * 2 ^ 59
def prefixEnd_582587 : Nat := 4983230072969 + 3 ^ 40 * 582587 * 2
def baseEnd_582587 : Nat := 299147154061017359383237

theorem tailTrace_582587 : CollatzResearch.WordTrace tailWord_582587 prefixEnd_582587 299147154061017359383237 := by
  unfold tailWord_582587
  simp only [CollatzResearch.WordTrace]
  refine ⟨21248693540394271783274015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14165795693596181188849343 21248693540394271783274015)
  ·
    refine ⟨31873040310591407674911023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21248693540394271783274015 31873040310591407674911023)
    ·
      refine ⟨47809560465887111512366535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31873040310591407674911023 47809560465887111512366535)
      ·
        refine ⟨71714340698830667268549803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47809560465887111512366535 71714340698830667268549803)
        ·
          refine ⟨107571511048246000902824705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71714340698830667268549803 107571511048246000902824705)
          ·
            refine ⟨80678633286184500677118529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107571511048246000902824705 80678633286184500677118529)
            ·
              refine ⟨60508974964638375507838897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80678633286184500677118529 60508974964638375507838897)
              ·
                refine ⟨45381731223478781630879173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60508974964638375507838897 45381731223478781630879173)
                ·
                  refine ⟨8509074604402271555789845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45381731223478781630879173 8509074604402271555789845)
                  ·
                    refine ⟨398862872081356479177649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8509074604402271555789845 398862872081356479177649)
                    ·
                      refine ⟨299147154061017359383237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 398862872081356479177649 299147154061017359383237)
                      ·
                        rfl

theorem cell23_582587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 6, 2].length) (baseStart_582587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582587 prefixEnd_582587 := by exact prefixLift 582587
  have htrace : WordTrace (prefixWord ++ tailWord_582587) baseStart_582587 baseEnd_582587 := by
    simpa [prefixWord, tailWord_582587, baseEnd_582587] using wordTrace_append hprefix tailTrace_582587
  have hstable : (prefixWord ++ tailWord_582587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582587).length < 2 ^ (prefixWord ++ tailWord_582587).sum := by decide
  have hdescent : baseEnd_582587 < baseStart_582587 := by decide
  rcases family_descends (prefixWord ++ tailWord_582587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582607 : List Nat := [1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 5]
def baseStart_582607 : Nat := 118140960795 + 582607 * 2 ^ 59
def prefixEnd_582607 : Nat := 4983230072969 + 3 ^ 40 * 582607 * 2
def baseEnd_582607 : Nat := 299157423674107281133145

theorem tailTrace_582607 : CollatzResearch.WordTrace tailWord_582607 prefixEnd_582607 299157423674107281133145 := by
  unfold tailWord_582607
  simp only [CollatzResearch.WordTrace]
  refine ⟨21249423000321815199002075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14166282000214543466001383 21249423000321815199002075)
  ·
    refine ⟨31874134500482722798503113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21249423000321815199002075 31874134500482722798503113)
    ·
      refine ⟨23905600875362042098877335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31874134500482722798503113 23905600875362042098877335)
      ·
        refine ⟨35858401313043063148316003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23905600875362042098877335 35858401313043063148316003)
        ·
          refine ⟨53787601969564594722474005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35858401313043063148316003 53787601969564594722474005)
          ·
            refine ⟨2521293842323340377615969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 53787601969564594722474005 2521293842323340377615969)
            ·
              refine ⟨1890970381742505283211977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2521293842323340377615969 1890970381742505283211977)
              ·
                refine ⟨1418227786306878962408983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1890970381742505283211977 1418227786306878962408983)
                ·
                  refine ⟨2127341679460318443613475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1418227786306878962408983 2127341679460318443613475)
                  ·
                    refine ⟨3191012519190477665420213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2127341679460318443613475 3191012519190477665420213)
                    ·
                      refine ⟨299157423674107281133145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3191012519190477665420213 299157423674107281133145)
                      ·
                        rfl

theorem cell23_582607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 5].length) (baseStart_582607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582607 prefixEnd_582607 := by exact prefixLift 582607
  have htrace : WordTrace (prefixWord ++ tailWord_582607) baseStart_582607 baseEnd_582607 := by
    simpa [prefixWord, tailWord_582607, baseEnd_582607] using wordTrace_append hprefix tailTrace_582607
  have hstable : (prefixWord ++ tailWord_582607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582607).length < 2 ^ (prefixWord ++ tailWord_582607).sum := by decide
  have hdescent : baseEnd_582607 < baseStart_582607 := by decide
  rcases family_descends (prefixWord ++ tailWord_582607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582617 : List Nat := [1, 2, 1, 2, 5, 1, 2, 1, 1, 1, 6]
def baseStart_582617 : Nat := 118140960795 + 582617 * 2 ^ 59
def prefixEnd_582617 : Nat := 4983230072969 + 3 ^ 40 * 582617 * 2
def baseEnd_582617 : Nat := 299162558480652242008099

theorem tailTrace_582617 : CollatzResearch.WordTrace tailWord_582617 prefixEnd_582617 299162558480652242008099 := by
  unfold tailWord_582617
  simp only [CollatzResearch.WordTrace]
  refine ⟨21249787730285586906866105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14166525153523724604577403 21249787730285586906866105)
  ·
    refine ⟨15937340797714190180149579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21249787730285586906866105 15937340797714190180149579)
    ·
      refine ⟨23906011196571285270224369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15937340797714190180149579 23906011196571285270224369)
      ·
        refine ⟨17929508397428463952668277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23906011196571285270224369 17929508397428463952668277)
        ·
          refine ⟨1680891412258918495562651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17929508397428463952668277 1680891412258918495562651)
          ·
            refine ⟨2521337118388377743343977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1680891412258918495562651 2521337118388377743343977)
            ·
              refine ⟨1891002838791283307507983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2521337118388377743343977 1891002838791283307507983)
              ·
                refine ⟨2836504258186924961261975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1891002838791283307507983 2836504258186924961261975)
                ·
                  refine ⟨4254756387280387441892963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2836504258186924961261975 4254756387280387441892963)
                  ·
                    refine ⟨6382134580920581162839445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4254756387280387441892963 6382134580920581162839445)
                    ·
                      refine ⟨299162558480652242008099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6382134580920581162839445 299162558480652242008099)
                      ·
                        rfl

theorem cell23_582617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_582617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582617 prefixEnd_582617 := by exact prefixLift 582617
  have htrace : WordTrace (prefixWord ++ tailWord_582617) baseStart_582617 baseEnd_582617 := by
    simpa [prefixWord, tailWord_582617, baseEnd_582617] using wordTrace_append hprefix tailTrace_582617
  have hstable : (prefixWord ++ tailWord_582617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582617).length < 2 ^ (prefixWord ++ tailWord_582617).sum := by decide
  have hdescent : baseEnd_582617 < baseStart_582617 := by decide
  rcases family_descends (prefixWord ++ tailWord_582617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582621 : List Nat := [1, 4, 3, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_582621 : Nat := 118140960795 + 582621 * 2 ^ 59
def prefixEnd_582621 : Nat := 4983230072969 + 3 ^ 40 * 582621 * 2
def baseEnd_582621 : Nat := 299164612403270226358081

theorem tailTrace_582621 : CollatzResearch.WordTrace tailWord_582621 prefixEnd_582621 299164612403270226358081 := by
  unfold tailWord_582621
  simp only [CollatzResearch.WordTrace]
  refine ⟨21249933622271095590011717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14166622414847397060007811 21249933622271095590011717)
  ·
    refine ⟨3984362554175830423127197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21249933622271095590011717 3984362554175830423127197)
    ·
      refine ⟨1494135957815936408672699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3984362554175830423127197 1494135957815936408672699)
      ·
        refine ⟨2241203936723904613009049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1494135957815936408672699 2241203936723904613009049)
        ·
          refine ⟨1680902952542928459756787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2241203936723904613009049 1680902952542928459756787)
          ·
            refine ⟨2521354428814392689635181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1680902952542928459756787 2521354428814392689635181)
            ·
              refine ⟨945507910805397258613193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2521354428814392689635181 945507910805397258613193)
              ·
                refine ⟨709130933104047943959895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 945507910805397258613193 709130933104047943959895)
                ·
                  refine ⟨1063696399656071915939843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 709130933104047943959895 1063696399656071915939843)
                  ·
                    refine ⟨1595544599484107873909765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1063696399656071915939843 1595544599484107873909765)
                    ·
                      refine ⟨299164612403270226358081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1595544599484107873909765 299164612403270226358081)
                      ·
                        rfl

theorem cell23_582621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_582621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582621 prefixEnd_582621 := by exact prefixLift 582621
  have htrace : WordTrace (prefixWord ++ tailWord_582621) baseStart_582621 baseEnd_582621 := by
    simpa [prefixWord, tailWord_582621, baseEnd_582621] using wordTrace_append hprefix tailTrace_582621
  have hstable : (prefixWord ++ tailWord_582621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582621).length < 2 ^ (prefixWord ++ tailWord_582621).sum := by decide
  have hdescent : baseEnd_582621 < baseStart_582621 := by decide
  rcases family_descends (prefixWord ++ tailWord_582621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582634 : List Nat := [3, 1, 3, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_582634 : Nat := 118140960795 + 582634 * 2 ^ 59
def prefixEnd_582634 : Nat := 4983230072969 + 3 ^ 40 * 582634 * 2
def baseEnd_582634 : Nat := 299171287651778675495521

theorem tailTrace_582634 : CollatzResearch.WordTrace tailWord_582634 prefixEnd_582634 299171287651778675495521 := by
  unfold tailWord_582634
  simp only [CollatzResearch.WordTrace]
  refine ⟨5312601942805999702558739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14166938514149332540156637 5312601942805999702558739)
  ·
    refine ⟨7968902914208999553838109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5312601942805999702558739 7968902914208999553838109)
    ·
      refine ⟨2988338592828374832689291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7968902914208999553838109 2988338592828374832689291)
      ·
        refine ⟨4482507889242562249033937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2988338592828374832689291 4482507889242562249033937)
        ·
          refine ⟨3361880916931921686775453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4482507889242562249033937 3361880916931921686775453)
          ·
            refine ⟨1260705343849470632540795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3361880916931921686775453 1260705343849470632540795)
            ·
              refine ⟨1891058015774205948811193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1260705343849470632540795 1891058015774205948811193)
              ·
                refine ⟨1418293511830654461608395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1891058015774205948811193 1418293511830654461608395)
                ·
                  refine ⟨2127440267745981692412593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1418293511830654461608395 2127440267745981692412593)
                  ·
                    refine ⟨1595580200809486269309445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2127440267745981692412593 1595580200809486269309445)
                    ·
                      refine ⟨299171287651778675495521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1595580200809486269309445 299171287651778675495521)
                      ·
                        rfl

theorem cell23_582634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_582634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582634 prefixEnd_582634 := by exact prefixLift 582634
  have htrace : WordTrace (prefixWord ++ tailWord_582634) baseStart_582634 baseEnd_582634 := by
    simpa [prefixWord, tailWord_582634, baseEnd_582634] using wordTrace_append hprefix tailTrace_582634
  have hstable : (prefixWord ++ tailWord_582634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582634).length < 2 ^ (prefixWord ++ tailWord_582634).sum := by decide
  have hdescent : baseEnd_582634 < baseStart_582634 := by decide
  rcases family_descends (prefixWord ++ tailWord_582634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582638 : List Nat := [4, 1, 2, 1, 4, 1, 3, 1, 1, 1, 4]
def baseStart_582638 : Nat := 118140960795 + 582638 * 2 ^ 59
def prefixEnd_582638 : Nat := 4983230072969 + 3 ^ 40 * 582638 * 2
def baseEnd_582638 : Nat := 299173341574396659845503

theorem tailTrace_582638 : CollatzResearch.WordTrace tailWord_582638 prefixEnd_582638 299173341574396659845503 := by
  unfold tailWord_582638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2656319207901188436672571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14167035775473004995587045 2656319207901188436672571)
  ·
    refine ⟨3984478811851782655008857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2656319207901188436672571 3984478811851782655008857)
    ·
      refine ⟨2988359108888836991256643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3984478811851782655008857 2988359108888836991256643)
      ·
        refine ⟨4482538663333255486884965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2988359108888836991256643 4482538663333255486884965)
        ·
          refine ⟨840475999374985403790931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4482538663333255486884965 840475999374985403790931)
          ·
            refine ⟨1260713999062478105686397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 840475999374985403790931 1260713999062478105686397)
            ·
              refine ⟨472767749648429289632399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1260713999062478105686397 472767749648429289632399)
              ·
                refine ⟨709151624472643934448599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 472767749648429289632399 709151624472643934448599)
                ·
                  refine ⟨1063727436708965901672899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 709151624472643934448599 1063727436708965901672899)
                  ·
                    refine ⟨1595591155063448852509349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1063727436708965901672899 1595591155063448852509349)
                    ·
                      refine ⟨299173341574396659845503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1595591155063448852509349 299173341574396659845503)
                      ·
                        rfl

theorem cell23_582638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_582638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582638 prefixEnd_582638 := by exact prefixLift 582638
  have htrace : WordTrace (prefixWord ++ tailWord_582638) baseStart_582638 baseEnd_582638 := by
    simpa [prefixWord, tailWord_582638, baseEnd_582638] using wordTrace_append hprefix tailTrace_582638
  have hstable : (prefixWord ++ tailWord_582638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582638).length < 2 ^ (prefixWord ++ tailWord_582638).sum := by decide
  have hdescent : baseEnd_582638 < baseStart_582638 := by decide
  rcases family_descends (prefixWord ++ tailWord_582638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582657 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 2, 7]
def baseStart_582657 : Nat := 118140960795 + 582657 * 2 ^ 59
def prefixEnd_582657 : Nat := 4983230072969 + 3 ^ 40 * 582657 * 2
def baseEnd_582657 : Nat := 99727699235610695169305

theorem tailTrace_582657 : CollatzResearch.WordTrace tailWord_582657 prefixEnd_582657 99727699235610695169305 := by
  unfold tailWord_582657
  simp only [CollatzResearch.WordTrace]
  refine ⟨21251246650140673738322225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14167497766760449158881483 21251246650140673738322225)
  ·
    refine ⟨15938434987605505303741669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21251246650140673738322225 15938434987605505303741669)
    ·
      refine ⟨2988456560176032244451563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15938434987605505303741669 2988456560176032244451563)
      ·
        refine ⟨4482684840264048366677345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2988456560176032244451563 4482684840264048366677345)
        ·
          refine ⟨3362013630198036275008009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4482684840264048366677345 3362013630198036275008009)
          ·
            refine ⟨2521510222648527206256007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3362013630198036275008009 2521510222648527206256007)
            ·
              refine ⟨3782265333972790809384011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2521510222648527206256007 3782265333972790809384011)
              ·
                refine ⟨5673398000959186214076017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3782265333972790809384011 5673398000959186214076017)
                ·
                  refine ⟨4255048500719389660557013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5673398000959186214076017 4255048500719389660557013)
                  ·
                    refine ⟨99727699235610695169305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4255048500719389660557013 99727699235610695169305)
                    ·
                      rfl

theorem cell23_582657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_582657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582657 prefixEnd_582657 := by exact prefixLift 582657
  have htrace : WordTrace (prefixWord ++ tailWord_582657) baseStart_582657 baseEnd_582657 := by
    simpa [prefixWord, tailWord_582657, baseEnd_582657] using wordTrace_append hprefix tailTrace_582657
  have hstable : (prefixWord ++ tailWord_582657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582657).length < 2 ^ (prefixWord ++ tailWord_582657).sum := by decide
  have hdescent : baseEnd_582657 < baseStart_582657 := by decide
  rcases family_descends (prefixWord ++ tailWord_582657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582764 : List Nat := [2, 2, 1, 1, 3, 2, 3, 2, 2, 5]
def baseStart_582764 : Nat := 118140960795 + 582764 * 2 ^ 59
def prefixEnd_582764 : Nat := 4983230072969 + 3 ^ 40 * 582764 * 2
def baseEnd_582764 : Nat := 99746013378954388956641

theorem tailTrace_582764 : CollatzResearch.WordTrace tailWord_582764 prefixEnd_582764 99746013378954388956641 := by
  unfold tailWord_582764
  simp only [CollatzResearch.WordTrace]
  refine ⟨10627574630376515506233673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14170099507168687341644897 10627574630376515506233673)
  ·
    refine ⟨7970680972782386629675255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10627574630376515506233673 7970680972782386629675255)
    ·
      refine ⟨11956021459173579944512883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7970680972782386629675255 11956021459173579944512883)
      ·
        refine ⟨17934032188760369916769325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11956021459173579944512883 17934032188760369916769325)
        ·
          refine ⟨6725262070785138718788497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17934032188760369916769325 6725262070785138718788497)
          ·
            refine ⟨5043946553088854039091373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6725262070785138718788497 5043946553088854039091373)
            ·
              refine ⟨1891479957408320264659265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5043946553088854039091373 1891479957408320264659265)
              ·
                refine ⟨1418609968056240198494449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1891479957408320264659265 1418609968056240198494449)
                ·
                  refine ⟨1063957476042180148870837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1418609968056240198494449 1063957476042180148870837)
                  ·
                    refine ⟨99746013378954388956641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1063957476042180148870837 99746013378954388956641)
                    ·
                      rfl

theorem cell23_582764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 5].length) (baseStart_582764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582764 prefixEnd_582764 := by exact prefixLift 582764
  have htrace : WordTrace (prefixWord ++ tailWord_582764) baseStart_582764 baseEnd_582764 := by
    simpa [prefixWord, tailWord_582764, baseEnd_582764] using wordTrace_append hprefix tailTrace_582764
  have hstable : (prefixWord ++ tailWord_582764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582764).length < 2 ^ (prefixWord ++ tailWord_582764).sum := by decide
  have hdescent : baseEnd_582764 < baseStart_582764 := by decide
  rcases family_descends (prefixWord ++ tailWord_582764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582821 : List Nat := [1, 3, 1, 2, 1, 4, 2, 2, 2, 2, 3]
def baseStart_582821 : Nat := 118140960795 + 582821 * 2 ^ 59
def prefixEnd_582821 : Nat := 4983230072969 + 3 ^ 40 * 582821 * 2
def baseEnd_582821 : Nat := 299267308534169443857161

theorem tailTrace_582821 : CollatzResearch.WordTrace tailWord_582821 prefixEnd_582821 299267308534169443857161 := by
  unfold tailWord_582821
  simp only [CollatzResearch.WordTrace]
  refine ⟨21257228221546529747292317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14171485481031019831528211 21257228221546529747292317)
  ·
    refine ⟨7971460583079948655234619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21257228221546529747292317 7971460583079948655234619)
    ·
      refine ⟨11957190874619922982851929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7971460583079948655234619 11957190874619922982851929)
      ·
        refine ⟨8967893155964942237138947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11957190874619922982851929 8967893155964942237138947)
        ·
          refine ⟨13451839733947413355708421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8967893155964942237138947 13451839733947413355708421)
          ·
            refine ⟨2522219950115140004195329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13451839733947413355708421 2522219950115140004195329)
            ·
              refine ⟨1891664962586355003146497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2522219950115140004195329 1891664962586355003146497)
              ·
                refine ⟨1418748721939766252359873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1891664962586355003146497 1418748721939766252359873)
                ·
                  refine ⟨1064061541454824689269905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1418748721939766252359873 1064061541454824689269905)
                  ·
                    refine ⟨798046156091118516952429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1064061541454824689269905 798046156091118516952429)
                    ·
                      refine ⟨299267308534169443857161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 798046156091118516952429 299267308534169443857161)
                      ·
                        rfl

theorem cell23_582821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_582821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582821 prefixEnd_582821 := by exact prefixLift 582821
  have htrace : WordTrace (prefixWord ++ tailWord_582821) baseStart_582821 baseEnd_582821 := by
    simpa [prefixWord, tailWord_582821, baseEnd_582821] using wordTrace_append hprefix tailTrace_582821
  have hstable : (prefixWord ++ tailWord_582821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582821).length < 2 ^ (prefixWord ++ tailWord_582821).sum := by decide
  have hdescent : baseEnd_582821 < baseStart_582821 := by decide
  rcases family_descends (prefixWord ++ tailWord_582821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582884 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 3, 6]
def baseStart_582884 : Nat := 118140960795 + 582884 * 2 ^ 59
def prefixEnd_582884 : Nat := 4983230072969 + 3 ^ 40 * 582884 * 2
def baseEnd_582884 : Nat := 99766552605134232456457

theorem tailTrace_582884 : CollatzResearch.WordTrace tailWord_582884 prefixEnd_582884 99766552605134232456457 := by
  unfold tailWord_582884
  simp only [CollatzResearch.WordTrace]
  refine ⟨10629763010159145753417853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14173017346878861004557137 10629763010159145753417853)
  ·
    refine ⟨3986161128809679657531695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10629763010159145753417853 3986161128809679657531695)
    ·
      refine ⟨5979241693214519486297543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3986161128809679657531695 5979241693214519486297543)
      ·
        refine ⟨8968862539821779229446315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5979241693214519486297543 8968862539821779229446315)
        ·
          refine ⟨13453293809732668844169473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8968862539821779229446315 13453293809732668844169473)
          ·
            refine ⟨10089970357299501633127105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13453293809732668844169473 10089970357299501633127105)
            ·
              refine ⟨7567477767974626224845329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10089970357299501633127105 7567477767974626224845329)
              ·
                refine ⟨5675608325980969668633997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7567477767974626224845329 5675608325980969668633997)
                ·
                  refine ⟨2128353122242863625737749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5675608325980969668633997 2128353122242863625737749)
                  ·
                    refine ⟨99766552605134232456457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2128353122242863625737749 99766552605134232456457)
                    ·
                      rfl

theorem cell23_582884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_582884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582884 prefixEnd_582884 := by exact prefixLift 582884
  have htrace : WordTrace (prefixWord ++ tailWord_582884) baseStart_582884 baseEnd_582884 := by
    simpa [prefixWord, tailWord_582884, baseEnd_582884] using wordTrace_append hprefix tailTrace_582884
  have hstable : (prefixWord ++ tailWord_582884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582884).length < 2 ^ (prefixWord ++ tailWord_582884).sum := by decide
  have hdescent : baseEnd_582884 < baseStart_582884 := by decide
  rcases family_descends (prefixWord ++ tailWord_582884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582885 : List Nat := [1, 3, 1, 4, 3, 1, 2, 1, 3, 1, 3]
def baseStart_582885 : Nat := 118140960795 + 582885 * 2 ^ 59
def prefixEnd_582885 : Nat := 4983230072969 + 3 ^ 40 * 582885 * 2
def baseEnd_582885 : Nat := 299300171296057193456867

theorem tailTrace_582885 : CollatzResearch.WordTrace tailWord_582885 prefixEnd_582885 299300171296057193456867 := by
  unfold tailWord_582885
  simp only [CollatzResearch.WordTrace]
  refine ⟨21259562493314668677622109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14173041662209779118414739 21259562493314668677622109)
  ·
    refine ⟨7972335934993000754108291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21259562493314668677622109 7972335934993000754108291)
    ·
      refine ⟨11958503902489501131162437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7972335934993000754108291 11958503902489501131162437)
      ·
        refine ⟨2242219481716781462092957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11958503902489501131162437 2242219481716781462092957)
        ·
          refine ⟨840832305643793048284859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2242219481716781462092957 840832305643793048284859)
          ·
            refine ⟨1261248458465689572427289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 840832305643793048284859 1261248458465689572427289)
            ·
              refine ⟨945936343849267179320467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1261248458465689572427289 945936343849267179320467)
              ·
                refine ⟨1418904515773900768980701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 945936343849267179320467 1418904515773900768980701)
                ·
                  refine ⟨532089193415212788367763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1418904515773900768980701 532089193415212788367763)
                  ·
                    refine ⟨798133790122819182551645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 532089193415212788367763 798133790122819182551645)
                    ·
                      refine ⟨299300171296057193456867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 798133790122819182551645 299300171296057193456867)
                      ·
                        rfl

theorem cell23_582885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_582885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582885 prefixEnd_582885 := by exact prefixLift 582885
  have htrace : WordTrace (prefixWord ++ tailWord_582885) baseStart_582885 baseEnd_582885 := by
    simpa [prefixWord, tailWord_582885, baseEnd_582885] using wordTrace_append hprefix tailTrace_582885
  have hstable : (prefixWord ++ tailWord_582885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582885).length < 2 ^ (prefixWord ++ tailWord_582885).sum := by decide
  have hdescent : baseEnd_582885 < baseStart_582885 := by decide
  rcases family_descends (prefixWord ++ tailWord_582885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582952 : List Nat := [2, 1, 5, 1, 2, 3, 2, 1, 2, 4]
def baseStart_582952 : Nat := 118140960795 + 582952 * 2 ^ 59
def prefixEnd_582952 : Nat := 4983230072969 + 3 ^ 40 * 582952 * 2
def baseEnd_582952 : Nat := 99778191499969477106353

theorem tailTrace_582952 : CollatzResearch.WordTrace tailWord_582952 prefixEnd_582952 99778191499969477106353 := by
  unfold tailWord_582952
  simp only [CollatzResearch.WordTrace]
  refine ⟨10631003092035969560155555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14174670789381292746874073 10631003092035969560155555)
  ·
    refine ⟨15946504638053954340233333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10631003092035969560155555 15946504638053954340233333)
    ·
      refine ⟨1494984809817558219396875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15946504638053954340233333 1494984809817558219396875)
      ·
        refine ⟨2242477214726337329095313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1494984809817558219396875 2242477214726337329095313)
        ·
          refine ⟨1681857911044752996821485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2242477214726337329095313 1681857911044752996821485)
          ·
            refine ⟨630696716641782373808057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1681857911044752996821485 630696716641782373808057)
            ·
              refine ⟨473022537481336780356043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 630696716641782373808057 473022537481336780356043)
              ·
                refine ⟨709533806222005170534065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 473022537481336780356043 709533806222005170534065)
                ·
                  refine ⟨532150354666503877900549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 709533806222005170534065 532150354666503877900549)
                  ·
                    refine ⟨99778191499969477106353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 532150354666503877900549 99778191499969477106353)
                    ·
                      rfl

theorem cell23_582952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_582952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_582952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_582952 prefixEnd_582952 := by exact prefixLift 582952
  have htrace : WordTrace (prefixWord ++ tailWord_582952) baseStart_582952 baseEnd_582952 := by
    simpa [prefixWord, tailWord_582952, baseEnd_582952] using wordTrace_append hprefix tailTrace_582952
  have hstable : (prefixWord ++ tailWord_582952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582952).length < 2 ^ (prefixWord ++ tailWord_582952).sum := by decide
  have hdescent : baseEnd_582952 < baseStart_582952 := by decide
  rcases family_descends (prefixWord ++ tailWord_582952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583001 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 2, 4, 3]
def baseStart_583001 : Nat := 118140960795 + 583001 * 2 ^ 59
def prefixEnd_583001 : Nat := 4983230072969 + 3 ^ 40 * 583001 * 2
def baseEnd_583001 : Nat := 299359735051978739606333

theorem tailTrace_583001 : CollatzResearch.WordTrace tailWord_583001 prefixEnd_583001 299359735051978739606333 := by
  unfold tailWord_583001
  simp only [CollatzResearch.WordTrace]
  refine ⟨21263793360894420488844857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14175862240596280325896571 21263793360894420488844857)
  ·
    refine ⟨15947845020670815366633643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21263793360894420488844857 15947845020670815366633643)
    ·
      refine ⟨23921767531006223049950465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15947845020670815366633643 23921767531006223049950465)
      ·
        refine ⟨17941325648254667287462849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23921767531006223049950465 17941325648254667287462849)
        ·
          refine ⟨13455994236191000465597137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17941325648254667287462849 13455994236191000465597137)
          ·
            refine ⟨10091995677143250349197853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13455994236191000465597137 10091995677143250349197853)
            ·
              refine ⟨3784498378928718880949195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10091995677143250349197853 3784498378928718880949195)
              ·
                refine ⟨5676747568393078321423793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3784498378928718880949195 5676747568393078321423793)
                ·
                  refine ⟨4257560676294808741067845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5676747568393078321423793 4257560676294808741067845)
                  ·
                    refine ⟨798292626805276638950221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4257560676294808741067845 798292626805276638950221)
                    ·
                      refine ⟨299359735051978739606333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 798292626805276638950221 299359735051978739606333)
                      ·
                        rfl

theorem cell23_583001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 4, 3].length) (baseStart_583001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583001 prefixEnd_583001 := by exact prefixLift 583001
  have htrace : WordTrace (prefixWord ++ tailWord_583001) baseStart_583001 baseEnd_583001 := by
    simpa [prefixWord, tailWord_583001, baseEnd_583001] using wordTrace_append hprefix tailTrace_583001
  have hstable : (prefixWord ++ tailWord_583001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583001).length < 2 ^ (prefixWord ++ tailWord_583001).sum := by decide
  have hdescent : baseEnd_583001 < baseStart_583001 := by decide
  rcases family_descends (prefixWord ++ tailWord_583001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583011 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 4]
def baseStart_583011 : Nat := 118140960795 + 583011 * 2 ^ 59
def prefixEnd_583011 : Nat := 4983230072969 + 3 ^ 40 * 583011 * 2
def baseEnd_583011 : Nat := 299364869858523700481287

theorem tailTrace_583011 : CollatzResearch.WordTrace tailWord_583011 prefixEnd_583011 299364869858523700481287 := by
  unfold tailWord_583011
  simp only [CollatzResearch.WordTrace]
  refine ⟨21264158090858192196708887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14176105393905461464472591 21264158090858192196708887)
  ·
    refine ⟨31896237136287288295063331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21264158090858192196708887 31896237136287288295063331)
    ·
      refine ⟨47844355704430932442594997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31896237136287288295063331 47844355704430932442594997)
      ·
        refine ⟨4485408347290399916493281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47844355704430932442594997 4485408347290399916493281)
        ·
          refine ⟨3364056260467799937369961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4485408347290399916493281 3364056260467799937369961)
          ·
            refine ⟨2523042195350849953027471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3364056260467799937369961 2523042195350849953027471)
            ·
              refine ⟨3784563293026274929541207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2523042195350849953027471 3784563293026274929541207)
              ·
                refine ⟨5676844939539412394311811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3784563293026274929541207 5676844939539412394311811)
                ·
                  refine ⟨8515267409309118591467717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5676844939539412394311811 8515267409309118591467717)
                  ·
                    refine ⟨1596612639245459735900197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8515267409309118591467717 1596612639245459735900197)
                    ·
                      refine ⟨299364869858523700481287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1596612639245459735900197 299364869858523700481287)
                      ·
                        rfl

theorem cell23_583011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_583011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583011 prefixEnd_583011 := by exact prefixLift 583011
  have htrace : WordTrace (prefixWord ++ tailWord_583011) baseStart_583011 baseEnd_583011 := by
    simpa [prefixWord, tailWord_583011, baseEnd_583011] using wordTrace_append hprefix tailTrace_583011
  have hstable : (prefixWord ++ tailWord_583011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583011).length < 2 ^ (prefixWord ++ tailWord_583011).sum := by decide
  have hdescent : baseEnd_583011 < baseStart_583011 := by decide
  rcases family_descends (prefixWord ++ tailWord_583011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583021 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 9]
def baseStart_583021 : Nat := 118140960795 + 583021 * 2 ^ 59
def prefixEnd_583021 : Nat := 4983230072969 + 3 ^ 40 * 583021 * 2
def baseEnd_583021 : Nat := 33263333851674295706249

theorem tailTrace_583021 : CollatzResearch.WordTrace tailWord_583021 prefixEnd_583021 33263333851674295706249 := by
  unfold tailWord_583021
  simp only [CollatzResearch.WordTrace]
  refine ⟨21264522820821963904572917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14176348547214642603048611 21264522820821963904572917)
  ·
    refine ⟨1993549014452059116053711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21264522820821963904572917 1993549014452059116053711)
    ·
      refine ⟨2990323521678088674080567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1993549014452059116053711 2990323521678088674080567)
      ·
        refine ⟨4485485282517133011120851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2990323521678088674080567 4485485282517133011120851)
        ·
          refine ⟨6728227923775699516681277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4485485282517133011120851 6728227923775699516681277)
          ·
            refine ⟨2523085471415887318755479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6728227923775699516681277 2523085471415887318755479)
            ·
              refine ⟨3784628207123830978133219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2523085471415887318755479 3784628207123830978133219)
              ·
                refine ⟨5676942310685746467199829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3784628207123830978133219 5676942310685746467199829)
                ·
                  refine ⟨33263333851674295706249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5676942310685746467199829 33263333851674295706249)
                  ·
                    rfl

theorem cell23_583021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_583021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583021 prefixEnd_583021 := by exact prefixLift 583021
  have htrace : WordTrace (prefixWord ++ tailWord_583021) baseStart_583021 baseEnd_583021 := by
    simpa [prefixWord, tailWord_583021, baseEnd_583021] using wordTrace_append hprefix tailTrace_583021
  have hstable : (prefixWord ++ tailWord_583021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583021).length < 2 ^ (prefixWord ++ tailWord_583021).sum := by decide
  have hdescent : baseEnd_583021 < baseStart_583021 := by decide
  rcases family_descends (prefixWord ++ tailWord_583021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583031 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 3]
def baseStart_583031 : Nat := 118140960795 + 583031 * 2 ^ 59
def prefixEnd_583031 : Nat := 4983230072969 + 3 ^ 40 * 583031 * 2
def baseEnd_583031 : Nat := 299375139471613622231195

theorem tailTrace_583031 : CollatzResearch.WordTrace tailWord_583031 prefixEnd_583031 299375139471613622231195 := by
  unfold tailWord_583031
  simp only [CollatzResearch.WordTrace]
  refine ⟨21264887550785735612436947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14176591700523823741624631 21264887550785735612436947)
  ·
    refine ⟨31897331326178603418655421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21264887550785735612436947 31897331326178603418655421)
    ·
      refine ⟨11961499247316976281995783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31897331326178603418655421 11961499247316976281995783)
      ·
        refine ⟨17942248870975464422993675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11961499247316976281995783 17942248870975464422993675)
        ·
          refine ⟨26913373306463196634490513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17942248870975464422993675 26913373306463196634490513)
          ·
            refine ⟨20185029979847397475867885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26913373306463196634490513 20185029979847397475867885)
            ·
              refine ⟨7569386242442774053450457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20185029979847397475867885 7569386242442774053450457)
              ·
                refine ⟨5677039681832080540087843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7569386242442774053450457 5677039681832080540087843)
                ·
                  refine ⟨8515559522748120810131765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5677039681832080540087843 8515559522748120810131765)
                  ·
                    refine ⟨798333705257636325949853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8515559522748120810131765 798333705257636325949853)
                    ·
                      refine ⟨299375139471613622231195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 798333705257636325949853 299375139471613622231195)
                      ·
                        rfl

theorem cell23_583031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 3].length) (baseStart_583031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583031 prefixEnd_583031 := by exact prefixLift 583031
  have htrace : WordTrace (prefixWord ++ tailWord_583031) baseStart_583031 baseEnd_583031 := by
    simpa [prefixWord, tailWord_583031, baseEnd_583031] using wordTrace_append hprefix tailTrace_583031
  have hstable : (prefixWord ++ tailWord_583031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583031).length < 2 ^ (prefixWord ++ tailWord_583031).sum := by decide
  have hdescent : baseEnd_583031 < baseStart_583031 := by decide
  rcases family_descends (prefixWord ++ tailWord_583031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583048 : List Nat := [2, 1, 3, 3, 1, 2, 1, 2, 2, 3, 3]
def baseStart_583048 : Nat := 118140960795 + 583048 * 2 ^ 59
def prefixEnd_583048 : Nat := 4983230072969 + 3 ^ 40 * 583048 * 2
def baseEnd_583048 : Nat := 299383868642740055718617

theorem tailTrace_583048 : CollatzResearch.WordTrace tailWord_583048 prefixEnd_583048 299383868642740055718617 := by
  unfold tailWord_583048
  simp only [CollatzResearch.WordTrace]
  refine ⟨10632753795862073757902899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14177005061149431677203865 10632753795862073757902899)
  ·
    refine ⟨15949130693793110636854349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10632753795862073757902899 15949130693793110636854349)
    ·
      refine ⟨5980924010172416488820381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15949130693793110636854349 5980924010172416488820381)
      ·
        refine ⟨2242846503814656183307643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5980924010172416488820381 2242846503814656183307643)
        ·
          refine ⟨3364269755721984274961465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2242846503814656183307643 3364269755721984274961465)
          ·
            refine ⟨2523202316791488206221099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3364269755721984274961465 2523202316791488206221099)
            ·
              refine ⟨3784803475187232309331649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2523202316791488206221099 3784803475187232309331649)
              ·
                refine ⟨2838602606390424231998737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3784803475187232309331649 2838602606390424231998737)
                ·
                  refine ⟨2128951954792818173999053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2838602606390424231998737 2128951954792818173999053)
                  ·
                    refine ⟨798356983047306815249645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2128951954792818173999053 798356983047306815249645)
                    ·
                      refine ⟨299383868642740055718617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 798356983047306815249645 299383868642740055718617)
                      ·
                        rfl

theorem cell23_583048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_583048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583048 prefixEnd_583048 := by exact prefixLift 583048
  have htrace : WordTrace (prefixWord ++ tailWord_583048) baseStart_583048 baseEnd_583048 := by
    simpa [prefixWord, tailWord_583048, baseEnd_583048] using wordTrace_append hprefix tailTrace_583048
  have hstable : (prefixWord ++ tailWord_583048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583048).length < 2 ^ (prefixWord ++ tailWord_583048).sum := by decide
  have hdescent : baseEnd_583048 < baseStart_583048 := by decide
  rcases family_descends (prefixWord ++ tailWord_583048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583049 : List Nat := [1, 2, 1, 1, 7, 2, 1, 2, 2, 2, 2]
def baseStart_583049 : Nat := 118140960795 + 583049 * 2 ^ 59
def prefixEnd_583049 : Nat := 4983230072969 + 3 ^ 40 * 583049 * 2
def baseEnd_583049 : Nat := 299384382123394551806113

theorem tailTrace_583049 : CollatzResearch.WordTrace tailWord_583049 prefixEnd_583049 299384382123394551806113 := by
  unfold tailWord_583049
  simp only [CollatzResearch.WordTrace]
  refine ⟨21265544064720524686592201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14177029376480349791061467 21265544064720524686592201)
  ·
    refine ⟨15949158048540393514944151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21265544064720524686592201 15949158048540393514944151)
    ·
      refine ⟨23923737072810590272416227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15949158048540393514944151 23923737072810590272416227)
      ·
        refine ⟨35885605609215885408624341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23923737072810590272416227 35885605609215885408624341)
        ·
          refine ⟨841068881465997314264633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 35885605609215885408624341 841068881465997314264633)
          ·
            refine ⟨630801661099497985698475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 841068881465997314264633 630801661099497985698475)
            ·
              refine ⟨946202491649246978547713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 630801661099497985698475 946202491649246978547713)
              ·
                refine ⟨709651868736935233910785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 946202491649246978547713 709651868736935233910785)
                ·
                  refine ⟨532238901552701425433089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 709651868736935233910785 532238901552701425433089)
                  ·
                    refine ⟨399179176164526069074817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 532238901552701425433089 399179176164526069074817)
                    ·
                      refine ⟨299384382123394551806113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 399179176164526069074817 299384382123394551806113)
                      ·
                        rfl

theorem cell23_583049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 2, 2].length) (baseStart_583049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583049 prefixEnd_583049 := by exact prefixLift 583049
  have htrace : WordTrace (prefixWord ++ tailWord_583049) baseStart_583049 baseEnd_583049 := by
    simpa [prefixWord, tailWord_583049, baseEnd_583049] using wordTrace_append hprefix tailTrace_583049
  have hstable : (prefixWord ++ tailWord_583049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583049).length < 2 ^ (prefixWord ++ tailWord_583049).sum := by decide
  have hdescent : baseEnd_583049 < baseStart_583049 := by decide
  rcases family_descends (prefixWord ++ tailWord_583049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583051 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 4, 5]
def baseStart_583051 : Nat := 118140960795 + 583051 * 2 ^ 59
def prefixEnd_583051 : Nat := 4983230072969 + 3 ^ 40 * 583051 * 2
def baseEnd_583051 : Nat := 99795136361567847993701

theorem tailTrace_583051 : CollatzResearch.WordTrace tailWord_583051 prefixEnd_583051 99795136361567847993701 := by
  unfold tailWord_583051
  simp only [CollatzResearch.WordTrace]
  refine ⟨21265617010713279028165007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14177078007142186018776671 21265617010713279028165007)
  ·
    refine ⟨31898425516069918542247511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21265617010713279028165007 31898425516069918542247511)
    ·
      refine ⟨47847638274104877813371267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31898425516069918542247511 47847638274104877813371267)
      ·
        refine ⟨71771457411157316720056901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47847638274104877813371267 71771457411157316720056901)
        ·
          refine ⟨13457148264591996885010669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71771457411157316720056901 13457148264591996885010669)
          ·
            refine ⟨5046430599221998831879001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13457148264591996885010669 5046430599221998831879001)
            ·
              refine ⟨3784822949416499123909251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5046430599221998831879001 3784822949416499123909251)
              ·
                refine ⟨5677234424124748685863877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3784822949416499123909251 5677234424124748685863877)
                ·
                  refine ⟨1064481454523390378599477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5677234424124748685863877 1064481454523390378599477)
                  ·
                    refine ⟨99795136361567847993701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1064481454523390378599477 99795136361567847993701)
                    ·
                      rfl

theorem cell23_583051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 5].length) (baseStart_583051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583051 prefixEnd_583051 := by exact prefixLift 583051
  have htrace : WordTrace (prefixWord ++ tailWord_583051) baseStart_583051 baseEnd_583051 := by
    simpa [prefixWord, tailWord_583051, baseEnd_583051] using wordTrace_append hprefix tailTrace_583051
  have hstable : (prefixWord ++ tailWord_583051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583051).length < 2 ^ (prefixWord ++ tailWord_583051).sum := by decide
  have hdescent : baseEnd_583051 < baseStart_583051 := by decide
  rcases family_descends (prefixWord ++ tailWord_583051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583061 : List Nat := [1, 3, 2, 1, 1, 2, 2, 3, 1, 2, 5]
def baseStart_583061 : Nat := 118140960795 + 583061 * 2 ^ 59
def prefixEnd_583061 : Nat := 4983230072969 + 3 ^ 40 * 583061 * 2
def baseEnd_583061 : Nat := 299390543891248504856057

theorem tailTrace_583061 : CollatzResearch.WordTrace tailWord_583061 prefixEnd_583061 299390543891248504856057 := by
  unfold tailWord_583061
  simp only [CollatzResearch.WordTrace]
  refine ⟨21265981740677050736029037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14177321160451367157352691 21265981740677050736029037)
  ·
    refine ⟨7974743152753894026010889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21265981740677050736029037 7974743152753894026010889)
    ·
      refine ⟨5981057364565420519508167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7974743152753894026010889 5981057364565420519508167)
      ·
        refine ⟨8971586046848130779262251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5981057364565420519508167 8971586046848130779262251)
        ·
          refine ⟨13457379070272196168893377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8971586046848130779262251 13457379070272196168893377)
          ·
            refine ⟨10093034302704147126670033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13457379070272196168893377 10093034302704147126670033)
            ·
              refine ⟨7569775727028110345002525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10093034302704147126670033 7569775727028110345002525)
              ·
                refine ⟨2838665897635541379375947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7569775727028110345002525 2838665897635541379375947)
                ·
                  refine ⟨4257998846453312069063921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2838665897635541379375947 4257998846453312069063921)
                  ·
                    refine ⟨3193499134839984051797941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4257998846453312069063921 3193499134839984051797941)
                    ·
                      refine ⟨299390543891248504856057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3193499134839984051797941 299390543891248504856057)
                      ·
                        rfl

theorem cell23_583061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_583061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583061 prefixEnd_583061 := by exact prefixLift 583061
  have htrace : WordTrace (prefixWord ++ tailWord_583061) baseStart_583061 baseEnd_583061 := by
    simpa [prefixWord, tailWord_583061, baseEnd_583061] using wordTrace_append hprefix tailTrace_583061
  have hstable : (prefixWord ++ tailWord_583061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583061).length < 2 ^ (prefixWord ++ tailWord_583061).sum := by decide
  have hdescent : baseEnd_583061 < baseStart_583061 := by decide
  rcases family_descends (prefixWord ++ tailWord_583061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583088 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 4, 4, 2]
def baseStart_583088 : Nat := 118140960795 + 583088 * 2 ^ 59
def prefixEnd_583088 : Nat := 4983230072969 + 3 ^ 40 * 583088 * 2
def baseEnd_583088 : Nat := 299404407868919899218433

theorem tailTrace_583088 : CollatzResearch.WordTrace tailWord_583088 prefixEnd_583088 299404407868919899218433 := by
  unfold tailWord_583088
  simp only [CollatzResearch.WordTrace]
  refine ⟨10633483255789617173630959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14177977674386156231507945 10633483255789617173630959)
  ·
    refine ⟨15950224883684425760446439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10633483255789617173630959 15950224883684425760446439)
    ·
      refine ⟨23925337325526638640669659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15950224883684425760446439 23925337325526638640669659)
      ·
        refine ⟨35888005988289957961004489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23925337325526638640669659 35888005988289957961004489)
        ·
          refine ⟨26916004491217468470753367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35888005988289957961004489 26916004491217468470753367)
          ·
            refine ⟨40374006736826202706130051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26916004491217468470753367 40374006736826202706130051)
            ·
              refine ⟨60561010105239304059195077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40374006736826202706130051 60561010105239304059195077)
              ·
                refine ⟨11355189394732369511099077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60561010105239304059195077 11355189394732369511099077)
                ·
                  refine ⟨2129098011512319283331077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11355189394732369511099077 2129098011512319283331077)
                  ·
                    refine ⟨399205877158559865624577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2129098011512319283331077 399205877158559865624577)
                    ·
                      refine ⟨299404407868919899218433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 399205877158559865624577 299404407868919899218433)
                      ·
                        rfl

theorem cell23_583088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 4, 4, 2].length) (baseStart_583088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583088 prefixEnd_583088 := by exact prefixLift 583088
  have htrace : WordTrace (prefixWord ++ tailWord_583088) baseStart_583088 baseEnd_583088 := by
    simpa [prefixWord, tailWord_583088, baseEnd_583088] using wordTrace_append hprefix tailTrace_583088
  have hstable : (prefixWord ++ tailWord_583088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583088).length < 2 ^ (prefixWord ++ tailWord_583088).sum := by decide
  have hdescent : baseEnd_583088 < baseStart_583088 := by decide
  rcases family_descends (prefixWord ++ tailWord_583088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583106 : List Nat := [3, 5, 2, 1, 1, 2, 1, 1, 7]
def baseStart_583106 : Nat := 118140960795 + 583106 * 2 ^ 59
def prefixEnd_583106 : Nat := 4983230072969 + 3 ^ 40 * 583106 * 2
def baseEnd_583106 : Nat := 33268183391188980977039

theorem tailTrace_583106 : CollatzResearch.WordTrace tailWord_583106 prefixEnd_583106 33268183391188980977039 := by
  unfold tailWord_583106
  simp only [CollatzResearch.WordTrace]
  refine ⟨5316905756378505855354293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14178415350342682280944781 5316905756378505855354293)
  ·
    refine ⟨498459914660484923939465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5316905756378505855354293 498459914660484923939465)
    ·
      refine ⟨373844935995363692954599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 498459914660484923939465 373844935995363692954599)
      ·
        refine ⟨560767403993045539431899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373844935995363692954599 560767403993045539431899)
        ·
          refine ⟨841151105989568309147849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560767403993045539431899 841151105989568309147849)
          ·
            refine ⟨630863329492176231860887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 841151105989568309147849 630863329492176231860887)
            ·
              refine ⟨946294994238264347791331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 630863329492176231860887 946294994238264347791331)
              ·
                refine ⟨1419442491357396521686997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 946294994238264347791331 1419442491357396521686997)
                ·
                  refine ⟨33268183391188980977039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1419442491357396521686997 33268183391188980977039)
                  ·
                    rfl

theorem cell23_583106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_583106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583106 prefixEnd_583106 := by exact prefixLift 583106
  have htrace : WordTrace (prefixWord ++ tailWord_583106) baseStart_583106 baseEnd_583106 := by
    simpa [prefixWord, tailWord_583106, baseEnd_583106] using wordTrace_append hprefix tailTrace_583106
  have hstable : (prefixWord ++ tailWord_583106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583106).length < 2 ^ (prefixWord ++ tailWord_583106).sum := by decide
  have hdescent : baseEnd_583106 < baseStart_583106 := by decide
  rcases family_descends (prefixWord ++ tailWord_583106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583111 : List Nat := [1, 1, 4, 1, 1, 3, 1, 3, 8]
def baseStart_583111 : Nat := 118140960795 + 583111 * 2 ^ 59
def prefixEnd_583111 : Nat := 4983230072969 + 3 ^ 40 * 583111 * 2
def baseEnd_583111 : Nat := 33268468658219256581203

theorem tailTrace_583111 : CollatzResearch.WordTrace tailWord_583111 prefixEnd_583111 33268468658219256581203 := by
  unfold tailWord_583111
  simp only [CollatzResearch.WordTrace]
  refine ⟨21267805390495909275349187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14178536926997272850232791 21267805390495909275349187)
  ·
    refine ⟨31901708085743863913023781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21267805390495909275349187 31901708085743863913023781)
    ·
      refine ⟨5981570266076974483691959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31901708085743863913023781 5981570266076974483691959)
      ·
        refine ⟨8972355399115461725537939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5981570266076974483691959 8972355399115461725537939)
        ·
          refine ⟨13458533098673192588306909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8972355399115461725537939 13458533098673192588306909)
          ·
            refine ⟨5046949912002447220615091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13458533098673192588306909 5046949912002447220615091)
            ·
              refine ⟨7570424868003670830922637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5046949912002447220615091 7570424868003670830922637)
              ·
                refine ⟨2838909325501376561595989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7570424868003670830922637 2838909325501376561595989)
                ·
                  refine ⟨33268468658219256581203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2838909325501376561595989 33268468658219256581203)
                  ·
                    rfl

theorem cell23_583111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 8].length) (baseStart_583111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583111 prefixEnd_583111 := by exact prefixLift 583111
  have htrace : WordTrace (prefixWord ++ tailWord_583111) baseStart_583111 baseEnd_583111 := by
    simpa [prefixWord, tailWord_583111, baseEnd_583111] using wordTrace_append hprefix tailTrace_583111
  have hstable : (prefixWord ++ tailWord_583111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583111).length < 2 ^ (prefixWord ++ tailWord_583111).sum := by decide
  have hdescent : baseEnd_583111 < baseStart_583111 := by decide
  rcases family_descends (prefixWord ++ tailWord_583111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583115 : List Nat := [1, 1, 1, 1, 3, 3, 2, 6, 1, 4]
def baseStart_583115 : Nat := 118140960795 + 583115 * 2 ^ 59
def prefixEnd_583115 : Nat := 4983230072969 + 3 ^ 40 * 583115 * 2
def baseEnd_583115 : Nat := 99806090615530431193603

theorem tailTrace_583115 : CollatzResearch.WordTrace tailWord_583115 prefixEnd_583115 99806090615530431193603 := by
  unfold tailWord_583115
  simp only [CollatzResearch.WordTrace]
  refine ⟨21267951282481417958494799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14178634188320945305663199 21267951282481417958494799)
  ·
    refine ⟨31901926923722126937742199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21267951282481417958494799 31901926923722126937742199)
    ·
      refine ⟨47852890385583190406613299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31901926923722126937742199 47852890385583190406613299)
      ·
        refine ⟨71779335578374785609919949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47852890385583190406613299 71779335578374785609919949)
        ·
          refine ⟨26917250841890544603719981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71779335578374785609919949 26917250841890544603719981)
          ·
            refine ⟨10093969065708954226394993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26917250841890544603719981 10093969065708954226394993)
            ·
              refine ⟨7570476799281715669796245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10093969065708954226394993 7570476799281715669796245)
              ·
                refine ⟨354866099966330422021699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7570476799281715669796245 354866099966330422021699)
                ·
                  refine ⟨532299149949495633032549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 354866099966330422021699 532299149949495633032549)
                  ·
                    refine ⟨99806090615530431193603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 532299149949495633032549 99806090615530431193603)
                    ·
                      rfl

theorem cell23_583115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 1, 4].length) (baseStart_583115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583115 prefixEnd_583115 := by exact prefixLift 583115
  have htrace : WordTrace (prefixWord ++ tailWord_583115) baseStart_583115 baseEnd_583115 := by
    simpa [prefixWord, tailWord_583115, baseEnd_583115] using wordTrace_append hprefix tailTrace_583115
  have hstable : (prefixWord ++ tailWord_583115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583115).length < 2 ^ (prefixWord ++ tailWord_583115).sum := by decide
  have hdescent : baseEnd_583115 < baseStart_583115 := by decide
  rcases family_descends (prefixWord ++ tailWord_583115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583166 : List Nat := [4, 2, 2, 3, 1, 1, 1, 4, 1, 4]
def baseStart_583166 : Nat := 118140960795 + 583166 * 2 ^ 59
def prefixEnd_583166 : Nat := 4983230072969 + 3 ^ 40 * 583166 * 2
def baseEnd_583166 : Nat := 99814819786656864681025

theorem tailTrace_583166 : CollatzResearch.WordTrace tailWord_583166 prefixEnd_583166 99814819786656864681025 := by
  unfold tailWord_583166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2658726425662081708575169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14179874270197769112400901 2658726425662081708575169)
  ·
    refine ⟨1994044819246561281431377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2658726425662081708575169 1994044819246561281431377)
    ·
      refine ⟨1495533614434920961073533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1994044819246561281431377 1495533614434920961073533)
      ·
        refine ⟨560825105413095360402575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1495533614434920961073533 560825105413095360402575)
        ·
          refine ⟨841237658119643040603863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560825105413095360402575 841237658119643040603863)
          ·
            refine ⟨1261856487179464560905795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841237658119643040603863 1261856487179464560905795)
            ·
              refine ⟨1892784730769196841358693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1261856487179464560905795 1892784730769196841358693)
              ·
                refine ⟨354897137019224407754755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1892784730769196841358693 354897137019224407754755)
                ·
                  refine ⟨532345705528836611632133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 354897137019224407754755 532345705528836611632133)
                  ·
                    refine ⟨99814819786656864681025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 532345705528836611632133 99814819786656864681025)
                    ·
                      rfl

theorem cell23_583166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_583166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583166 prefixEnd_583166 := by exact prefixLift 583166
  have htrace : WordTrace (prefixWord ++ tailWord_583166) baseStart_583166 baseEnd_583166 := by
    simpa [prefixWord, tailWord_583166, baseEnd_583166] using wordTrace_append hprefix tailTrace_583166
  have hstable : (prefixWord ++ tailWord_583166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583166).length < 2 ^ (prefixWord ++ tailWord_583166).sum := by decide
  have hdescent : baseEnd_583166 < baseStart_583166 := by decide
  rcases family_descends (prefixWord ++ tailWord_583166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583239 : List Nat := [1, 1, 4, 1, 5, 1, 3, 1, 2, 4]
def baseStart_583239 : Nat := 118140960795 + 583239 * 2 ^ 59
def prefixEnd_583239 : Nat := 4983230072969 + 3 ^ 40 * 583239 * 2
def baseEnd_583239 : Nat := 99827314482582936143413

theorem tailTrace_583239 : CollatzResearch.WordTrace tailWord_583239 prefixEnd_583239 99827314482582936143413 := by
  unfold tailWord_583239
  simp only [CollatzResearch.WordTrace]
  refine ⟨21272473934032187136008771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14181649289354791424005847 21272473934032187136008771)
  ·
    refine ⟨31908710901048280704013157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21272473934032187136008771 31908710901048280704013157)
    ·
      refine ⟨5982883293946552632002467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31908710901048280704013157 5982883293946552632002467)
      ·
        refine ⟨8974324940919828948003701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5982883293946552632002467 8974324940919828948003701)
        ·
          refine ⟨841342963211233963875347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8974324940919828948003701 841342963211233963875347)
          ·
            refine ⟨1262014444816850945813021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841342963211233963875347 1262014444816850945813021)
            ·
              refine ⟨473255416806319104679883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1262014444816850945813021 473255416806319104679883)
              ·
                refine ⟨709883125209478657019825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 473255416806319104679883 709883125209478657019825)
                ·
                  refine ⟨532412343907108992764869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 709883125209478657019825 532412343907108992764869)
                  ·
                    refine ⟨99827314482582936143413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 532412343907108992764869 99827314482582936143413)
                    ·
                      rfl

theorem cell23_583239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_583239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583239 prefixEnd_583239 := by exact prefixLift 583239
  have htrace : WordTrace (prefixWord ++ tailWord_583239) baseStart_583239 baseEnd_583239 := by
    simpa [prefixWord, tailWord_583239, baseEnd_583239] using wordTrace_append hprefix tailTrace_583239
  have hstable : (prefixWord ++ tailWord_583239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583239).length < 2 ^ (prefixWord ++ tailWord_583239).sum := by decide
  have hdescent : baseEnd_583239 < baseStart_583239 := by decide
  rcases family_descends (prefixWord ++ tailWord_583239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583288 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 6, 1, 5]
def baseStart_583288 : Nat := 118140960795 + 583288 * 2 ^ 59
def prefixEnd_583288 : Nat := 4983230072969 + 3 ^ 40 * 583288 * 2
def baseEnd_583288 : Nat := 299507103999819116717513

theorem tailTrace_583288 : CollatzResearch.WordTrace tailWord_583288 prefixEnd_583288 299507103999819116717513 := by
  unfold tailWord_583288
  simp only [CollatzResearch.WordTrace]
  refine ⟨10637130555427334252271259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14182840740569779003028345 10637130555427334252271259)
  ·
    refine ⟨15955695833141001378406889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10637130555427334252271259 15955695833141001378406889)
    ·
      refine ⟨11966771874855751033805167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15955695833141001378406889 11966771874855751033805167)
      ·
        refine ⟨17950157812283626550707751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11966771874855751033805167 17950157812283626550707751)
        ·
          refine ⟨26925236718425439826061627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17950157812283626550707751 26925236718425439826061627)
          ·
            refine ⟨40387855077638159739092441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26925236718425439826061627 40387855077638159739092441)
            ·
              refine ⟨30290891308228619804319331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40387855077638159739092441 30290891308228619804319331)
              ·
                refine ⟨45436336962342929706478997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30290891308228619804319331 45436336962342929706478997)
                ·
                  refine ⟨2129828295109824829991203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45436336962342929706478997 2129828295109824829991203)
                  ·
                    refine ⟨3194742442664737244986805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2129828295109824829991203 3194742442664737244986805)
                    ·
                      refine ⟨299507103999819116717513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3194742442664737244986805 299507103999819116717513)
                      ·
                        rfl

theorem cell23_583288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_583288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583288 prefixEnd_583288 := by exact prefixLift 583288
  have htrace : WordTrace (prefixWord ++ tailWord_583288) baseStart_583288 baseEnd_583288 := by
    simpa [prefixWord, tailWord_583288, baseEnd_583288] using wordTrace_append hprefix tailTrace_583288
  have hstable : (prefixWord ++ tailWord_583288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583288).length < 2 ^ (prefixWord ++ tailWord_583288).sum := by decide
  have hdescent : baseEnd_583288 < baseStart_583288 := by decide
  rcases family_descends (prefixWord ++ tailWord_583288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583306 : List Nat := [3, 1, 2, 3, 2, 3, 1, 2, 1, 3, 2]
def baseStart_583306 : Nat := 118140960795 + 583306 * 2 ^ 59
def prefixEnd_583306 : Nat := 4983230072969 + 3 ^ 40 * 583306 * 2
def baseEnd_583306 : Nat := 299516346651600046292431

theorem tailTrace_583306 : CollatzResearch.WordTrace tailWord_583306 prefixEnd_583306 299516346651600046292431 := by
  unfold tailWord_583306
  simp only [CollatzResearch.WordTrace]
  refine ⟨5318729406197364394674443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14183278416526305052465181 5318729406197364394674443)
  ·
    refine ⟨7978094109296046592011665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5318729406197364394674443 7978094109296046592011665)
    ·
      refine ⟨5983570581972034944008749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7978094109296046592011665 5983570581972034944008749)
      ·
        refine ⟨2243838968239513104003281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5983570581972034944008749 2243838968239513104003281)
        ·
          refine ⟨1682879226179634828002461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2243838968239513104003281 1682879226179634828002461)
          ·
            refine ⟨631079709817363060500923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1682879226179634828002461 631079709817363060500923)
            ·
              refine ⟨946619564726044590751385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 631079709817363060500923 946619564726044590751385)
              ·
                refine ⟨709964673544533443063539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 946619564726044590751385 709964673544533443063539)
                ·
                  refine ⟨1064947010316800164595309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 709964673544533443063539 1064947010316800164595309)
                  ·
                    refine ⟨399355128868800061723241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1064947010316800164595309 399355128868800061723241)
                    ·
                      refine ⟨299516346651600046292431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 399355128868800061723241 299516346651600046292431)
                      ·
                        rfl

theorem cell23_583306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_583306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583306 prefixEnd_583306 := by exact prefixLift 583306
  have htrace : WordTrace (prefixWord ++ tailWord_583306) baseStart_583306 baseEnd_583306 := by
    simpa [prefixWord, tailWord_583306, baseEnd_583306] using wordTrace_append hprefix tailTrace_583306
  have hstable : (prefixWord ++ tailWord_583306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583306).length < 2 ^ (prefixWord ++ tailWord_583306).sum := by decide
  have hdescent : baseEnd_583306 < baseStart_583306 := by decide
  rcases family_descends (prefixWord ++ tailWord_583306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583308 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 9]
def baseStart_583308 : Nat := 118140960795 + 583308 * 2 ^ 59
def prefixEnd_583308 : Nat := 4983230072969 + 3 ^ 40 * 583308 * 2
def baseEnd_583308 : Nat := 33279708179212115385269

theorem tailTrace_583308 : CollatzResearch.WordTrace tailWord_583308 prefixEnd_583308 33279708179212115385269 := by
  unfold tailWord_583308
  simp only [CollatzResearch.WordTrace]
  refine ⟨10637495285391105960135289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14183327047188141280180385 10637495285391105960135289)
  ·
    refine ⟨7978121464043329470101467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10637495285391105960135289 7978121464043329470101467)
    ·
      refine ⟨11967182196064994205152201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7978121464043329470101467 11967182196064994205152201)
      ·
        refine ⟨8975386647048745653864151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11967182196064994205152201 8975386647048745653864151)
        ·
          refine ⟨13463079970573118480796227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8975386647048745653864151 13463079970573118480796227)
          ·
            refine ⟨20194619955859677721194341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13463079970573118480796227 20194619955859677721194341)
            ·
              refine ⟨3786491241723689572723939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20194619955859677721194341 3786491241723689572723939)
              ·
                refine ⟨5679736862585534359085909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3786491241723689572723939 5679736862585534359085909)
                ·
                  refine ⟨33279708179212115385269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5679736862585534359085909 33279708179212115385269)
                  ·
                    rfl

theorem cell23_583308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 9].length) (baseStart_583308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583308 prefixEnd_583308 := by exact prefixLift 583308
  have htrace : WordTrace (prefixWord ++ tailWord_583308) baseStart_583308 baseEnd_583308 := by
    simpa [prefixWord, tailWord_583308, baseEnd_583308] using wordTrace_append hprefix tailTrace_583308
  have hstable : (prefixWord ++ tailWord_583308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583308).length < 2 ^ (prefixWord ++ tailWord_583308).sum := by decide
  have hdescent : baseEnd_583308 < baseStart_583308 := by decide
  rcases family_descends (prefixWord ++ tailWord_583308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583372 : List Nat := [2, 2, 1, 5, 2, 1, 1, 1, 1, 7]
def baseStart_583372 : Nat := 118140960795 + 583372 * 2 ^ 59
def prefixEnd_583372 : Nat := 4983230072969 + 3 ^ 40 * 583372 * 2
def baseEnd_583372 : Nat := 99850078791598929355709

theorem tailTrace_583372 : CollatzResearch.WordTrace tailWord_583372 prefixEnd_583372 99850078791598929355709 := by
  unfold tailWord_583372
  simp only [CollatzResearch.WordTrace]
  refine ⟨10638662421275175425300185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14184883228366900567066913 10638662421275175425300185)
  ·
    refine ⟨7978996815956381568975139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10638662421275175425300185 7978996815956381568975139)
    ·
      refine ⟨11968495223934572353462709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7978996815956381568975139 11968495223934572353462709)
      ·
        refine ⟨1122046427243866158137129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11968495223934572353462709 1122046427243866158137129)
        ·
          refine ⟨841534820432899618602847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1122046427243866158137129 841534820432899618602847)
          ·
            refine ⟨1262302230649349427904271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841534820432899618602847 1262302230649349427904271)
            ·
              refine ⟨1893453345974024141856407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1262302230649349427904271 1893453345974024141856407)
              ·
                refine ⟨2840180018961036212784611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1893453345974024141856407 2840180018961036212784611)
                ·
                  refine ⟨4260270028441554319176917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2840180018961036212784611 4260270028441554319176917)
                  ·
                    refine ⟨99850078791598929355709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4260270028441554319176917 99850078791598929355709)
                    ·
                      rfl

theorem cell23_583372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 1, 7].length) (baseStart_583372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583372 prefixEnd_583372 := by exact prefixLift 583372
  have htrace : WordTrace (prefixWord ++ tailWord_583372) baseStart_583372 baseEnd_583372 := by
    simpa [prefixWord, tailWord_583372, baseEnd_583372] using wordTrace_append hprefix tailTrace_583372
  have hstable : (prefixWord ++ tailWord_583372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583372).length < 2 ^ (prefixWord ++ tailWord_583372).sum := by decide
  have hdescent : baseEnd_583372 < baseStart_583372 := by decide
  rcases family_descends (prefixWord ++ tailWord_583372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583392 : List Nat := [2, 1, 1, 3, 1, 2, 3, 2, 2, 4, 2]
def baseStart_583392 : Nat := 118140960795 + 583392 * 2 ^ 59
def prefixEnd_583392 : Nat := 4983230072969 + 3 ^ 40 * 583392 * 2
def baseEnd_583392 : Nat := 299560505987886709817035

theorem tailTrace_583392 : CollatzResearch.WordTrace tailWord_583392 prefixEnd_583392 299560505987886709817035 := by
  unfold tailWord_583392
  simp only [CollatzResearch.WordTrace]
  refine ⟨10639027151238947133164215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14185369534985262844218953 10639027151238947133164215)
  ·
    refine ⟨15958540726858420699746323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10639027151238947133164215 15958540726858420699746323)
    ·
      refine ⟨23937811090287631049619485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15958540726858420699746323 23937811090287631049619485)
      ·
        refine ⟨8976679158857861643607307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23937811090287631049619485 8976679158857861643607307)
        ·
          refine ⟨13465018738286792465410961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8976679158857861643607307 13465018738286792465410961)
          ·
            refine ⟨10098764053715094349058221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13465018738286792465410961 10098764053715094349058221)
            ·
              refine ⟨3787036520143160380896833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10098764053715094349058221 3787036520143160380896833)
              ·
                refine ⟨2840277390107370285672625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3787036520143160380896833 2840277390107370285672625)
                ·
                  refine ⟨2130208042580527714254469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2840277390107370285672625 2130208042580527714254469)
                  ·
                    refine ⟨399414007983848946422713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2130208042580527714254469 399414007983848946422713)
                    ·
                      refine ⟨299560505987886709817035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 399414007983848946422713 299560505987886709817035)
                      ·
                        rfl

theorem cell23_583392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 2, 4, 2].length) (baseStart_583392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583392 prefixEnd_583392 := by exact prefixLift 583392
  have htrace : WordTrace (prefixWord ++ tailWord_583392) baseStart_583392 baseEnd_583392 := by
    simpa [prefixWord, tailWord_583392, baseEnd_583392] using wordTrace_append hprefix tailTrace_583392
  have hstable : (prefixWord ++ tailWord_583392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583392).length < 2 ^ (prefixWord ++ tailWord_583392).sum := by decide
  have hdescent : baseEnd_583392 < baseStart_583392 := by decide
  rcases family_descends (prefixWord ++ tailWord_583392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583402 : List Nat := [3, 1, 3, 1, 1, 1, 3, 3, 3, 4]
def baseStart_583402 : Nat := 118140960795 + 583402 * 2 ^ 59
def prefixEnd_583402 : Nat := 4983230072969 + 3 ^ 40 * 583402 * 2
def baseEnd_583402 : Nat := 99855213598143890230663

theorem tailTrace_583402 : CollatzResearch.WordTrace tailWord_583402 prefixEnd_583402 99855213598143890230663 := by
  unfold tailWord_583402
  simp only [CollatzResearch.WordTrace]
  refine ⟨5319604758110416493548115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14185612688294443982794973 5319604758110416493548115)
  ·
    refine ⟨7979407137165624740322173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5319604758110416493548115 7979407137165624740322173)
    ·
      refine ⟨2992277676437109277620815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7979407137165624740322173 2992277676437109277620815)
      ·
        refine ⟨4488416514655663916431223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2992277676437109277620815 4488416514655663916431223)
        ·
          refine ⟨6732624771983495874646835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4488416514655663916431223 6732624771983495874646835)
          ·
            refine ⟨10098937157975243811970253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6732624771983495874646835 10098937157975243811970253)
            ·
              refine ⟨3787101434240716429488845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10098937157975243811970253 3787101434240716429488845)
              ·
                refine ⟨1420163037840268661058317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3787101434240716429488845 1420163037840268661058317)
                ·
                  refine ⟨532561139190100747896869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1420163037840268661058317 532561139190100747896869)
                  ·
                    refine ⟨99855213598143890230663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 532561139190100747896869 99855213598143890230663)
                    ·
                      rfl

theorem cell23_583402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_583402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583402 prefixEnd_583402 := by exact prefixLift 583402
  have htrace : WordTrace (prefixWord ++ tailWord_583402) baseStart_583402 baseEnd_583402 := by
    simpa [prefixWord, tailWord_583402, baseEnd_583402] using wordTrace_append hprefix tailTrace_583402
  have hstable : (prefixWord ++ tailWord_583402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583402).length < 2 ^ (prefixWord ++ tailWord_583402).sum := by decide
  have hdescent : baseEnd_583402 < baseStart_583402 := by decide
  rcases family_descends (prefixWord ++ tailWord_583402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583415 : List Nat := [1, 1, 3, 1, 1, 1, 4, 5, 6]
def baseStart_583415 : Nat := 118140960795 + 583415 * 2 ^ 59
def prefixEnd_583415 : Nat := 4983230072969 + 3 ^ 40 * 583415 * 2
def baseEnd_583415 : Nat := 33285812893660013314381

theorem tailTrace_583415 : CollatzResearch.WordTrace tailWord_583415 prefixEnd_583415 33285812893660013314381 := by
  unfold tailWord_583415
  simp only [CollatzResearch.WordTrace]
  refine ⟨21278893181394569194415699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14185928787596379462943799 21278893181394569194415699)
  ·
    refine ⟨31918339772091853791623549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21278893181394569194415699 31918339772091853791623549)
    ·
      refine ⟨11969377414534445171858831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31918339772091853791623549 11969377414534445171858831)
      ·
        refine ⟨17954066121801667757788247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11969377414534445171858831 17954066121801667757788247)
        ·
          refine ⟨26931099182702501636682371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17954066121801667757788247 26931099182702501636682371)
          ·
            refine ⟨40396648774053752455023557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26931099182702501636682371 40396648774053752455023557)
            ·
              refine ⟨7574371645135078585316917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40396648774053752455023557 7574371645135078585316917)
              ·
                refine ⟨710097341731413617373461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7574371645135078585316917 710097341731413617373461)
                ·
                  refine ⟨33285812893660013314381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 710097341731413617373461 33285812893660013314381)
                  ·
                    rfl

theorem cell23_583415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 6].length) (baseStart_583415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583415 prefixEnd_583415 := by exact prefixLift 583415
  have htrace : WordTrace (prefixWord ++ tailWord_583415) baseStart_583415 baseEnd_583415 := by
    simpa [prefixWord, tailWord_583415, baseEnd_583415] using wordTrace_append hprefix tailTrace_583415
  have hstable : (prefixWord ++ tailWord_583415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583415).length < 2 ^ (prefixWord ++ tailWord_583415).sum := by decide
  have hdescent : baseEnd_583415 < baseStart_583415 := by decide
  rcases family_descends (prefixWord ++ tailWord_583415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583459 : List Nat := [1, 1, 1, 4, 2, 1, 5, 1, 3, 1, 3]
def baseStart_583459 : Nat := 118140960795 + 583459 * 2 ^ 59
def prefixEnd_583459 : Nat := 4983230072969 + 3 ^ 40 * 583459 * 2
def baseEnd_583459 : Nat := 299594909191737947679227

theorem tailTrace_583459 : CollatzResearch.WordTrace tailWord_583459 prefixEnd_583459 299594909191737947679227 := by
  unfold tailWord_583459
  simp only [CollatzResearch.WordTrace]
  refine ⟨21280497993235164709017431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14186998662156776472678287 21280497993235164709017431)
  ·
    refine ⟨31920746989852747063526147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21280497993235164709017431 31920746989852747063526147)
    ·
      refine ⟨47881120484779120595289221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31920746989852747063526147 47881120484779120595289221)
      ·
        refine ⟨8977710090896085111616729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47881120484779120595289221 8977710090896085111616729)
        ·
          refine ⟨6733282568172063833712547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8977710090896085111616729 6733282568172063833712547)
          ·
            refine ⟨10099923852258095750568821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6733282568172063833712547 10099923852258095750568821)
            ·
              refine ⟨946867861149196476615827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10099923852258095750568821 946867861149196476615827)
              ·
                refine ⟨1420301791723794714923741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 946867861149196476615827 1420301791723794714923741)
                ·
                  refine ⟨532613171896423018096403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1420301791723794714923741 532613171896423018096403)
                  ·
                    refine ⟨798919757844634527144605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 532613171896423018096403 798919757844634527144605)
                    ·
                      refine ⟨299594909191737947679227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 798919757844634527144605 299594909191737947679227)
                      ·
                        rfl

theorem cell23_583459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_583459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583459 prefixEnd_583459 := by exact prefixLift 583459
  have htrace : WordTrace (prefixWord ++ tailWord_583459) baseStart_583459 baseEnd_583459 := by
    simpa [prefixWord, tailWord_583459, baseEnd_583459] using wordTrace_append hprefix tailTrace_583459
  have hstable : (prefixWord ++ tailWord_583459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583459).length < 2 ^ (prefixWord ++ tailWord_583459).sum := by decide
  have hdescent : baseEnd_583459 < baseStart_583459 := by decide
  rcases family_descends (prefixWord ++ tailWord_583459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583486 : List Nat := [4, 2, 1, 2, 2, 1, 1, 3, 2, 3, 2]
def baseStart_583486 : Nat := 118140960795 + 583486 * 2 ^ 59
def prefixEnd_583486 : Nat := 4983230072969 + 3 ^ 40 * 583486 * 2
def baseEnd_583486 : Nat := 299608773169409342041603

theorem tailTrace_583486 : CollatzResearch.WordTrace tailWord_583486 prefixEnd_583486 299608773169409342041603 := by
  unfold tailWord_583486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2660185345517168540031289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14187655176091565546833541 2660185345517168540031289)
  ·
    refine ⟨1995139009137876405023467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2660185345517168540031289 1995139009137876405023467)
    ·
      refine ⟨2992708513706814607535201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1995139009137876405023467 2992708513706814607535201)
      ·
        refine ⟨2244531385280110955651401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2992708513706814607535201 2244531385280110955651401)
        ·
          refine ⟨1683398538960083216738551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2244531385280110955651401 1683398538960083216738551)
          ·
            refine ⟨2525097808440124825107827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1683398538960083216738551 2525097808440124825107827)
            ·
              refine ⟨3787646712660187237661741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2525097808440124825107827 3787646712660187237661741)
              ·
                refine ⟨1420367517247570214123153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3787646712660187237661741 1420367517247570214123153)
                ·
                  refine ⟨1065275637935677660592365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1420367517247570214123153 1065275637935677660592365)
                  ·
                    refine ⟨399478364225879122722137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1065275637935677660592365 399478364225879122722137)
                    ·
                      refine ⟨299608773169409342041603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 399478364225879122722137 299608773169409342041603)
                      ·
                        rfl

theorem cell23_583486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_583486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583486 prefixEnd_583486 := by exact prefixLift 583486
  have htrace : WordTrace (prefixWord ++ tailWord_583486) baseStart_583486 baseEnd_583486 := by
    simpa [prefixWord, tailWord_583486, baseEnd_583486] using wordTrace_append hprefix tailTrace_583486
  have hstable : (prefixWord ++ tailWord_583486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583486).length < 2 ^ (prefixWord ++ tailWord_583486).sum := by decide
  have hdescent : baseEnd_583486 < baseStart_583486 := by decide
  rcases family_descends (prefixWord ++ tailWord_583486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583505 : List Nat := [1, 2, 2, 1, 5, 12]
def baseStart_583505 : Nat := 118140960795 + 583505 * 2 ^ 59
def prefixEnd_583505 : Nat := 4983230072969 + 3 ^ 40 * 583505 * 2
def baseEnd_583505 : Nat := 1232998062970554599605

theorem tailTrace_583505 : CollatzResearch.WordTrace tailWord_583505 prefixEnd_583505 1232998062970554599605 := by
  unfold tailWord_583505
  simp only [CollatzResearch.WordTrace]
  refine ⟨21282175751068514565191969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14188117167379009710127979 21282175751068514565191969)
  ·
    refine ⟨15961631813301385923893977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21282175751068514565191969 15961631813301385923893977)
    ·
      refine ⟨11971223859976039442920483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15961631813301385923893977 11971223859976039442920483)
      ·
        refine ⟨17956835789964059164380725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11971223859976039442920483 17956835789964059164380725)
        ·
          refine ⟨1683453355309130546660693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17956835789964059164380725 1683453355309130546660693)
          ·
            refine ⟨1232998062970554599605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 1683453355309130546660693 1232998062970554599605)
            ·
              rfl

theorem cell23_583505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 12].length) (baseStart_583505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583505 prefixEnd_583505 := by exact prefixLift 583505
  have htrace : WordTrace (prefixWord ++ tailWord_583505) baseStart_583505 baseEnd_583505 := by
    simpa [prefixWord, tailWord_583505, baseEnd_583505] using wordTrace_append hprefix tailTrace_583505
  have hstable : (prefixWord ++ tailWord_583505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583505).length < 2 ^ (prefixWord ++ tailWord_583505).sum := by decide
  have hdescent : baseEnd_583505 < baseStart_583505 := by decide
  rcases family_descends (prefixWord ++ tailWord_583505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583509 : List Nat := [1, 3, 2, 2, 2, 2, 1, 4, 2, 4]
def baseStart_583509 : Nat := 118140960795 + 583509 * 2 ^ 59
def prefixEnd_583509 : Nat := 4983230072969 + 3 ^ 40 * 583509 * 2
def baseEnd_583509 : Nat := 99873527741487584017999

theorem tailTrace_583509 : CollatzResearch.WordTrace tailWord_583509 prefixEnd_583509 99873527741487584017999 := by
  unfold tailWord_583509
  simp only [CollatzResearch.WordTrace]
  refine ⟨21282321643054023248337581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14188214428702682165558387 21282321643054023248337581)
  ·
    refine ⟨7980870616145258718126593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21282321643054023248337581 7980870616145258718126593)
    ·
      refine ⟨5985652962108944038594945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7980870616145258718126593 5985652962108944038594945)
      ·
        refine ⟨4489239721581708028946209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5985652962108944038594945 4489239721581708028946209)
        ·
          refine ⟨3366929791186281021709657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4489239721581708028946209 3366929791186281021709657)
          ·
            refine ⟨2525197343389710766282243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3366929791186281021709657 2525197343389710766282243)
            ·
              refine ⟨3787796015084566149423365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2525197343389710766282243 3787796015084566149423365)
              ·
                refine ⟨710211752828356153016881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3787796015084566149423365 710211752828356153016881)
                ·
                  refine ⟨532658814621267114762661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 710211752828356153016881 532658814621267114762661)
                  ·
                    refine ⟨99873527741487584017999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 532658814621267114762661 99873527741487584017999)
                    ·
                      rfl

theorem cell23_583509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_583509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583509 prefixEnd_583509 := by exact prefixLift 583509
  have htrace : WordTrace (prefixWord ++ tailWord_583509) baseStart_583509 baseEnd_583509 := by
    simpa [prefixWord, tailWord_583509, baseEnd_583509] using wordTrace_append hprefix tailTrace_583509
  have hstable : (prefixWord ++ tailWord_583509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583509).length < 2 ^ (prefixWord ++ tailWord_583509).sum := by decide
  have hdescent : baseEnd_583509 < baseStart_583509 := by decide
  rcases family_descends (prefixWord ++ tailWord_583509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583549 : List Nat := [1, 4, 1, 1, 2, 1, 1, 4, 4, 1, 3]
def baseStart_583549 : Nat := 118140960795 + 583549 * 2 ^ 59
def prefixEnd_583549 : Nat := 4983230072969 + 3 ^ 40 * 583549 * 2
def baseEnd_583549 : Nat := 299641122450642595553813

theorem tailTrace_583549 : CollatzResearch.WordTrace tailWord_583549 prefixEnd_583549 299641122450642595553813 := by
  unfold tailWord_583549
  simp only [CollatzResearch.WordTrace]
  refine ⟨21283780562909110079793701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14189187041939406719862467 21283780562909110079793701)
  ·
    refine ⟨3990708855545458139961319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21283780562909110079793701 3990708855545458139961319)
    ·
      refine ⟨5986063283318187209941979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3990708855545458139961319 5986063283318187209941979)
      ·
        refine ⟨8979094924977280814912969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5986063283318187209941979 8979094924977280814912969)
        ·
          refine ⟨6734321193732960611184727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8979094924977280814912969 6734321193732960611184727)
          ·
            refine ⟨10101481790599440916777091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6734321193732960611184727 10101481790599440916777091)
            ·
              refine ⟨15152222685899161375165637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10101481790599440916777091 15152222685899161375165637)
              ·
                refine ⟨2841041753606092757843557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15152222685899161375165637 2841041753606092757843557)
                ·
                  refine ⟨532695328801142392095667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2841041753606092757843557 532695328801142392095667)
                  ·
                    refine ⟨799042993201713588143501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 532695328801142392095667 799042993201713588143501)
                    ·
                      refine ⟨299641122450642595553813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 799042993201713588143501 299641122450642595553813)
                      ·
                        rfl

theorem cell23_583549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_583549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583549 prefixEnd_583549 := by exact prefixLift 583549
  have htrace : WordTrace (prefixWord ++ tailWord_583549) baseStart_583549 baseEnd_583549 := by
    simpa [prefixWord, tailWord_583549, baseEnd_583549] using wordTrace_append hprefix tailTrace_583549
  have hstable : (prefixWord ++ tailWord_583549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583549).length < 2 ^ (prefixWord ++ tailWord_583549).sum := by decide
  have hdescent : baseEnd_583549 < baseStart_583549 := by decide
  rcases family_descends (prefixWord ++ tailWord_583549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583550 : List Nat := [4, 2, 3, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_583550 : Nat := 118140960795 + 583550 * 2 ^ 59
def prefixEnd_583550 : Nat := 4983230072969 + 3 ^ 40 * 583550 * 2
def baseEnd_583550 : Nat := 299641635931297091641309

theorem tailTrace_583550 : CollatzResearch.WordTrace tailWord_583550 prefixEnd_583550 299641635931297091641309 := by
  unfold tailWord_583550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2660477129488185906322513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14189211357270324833720069 2660477129488185906322513)
  ·
    refine ⟨1995357847116139429741885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2660477129488185906322513 1995357847116139429741885)
    ·
      refine ⟨748259192668552286153207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1995357847116139429741885 748259192668552286153207)
      ·
        refine ⟨1122388789002828429229811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 748259192668552286153207 1122388789002828429229811)
        ·
          refine ⟨1683583183504242643844717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1122388789002828429229811 1683583183504242643844717)
          ·
            refine ⟨631343693814090991441769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1683583183504242643844717 631343693814090991441769)
            ·
              refine ⟨473507770360568243581327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 631343693814090991441769 473507770360568243581327)
              ·
                refine ⟨710261655540852365371991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 473507770360568243581327 710261655540852365371991)
                ·
                  refine ⟨1065392483311278548057987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 710261655540852365371991 1065392483311278548057987)
                  ·
                    refine ⟨1598088724966917822086981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1065392483311278548057987 1598088724966917822086981)
                    ·
                      refine ⟨299641635931297091641309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1598088724966917822086981 299641635931297091641309)
                      ·
                        rfl

theorem cell23_583550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_583550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583550 prefixEnd_583550 := by exact prefixLift 583550
  have htrace : WordTrace (prefixWord ++ tailWord_583550) baseStart_583550 baseEnd_583550 := by
    simpa [prefixWord, tailWord_583550, baseEnd_583550] using wordTrace_append hprefix tailTrace_583550
  have hstable : (prefixWord ++ tailWord_583550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583550).length < 2 ^ (prefixWord ++ tailWord_583550).sum := by decide
  have hdescent : baseEnd_583550 < baseStart_583550 := by decide
  rcases family_descends (prefixWord ++ tailWord_583550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583553 : List Nat := [1, 2, 4, 4, 1, 1, 1, 3, 1, 2, 3]
def baseStart_583553 : Nat := 118140960795 + 583553 * 2 ^ 59
def prefixEnd_583553 : Nat := 4983230072969 + 3 ^ 40 * 583553 * 2
def baseEnd_583553 : Nat := 299643176373260579903795

theorem tailTrace_583553 : CollatzResearch.WordTrace tailWord_583553 prefixEnd_583553 299643176373260579903795 := by
  unfold tailWord_583553
  simp only [CollatzResearch.WordTrace]
  refine ⟨21283926454894618762939313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14189284303263079175292875 21283926454894618762939313)
  ·
    refine ⟨15962944841170964072204485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21283926454894618762939313 15962944841170964072204485)
    ·
      refine ⟨2993052157719555763538341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15962944841170964072204485 2993052157719555763538341)
      ·
        refine ⟨561197279572416705663439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2993052157719555763538341 561197279572416705663439)
        ·
          refine ⟨841795919358625058495159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561197279572416705663439 841795919358625058495159)
          ·
            refine ⟨1262693879037937587742739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841795919358625058495159 1262693879037937587742739)
            ·
              refine ⟨1894040818556906381614109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1262693879037937587742739 1894040818556906381614109)
              ·
                refine ⟨710265306958839893105291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1894040818556906381614109 710265306958839893105291)
                ·
                  refine ⟨1065397960438259839657937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 710265306958839893105291 1065397960438259839657937)
                  ·
                    refine ⟨799048470328694879743453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1065397960438259839657937 799048470328694879743453)
                    ·
                      refine ⟨299643176373260579903795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 799048470328694879743453 299643176373260579903795)
                      ·
                        rfl

theorem cell23_583553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_583553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583553 prefixEnd_583553 := by exact prefixLift 583553
  have htrace : WordTrace (prefixWord ++ tailWord_583553) baseStart_583553 baseEnd_583553 := by
    simpa [prefixWord, tailWord_583553, baseEnd_583553] using wordTrace_append hprefix tailTrace_583553
  have hstable : (prefixWord ++ tailWord_583553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583553).length < 2 ^ (prefixWord ++ tailWord_583553).sum := by decide
  have hdescent : baseEnd_583553 < baseStart_583553 := by decide
  rcases family_descends (prefixWord ++ tailWord_583553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583583 : List Nat := [1, 1, 2, 5, 4, 1, 1, 1, 1, 3, 3]
def baseStart_583583 : Nat := 118140960795 + 583583 * 2 ^ 59
def prefixEnd_583583 : Nat := 4983230072969 + 3 ^ 40 * 583583 * 2
def baseEnd_583583 : Nat := 299658580792895462528657

theorem tailTrace_583583 : CollatzResearch.WordTrace tailWord_583583 prefixEnd_583583 299658580792895462528657 := by
  unfold tailWord_583583
  simp only [CollatzResearch.WordTrace]
  refine ⟨21285020644785933886531403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14190013763190622591020935 21285020644785933886531403)
  ·
    refine ⟨31927530967178900829797105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21285020644785933886531403 31927530967178900829797105)
    ·
      refine ⟨23945648225384175622347829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31927530967178900829797105 23945648225384175622347829)
      ·
        refine ⟨2244904521129766464595109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23945648225384175622347829 2244904521129766464595109)
        ·
          refine ⟨420919597711831212111583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2244904521129766464595109 420919597711831212111583)
          ·
            refine ⟨631379396567746818167375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420919597711831212111583 631379396567746818167375)
            ·
              refine ⟨947069094851620227251063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 631379396567746818167375 947069094851620227251063)
              ·
                refine ⟨1420603642277430340876595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 947069094851620227251063 1420603642277430340876595)
                ·
                  refine ⟨2130905463416145511314893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1420603642277430340876595 2130905463416145511314893)
                  ·
                    refine ⟨799089548781054566743085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2130905463416145511314893 799089548781054566743085)
                    ·
                      refine ⟨299658580792895462528657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 799089548781054566743085 299658580792895462528657)
                      ·
                        rfl

theorem cell23_583583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_583583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583583 prefixEnd_583583 := by exact prefixLift 583583
  have htrace : WordTrace (prefixWord ++ tailWord_583583) baseStart_583583 baseEnd_583583 := by
    simpa [prefixWord, tailWord_583583, baseEnd_583583] using wordTrace_append hprefix tailTrace_583583
  have hstable : (prefixWord ++ tailWord_583583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583583).length < 2 ^ (prefixWord ++ tailWord_583583).sum := by decide
  have hdescent : baseEnd_583583 < baseStart_583583 := by decide
  rcases family_descends (prefixWord ++ tailWord_583583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583602 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4]
def baseStart_583602 : Nat := 118140960795 + 583602 * 2 ^ 59
def prefixEnd_583602 : Nat := 4983230072969 + 3 ^ 40 * 583602 * 2
def baseEnd_583602 : Nat := 299668336925330888191069

theorem tailTrace_583602 : CollatzResearch.WordTrace tailWord_583602 prefixEnd_583602 299668336925330888191069 := by
  unfold tailWord_583602
  simp only [CollatzResearch.WordTrace]
  refine ⟨5321428407929275032868265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14190475754478066754315373 5321428407929275032868265)
  ·
    refine ⟨3991071305946956274651199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5321428407929275032868265 3991071305946956274651199)
    ·
      refine ⟨5986606958920434411976799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3991071305946956274651199 5986606958920434411976799)
      ·
        refine ⟨8979910438380651617965199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5986606958920434411976799 8979910438380651617965199)
        ·
          refine ⟨13469865657570977426947799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8979910438380651617965199 13469865657570977426947799)
          ·
            refine ⟨20204798486356466140421699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13469865657570977426947799 20204798486356466140421699)
            ·
              refine ⟨30307197729534699210632549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20204798486356466140421699 30307197729534699210632549)
              ·
                refine ⟨5682599574287756101993603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30307197729534699210632549 5682599574287756101993603)
                ·
                  refine ⟨8523899361431634152990405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5682599574287756101993603 8523899361431634152990405)
                  ·
                    refine ⟨1598231130268431403685701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8523899361431634152990405 1598231130268431403685701)
                    ·
                      refine ⟨299668336925330888191069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1598231130268431403685701 299668336925330888191069)
                      ·
                        rfl

theorem cell23_583602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_583602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583602 prefixEnd_583602 := by exact prefixLift 583602
  have htrace : WordTrace (prefixWord ++ tailWord_583602) baseStart_583602 baseEnd_583602 := by
    simpa [prefixWord, tailWord_583602, baseEnd_583602] using wordTrace_append hprefix tailTrace_583602
  have hstable : (prefixWord ++ tailWord_583602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583602).length < 2 ^ (prefixWord ++ tailWord_583602).sum := by decide
  have hdescent : baseEnd_583602 < baseStart_583602 := by decide
  rcases family_descends (prefixWord ++ tailWord_583602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583644 : List Nat := [2, 2, 6, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_583644 : Nat := 118140960795 + 583644 * 2 ^ 59
def prefixEnd_583644 : Nat := 4983230072969 + 3 ^ 40 * 583644 * 2
def baseEnd_583644 : Nat := 299689903112819723865877

theorem tailTrace_583644 : CollatzResearch.WordTrace tailWord_583644 prefixEnd_583644 299689903112819723865877 := by
  unfold tailWord_583644
  simp only [CollatzResearch.WordTrace]
  refine ⟨10643622748782470652250993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14191496998376627536334657 10643622748782470652250993)
  ·
    refine ⟨7982717061586852989188245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10643622748782470652250993 7982717061586852989188245)
    ·
      refine ⟨374189862261883733868199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7982717061586852989188245 374189862261883733868199)
      ·
        refine ⟨561284793392825600802299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374189862261883733868199 561284793392825600802299)
        ·
          refine ⟨841927190089238401203449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561284793392825600802299 841927190089238401203449)
          ·
            refine ⟨631445392566928800902587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 841927190089238401203449 631445392566928800902587)
            ·
              refine ⟨947168088850393201353881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 631445392566928800902587 947168088850393201353881)
              ·
                refine ⟨710376066637794901015411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 947168088850393201353881 710376066637794901015411)
                ·
                  refine ⟨1065564099956692351523117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 710376066637794901015411 1065564099956692351523117)
                  ·
                    refine ⟨399586537483759631821169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1065564099956692351523117 399586537483759631821169)
                    ·
                      refine ⟨299689903112819723865877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 399586537483759631821169 299689903112819723865877)
                      ·
                        rfl

theorem cell23_583644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_583644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583644 prefixEnd_583644 := by exact prefixLift 583644
  have htrace : WordTrace (prefixWord ++ tailWord_583644) baseStart_583644 baseEnd_583644 := by
    simpa [prefixWord, tailWord_583644, baseEnd_583644] using wordTrace_append hprefix tailTrace_583644
  have hstable : (prefixWord ++ tailWord_583644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583644).length < 2 ^ (prefixWord ++ tailWord_583644).sum := by decide
  have hdescent : baseEnd_583644 < baseStart_583644 := by decide
  rcases family_descends (prefixWord ++ tailWord_583644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583652 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 1, 1, 7]
def baseStart_583652 : Nat := 118140960795 + 583652 * 2 ^ 59
def prefixEnd_583652 : Nat := 4983230072969 + 3 ^ 40 * 583652 * 2
def baseEnd_583652 : Nat := 299694010958055692565839

theorem tailTrace_583652 : CollatzResearch.WordTrace tailWord_583652 prefixEnd_583652 299694010958055692565839 := by
  unfold tailWord_583652
  simp only [CollatzResearch.WordTrace]
  refine ⟨10643768640767979335396605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14191691521023972447195473 10643768640767979335396605)
  ·
    refine ⟨3991413240287992250773727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10643768640767979335396605 3991413240287992250773727)
    ·
      refine ⟨5987119860431988376160591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3991413240287992250773727 5987119860431988376160591)
      ·
        refine ⟨8980679790647982564240887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5987119860431988376160591 8980679790647982564240887)
        ·
          refine ⟨13471019685971973846361331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8980679790647982564240887 13471019685971973846361331)
          ·
            refine ⟨20206529528957960769541997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13471019685971973846361331 20206529528957960769541997)
            ·
              refine ⟨7577448573359235288578249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20206529528957960769541997 7577448573359235288578249)
              ·
                refine ⟨5683086430019426466433687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7577448573359235288578249 5683086430019426466433687)
                ·
                  refine ⟨8524629645029139699650531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5683086430019426466433687 8524629645029139699650531)
                  ·
                    refine ⟨12786944467543709549475797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8524629645029139699650531 12786944467543709549475797)
                    ·
                      refine ⟨299694010958055692565839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 12786944467543709549475797 299694010958055692565839)
                      ·
                        rfl

theorem cell23_583652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_583652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583652 prefixEnd_583652 := by exact prefixLift 583652
  have htrace : WordTrace (prefixWord ++ tailWord_583652) baseStart_583652 baseEnd_583652 := by
    simpa [prefixWord, tailWord_583652, baseEnd_583652] using wordTrace_append hprefix tailTrace_583652
  have hstable : (prefixWord ++ tailWord_583652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583652).length < 2 ^ (prefixWord ++ tailWord_583652).sum := by decide
  have hdescent : baseEnd_583652 < baseStart_583652 := by decide
  rcases family_descends (prefixWord ++ tailWord_583652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583679 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 3, 6, 2]
def baseStart_583679 : Nat := 118140960795 + 583679 * 2 ^ 59
def prefixEnd_583679 : Nat := 4983230072969 + 3 ^ 40 * 583679 * 2
def baseEnd_583679 : Nat := 299707874935727086928215

theorem tailTrace_583679 : CollatzResearch.WordTrace tailWord_583679 prefixEnd_583679 299707874935727086928215 := by
  unfold tailWord_583679
  simp only [CollatzResearch.WordTrace]
  refine ⟨21288522052438142282026091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14192348034958761521350727 21288522052438142282026091)
  ·
    refine ⟨31932783078657213423039137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21288522052438142282026091 31932783078657213423039137)
    ·
      refine ⟨23949587308992910067279353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31932783078657213423039137 23949587308992910067279353)
      ·
        refine ⟨17962190481744682550459515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23949587308992910067279353 17962190481744682550459515)
        ·
          refine ⟨26943285722617023825689273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17962190481744682550459515 26943285722617023825689273)
          ·
            refine ⟨20207464291962767869266955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26943285722617023825689273 20207464291962767869266955)
            ·
              refine ⟨30311196437944151803900433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20207464291962767869266955 30311196437944151803900433)
              ·
                refine ⟨22733397328458113852925325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30311196437944151803900433 22733397328458113852925325)
                ·
                  refine ⟨8525023998171792694846997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22733397328458113852925325 8525023998171792694846997)
                  ·
                    refine ⟨399610499914302782570953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8525023998171792694846997 399610499914302782570953)
                    ·
                      refine ⟨299707874935727086928215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 399610499914302782570953 299707874935727086928215)
                      ·
                        rfl

theorem cell23_583679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 6, 2].length) (baseStart_583679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583679 prefixEnd_583679 := by exact prefixLift 583679
  have htrace : WordTrace (prefixWord ++ tailWord_583679) baseStart_583679 baseEnd_583679 := by
    simpa [prefixWord, tailWord_583679, baseEnd_583679] using wordTrace_append hprefix tailTrace_583679
  have hstable : (prefixWord ++ tailWord_583679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583679).length < 2 ^ (prefixWord ++ tailWord_583679).sum := by decide
  have hdescent : baseEnd_583679 < baseStart_583679 := by decide
  rcases family_descends (prefixWord ++ tailWord_583679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583699 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 3]
def baseStart_583699 : Nat := 118140960795 + 583699 * 2 ^ 59
def prefixEnd_583699 : Nat := 4983230072969 + 3 ^ 40 * 583699 * 2
def baseEnd_583699 : Nat := 299718144548817008678123

theorem tailTrace_583699 : CollatzResearch.WordTrace tailWord_583699 prefixEnd_583699 299718144548817008678123 := by
  unfold tailWord_583699
  simp only [CollatzResearch.WordTrace]
  refine ⟨21289251512365685697754151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14192834341577123798502767 21289251512365685697754151)
  ·
    refine ⟨31933877268548528546631227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21289251512365685697754151 31933877268548528546631227)
    ·
      refine ⟨47900815902822792819946841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31933877268548528546631227 47900815902822792819946841)
      ·
        refine ⟨35925611927117094614960131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47900815902822792819946841 35925611927117094614960131)
        ·
          refine ⟨53888417890675641922440197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35925611927117094614960131 53888417890675641922440197)
          ·
            refine ⟨10104078354501682860457537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53888417890675641922440197 10104078354501682860457537)
            ·
              refine ⟨7578058765876262145343153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10104078354501682860457537 7578058765876262145343153)
              ·
                refine ⟨5683544074407196609007365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7578058765876262145343153 5683544074407196609007365)
                ·
                  refine ⟨1065664513951349364188881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5683544074407196609007365 1065664513951349364188881)
                  ·
                    refine ⟨799248385463512023141661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1065664513951349364188881 799248385463512023141661)
                    ·
                      refine ⟨299718144548817008678123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 799248385463512023141661 299718144548817008678123)
                      ·
                        rfl

theorem cell23_583699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 3].length) (baseStart_583699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583699 prefixEnd_583699 := by exact prefixLift 583699
  have htrace : WordTrace (prefixWord ++ tailWord_583699) baseStart_583699 baseEnd_583699 := by
    simpa [prefixWord, tailWord_583699, baseEnd_583699] using wordTrace_append hprefix tailTrace_583699
  have hstable : (prefixWord ++ tailWord_583699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583699).length < 2 ^ (prefixWord ++ tailWord_583699).sum := by decide
  have hdescent : baseEnd_583699 < baseStart_583699 := by decide
  rcases family_descends (prefixWord ++ tailWord_583699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583706 : List Nat := [3, 1, 1, 3, 1, 4, 1, 2, 3, 4]
def baseStart_583706 : Nat := 118140960795 + 583706 * 2 ^ 59
def prefixEnd_583706 : Nat := 4983230072969 + 3 ^ 40 * 583706 * 2
def baseEnd_583706 : Nat := 99907246304466160430197

theorem tailTrace_583706 : CollatzResearch.WordTrace tailWord_583706 prefixEnd_583706 99907246304466160430197 := by
  unfold tailWord_583706
  simp only [CollatzResearch.WordTrace]
  refine ⟨5322376705835081473314743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14193004548893550595505981 5322376705835081473314743)
  ·
    refine ⟨7983565058752622209972115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5322376705835081473314743 7983565058752622209972115)
    ·
      refine ⟨11975347588128933314958173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7983565058752622209972115 11975347588128933314958173)
      ·
        refine ⟨4490755345548349993109315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11975347588128933314958173 4490755345548349993109315)
        ·
          refine ⟨6736133018322524989663973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4490755345548349993109315 6736133018322524989663973)
          ·
            refine ⟨1263024940935473435561995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6736133018322524989663973 1263024940935473435561995)
            ·
              refine ⟨1894537411403210153342993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1263024940935473435561995 1894537411403210153342993)
              ·
                refine ⟨1420903058552407615007245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1894537411403210153342993 1420903058552407615007245)
                ·
                  refine ⟨532838646957152855627717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1420903058552407615007245 532838646957152855627717)
                  ·
                    refine ⟨99907246304466160430197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 532838646957152855627717 99907246304466160430197)
                    ·
                      rfl

theorem cell23_583706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 3, 4].length) (baseStart_583706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583706 prefixEnd_583706 := by exact prefixLift 583706
  have htrace : WordTrace (prefixWord ++ tailWord_583706) baseStart_583706 baseEnd_583706 := by
    simpa [prefixWord, tailWord_583706, baseEnd_583706] using wordTrace_append hprefix tailTrace_583706
  have hstable : (prefixWord ++ tailWord_583706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583706).length < 2 ^ (prefixWord ++ tailWord_583706).sum := by decide
  have hdescent : baseEnd_583706 < baseStart_583706 := by decide
  rcases family_descends (prefixWord ++ tailWord_583706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583713 : List Nat := [1, 2, 3, 2, 4, 2, 1, 1, 2, 1, 4]
def baseStart_583713 : Nat := 118140960795 + 583713 * 2 ^ 59
def prefixEnd_583713 : Nat := 4983230072969 + 3 ^ 40 * 583713 * 2
def baseEnd_583713 : Nat := 299725333277979953903059

theorem tailTrace_583713 : CollatzResearch.WordTrace tailWord_583713 prefixEnd_583713 299725333277979953903059 := by
  unfold tailWord_583713
  simp only [CollatzResearch.WordTrace]
  refine ⟨21289762134314966088763793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14193174756209977392509195 21289762134314966088763793)
  ·
    refine ⟨15967321600736224566572845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21289762134314966088763793 15967321600736224566572845)
    ·
      refine ⟨5987745600276084212464817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15967321600736224566572845 5987745600276084212464817)
      ·
        refine ⟨4490809200207063159348613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5987745600276084212464817 4490809200207063159348613)
        ·
          refine ⟨842026725038824342377865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4490809200207063159348613 842026725038824342377865)
          ·
            refine ⟨631520043779118256783399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 842026725038824342377865 631520043779118256783399)
            ·
              refine ⟨947280065668677385175099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 631520043779118256783399 947280065668677385175099)
              ·
                refine ⟨1420920098503016077762649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 947280065668677385175099 1420920098503016077762649)
                ·
                  refine ⟨1065690073877262058321987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1420920098503016077762649 1065690073877262058321987)
                  ·
                    refine ⟨1598535110815893087482981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1065690073877262058321987 1598535110815893087482981)
                    ·
                      refine ⟨299725333277979953903059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1598535110815893087482981 299725333277979953903059)
                      ·
                        rfl

theorem cell23_583713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_583713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583713 prefixEnd_583713 := by exact prefixLift 583713
  have htrace : WordTrace (prefixWord ++ tailWord_583713) baseStart_583713 baseEnd_583713 := by
    simpa [prefixWord, tailWord_583713, baseEnd_583713] using wordTrace_append hprefix tailTrace_583713
  have hstable : (prefixWord ++ tailWord_583713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583713).length < 2 ^ (prefixWord ++ tailWord_583713).sum := by decide
  have hdescent : baseEnd_583713 < baseStart_583713 := by decide
  rcases family_descends (prefixWord ++ tailWord_583713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583756 : List Nat := [2, 2, 1, 3, 1, 1, 3, 2, 1, 5, 2]
def baseStart_583756 : Nat := 118140960795 + 583756 * 2 ^ 59
def prefixEnd_583756 : Nat := 4983230072969 + 3 ^ 40 * 583756 * 2
def baseEnd_583756 : Nat := 299747412946123285665361

theorem tailTrace_583756 : CollatzResearch.WordTrace tailWord_583756 prefixEnd_583756 299747412946123285665361 := by
  unfold tailWord_583756
  simp only [CollatzResearch.WordTrace]
  refine ⟨10645665236579592216289561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14194220315439456288386081 10645665236579592216289561)
  ·
    refine ⟨7984248927434694162217171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10645665236579592216289561 7984248927434694162217171)
    ·
      refine ⟨11976373391152041243325757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7984248927434694162217171 11976373391152041243325757)
      ·
        refine ⟨4491140021682015466247159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11976373391152041243325757 4491140021682015466247159)
        ·
          refine ⟨6736710032523023199370739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4491140021682015466247159 6736710032523023199370739)
          ·
            refine ⟨10105065048784534799056109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6736710032523023199370739 10105065048784534799056109)
            ·
              refine ⟨3789399393294200549646041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10105065048784534799056109 3789399393294200549646041)
              ·
                refine ⟨2842049544970650412234531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3789399393294200549646041 2842049544970650412234531)
                ·
                  refine ⟨4263074317455975618351797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2842049544970650412234531 4263074317455975618351797)
                  ·
                    refine ⟨399663217261497714220481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4263074317455975618351797 399663217261497714220481)
                    ·
                      refine ⟨299747412946123285665361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 399663217261497714220481 299747412946123285665361)
                      ·
                        rfl

theorem cell23_583756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_583756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583756 prefixEnd_583756 := by exact prefixLift 583756
  have htrace : WordTrace (prefixWord ++ tailWord_583756) baseStart_583756 baseEnd_583756 := by
    simpa [prefixWord, tailWord_583756, baseEnd_583756] using wordTrace_append hprefix tailTrace_583756
  have hstable : (prefixWord ++ tailWord_583756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583756).length < 2 ^ (prefixWord ++ tailWord_583756).sum := by decide
  have hdescent : baseEnd_583756 < baseStart_583756 := by decide
  rcases family_descends (prefixWord ++ tailWord_583756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583779 : List Nat := [1, 1, 1, 5, 1, 1, 2, 4, 1, 6]
def baseStart_583779 : Nat := 118140960795 + 583779 * 2 ^ 59
def prefixEnd_583779 : Nat := 4983230072969 + 3 ^ 40 * 583779 * 2
def baseEnd_583779 : Nat := 99919741000392231892585

theorem tailTrace_583779 : CollatzResearch.WordTrace tailWord_583779 prefixEnd_583779 99919741000392231892585 := by
  unfold tailWord_583779
  simp only [CollatzResearch.WordTrace]
  refine ⟨21292169352075859360666391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14194779568050572907110927 21292169352075859360666391)
  ·
    refine ⟨31938254028113789040999587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21292169352075859360666391 31938254028113789040999587)
    ·
      refine ⟨47907381042170683561499381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31938254028113789040999587 47907381042170683561499381)
      ·
        refine ⟨4491316972703501583890567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47907381042170683561499381 4491316972703501583890567)
        ·
          refine ⟨6736975459055252375835851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4491316972703501583890567 6736975459055252375835851)
          ·
            refine ⟨10105463188582878563753777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6736975459055252375835851 10105463188582878563753777)
            ·
              refine ⟨7579097391437158922815333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10105463188582878563753777 7579097391437158922815333)
              ·
                refine ⟨1421080760894467298027875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7579097391437158922815333 1421080760894467298027875)
                ·
                  refine ⟨2131621141341700947041813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1421080760894467298027875 2131621141341700947041813)
                  ·
                    refine ⟨99919741000392231892585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2131621141341700947041813 99919741000392231892585)
                    ·
                      rfl

theorem cell23_583779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 6].length) (baseStart_583779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583779 prefixEnd_583779 := by exact prefixLift 583779
  have htrace : WordTrace (prefixWord ++ tailWord_583779) baseStart_583779 baseEnd_583779 := by
    simpa [prefixWord, tailWord_583779, baseEnd_583779] using wordTrace_append hprefix tailTrace_583779
  have hstable : (prefixWord ++ tailWord_583779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583779).length < 2 ^ (prefixWord ++ tailWord_583779).sum := by decide
  have hdescent : baseEnd_583779 < baseStart_583779 := by decide
  rcases family_descends (prefixWord ++ tailWord_583779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583780 : List Nat := [2, 3, 1, 1, 2, 1, 5, 3, 1, 1, 3]
def baseStart_583780 : Nat := 118140960795 + 583780 * 2 ^ 59
def prefixEnd_583780 : Nat := 4983230072969 + 3 ^ 40 * 583780 * 2
def baseEnd_583780 : Nat := 299759736481831191765251

theorem tailTrace_583780 : CollatzResearch.WordTrace tailWord_583780 prefixEnd_583780 299759736481831191765251 := by
  unfold tailWord_583780
  simp only [CollatzResearch.WordTrace]
  refine ⟨10646102912536118265726397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14194803883381491020968529 10646102912536118265726397)
  ·
    refine ⟨3992288592201044349647399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10646102912536118265726397 3992288592201044349647399)
    ·
      refine ⟨5988432888301566524471099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3992288592201044349647399 5988432888301566524471099)
      ·
        refine ⟨8982649332452349786706649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5988432888301566524471099 8982649332452349786706649)
        ·
          refine ⟨6736986999339262340029987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8982649332452349786706649 6736986999339262340029987)
          ·
            refine ⟨10105480499008893510044981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6736986999339262340029987 10105480499008893510044981)
            ·
              refine ⟨947388796782083766566717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10105480499008893510044981 947388796782083766566717)
              ·
                refine ⟨355270798793281412462519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 947388796782083766566717 355270798793281412462519)
                ·
                  refine ⟨532906198189922118693779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 355270798793281412462519 532906198189922118693779)
                  ·
                    refine ⟨799359297284883178040669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 532906198189922118693779 799359297284883178040669)
                    ·
                      refine ⟨299759736481831191765251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 799359297284883178040669 299759736481831191765251)
                      ·
                        rfl

theorem cell23_583780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 1, 1, 3].length) (baseStart_583780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583780 prefixEnd_583780 := by exact prefixLift 583780
  have htrace : WordTrace (prefixWord ++ tailWord_583780) baseStart_583780 baseEnd_583780 := by
    simpa [prefixWord, tailWord_583780, baseEnd_583780] using wordTrace_append hprefix tailTrace_583780
  have hstable : (prefixWord ++ tailWord_583780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583780).length < 2 ^ (prefixWord ++ tailWord_583780).sum := by decide
  have hdescent : baseEnd_583780 < baseStart_583780 := by decide
  rcases family_descends (prefixWord ++ tailWord_583780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583799 : List Nat := [1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 6]
def baseStart_583799 : Nat := 118140960795 + 583799 * 2 ^ 59
def prefixEnd_583799 : Nat := 4983230072969 + 3 ^ 40 * 583799 * 2
def baseEnd_583799 : Nat := 299769492614266617427663

theorem tailTrace_583799 : CollatzResearch.WordTrace tailWord_583799 prefixEnd_583799 299769492614266617427663 := by
  unfold tailWord_583799
  simp only [CollatzResearch.WordTrace]
  refine ⟨21292898812003402776394451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14195265874668935184262967 21292898812003402776394451)
  ·
    refine ⟨31939348218005104164591677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21292898812003402776394451 31939348218005104164591677)
    ·
      refine ⟨11977255581751914061721879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31939348218005104164591677 11977255581751914061721879)
      ·
        refine ⟨17965883372627871092582819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11977255581751914061721879 17965883372627871092582819)
        ·
          refine ⟨26948825058941806638874229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17965883372627871092582819 26948825058941806638874229)
          ·
            refine ⟨2526452349275794372394459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26948825058941806638874229 2526452349275794372394459)
            ·
              refine ⟨3789678523913691558591689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2526452349275794372394459 3789678523913691558591689)
              ·
                refine ⟨2842258892935268668943767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3789678523913691558591689 2842258892935268668943767)
                ·
                  refine ⟨4263388339402903003415651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2842258892935268668943767 4263388339402903003415651)
                  ·
                    refine ⟨6395082509104354505123477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4263388339402903003415651 6395082509104354505123477)
                    ·
                      refine ⟨299769492614266617427663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6395082509104354505123477 299769492614266617427663)
                      ·
                        rfl

theorem cell23_583799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_583799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583799 prefixEnd_583799 := by exact prefixLift 583799
  have htrace : WordTrace (prefixWord ++ tailWord_583799) baseStart_583799 baseEnd_583799 := by
    simpa [prefixWord, tailWord_583799, baseEnd_583799] using wordTrace_append hprefix tailTrace_583799
  have hstable : (prefixWord ++ tailWord_583799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583799).length < 2 ^ (prefixWord ++ tailWord_583799).sum := by decide
  have hdescent : baseEnd_583799 < baseStart_583799 := by decide
  rcases family_descends (prefixWord ++ tailWord_583799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583813 : List Nat := [1, 3, 1, 1, 5, 2, 1, 3, 2, 4]
def baseStart_583813 : Nat := 118140960795 + 583813 * 2 ^ 59
def prefixEnd_583813 : Nat := 4983230072969 + 3 ^ 40 * 583813 * 2
def baseEnd_583813 : Nat := 99925560447809854217533

theorem tailTrace_583813 : CollatzResearch.WordTrace tailWord_583813 prefixEnd_583813 99925560447809854217533 := by
  unfold tailWord_583813
  simp only [CollatzResearch.WordTrace]
  refine ⟨21293409433952683167404093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14195606289301788778269395 21293409433952683167404093)
  ·
    refine ⟨7985028537732256187776535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21293409433952683167404093 7985028537732256187776535)
    ·
      refine ⟨11977542806598384281664803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7985028537732256187776535 11977542806598384281664803)
      ·
        refine ⟨17966314209897576422497205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11977542806598384281664803 17966314209897576422497205)
        ·
          refine ⟨1684341957177897789609113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17966314209897576422497205 1684341957177897789609113)
          ·
            refine ⟨1263256467883423342206835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1684341957177897789609113 1263256467883423342206835)
            ·
              refine ⟨1894884701825135013310253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1263256467883423342206835 1894884701825135013310253)
              ·
                refine ⟨710581763184425629991345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1894884701825135013310253 710581763184425629991345)
                ·
                  refine ⟨532936322388319222493509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 710581763184425629991345 532936322388319222493509)
                  ·
                    refine ⟨99925560447809854217533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 532936322388319222493509 99925560447809854217533)
                    ·
                      rfl

theorem cell23_583813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 2, 4].length) (baseStart_583813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583813 prefixEnd_583813 := by exact prefixLift 583813
  have htrace : WordTrace (prefixWord ++ tailWord_583813) baseStart_583813 baseEnd_583813 := by
    simpa [prefixWord, tailWord_583813, baseEnd_583813] using wordTrace_append hprefix tailTrace_583813
  have hstable : (prefixWord ++ tailWord_583813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583813).length < 2 ^ (prefixWord ++ tailWord_583813).sum := by decide
  have hdescent : baseEnd_583813 < baseStart_583813 := by decide
  rcases family_descends (prefixWord ++ tailWord_583813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583816 : List Nat := [2, 1, 3, 4, 1, 1, 2, 1, 1, 1, 6]
def baseStart_583816 : Nat := 118140960795 + 583816 * 2 ^ 59
def prefixEnd_583816 : Nat := 4983230072969 + 3 ^ 40 * 583816 * 2
def baseEnd_583816 : Nat := 299778221785393050915085

theorem tailTrace_583816 : CollatzResearch.WordTrace tailWord_583816 prefixEnd_583816 299778221785393050915085 := by
  unfold tailWord_583816
  simp only [CollatzResearch.WordTrace]
  refine ⟨10646759426470907339881651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14195679235294543119842201 10646759426470907339881651)
  ·
    refine ⟨15970139139706361009822477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10646759426470907339881651 15970139139706361009822477)
    ·
      refine ⟨5988802177389885378683429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15970139139706361009822477 5988802177389885378683429)
      ·
        refine ⟨1122900408260603508503143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5988802177389885378683429 1122900408260603508503143)
        ·
          refine ⟨1684350612390905262754715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1122900408260603508503143 1684350612390905262754715)
          ·
            refine ⟨2526525918586357894132073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1684350612390905262754715 2526525918586357894132073)
            ·
              refine ⟨1894894438939768420599055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2526525918586357894132073 1894894438939768420599055)
              ·
                refine ⟨2842341658409652630898583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1894894438939768420599055 2842341658409652630898583)
                ·
                  refine ⟨4263512487614478946347875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2842341658409652630898583 4263512487614478946347875)
                  ·
                    refine ⟨6395268731421718419521813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4263512487614478946347875 6395268731421718419521813)
                    ·
                      refine ⟨299778221785393050915085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6395268731421718419521813 299778221785393050915085)
                      ·
                        rfl

theorem cell23_583816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_583816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583816 prefixEnd_583816 := by exact prefixLift 583816
  have htrace : WordTrace (prefixWord ++ tailWord_583816) baseStart_583816 baseEnd_583816 := by
    simpa [prefixWord, tailWord_583816, baseEnd_583816] using wordTrace_append hprefix tailTrace_583816
  have hstable : (prefixWord ++ tailWord_583816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583816).length < 2 ^ (prefixWord ++ tailWord_583816).sum := by decide
  have hdescent : baseEnd_583816 < baseStart_583816 := by decide
  rcases family_descends (prefixWord ++ tailWord_583816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583840 : List Nat := [2, 1, 1, 4, 2, 3, 3, 1, 1, 2, 3]
def baseStart_583840 : Nat := 118140960795 + 583840 * 2 ^ 59
def prefixEnd_583840 : Nat := 4983230072969 + 3 ^ 40 * 583840 * 2
def baseEnd_583840 : Nat := 299790545321100957014975

theorem tailTrace_583840 : CollatzResearch.WordTrace tailWord_583840 prefixEnd_583840 299790545321100957014975 := by
  unfold tailWord_583840
  simp only [CollatzResearch.WordTrace]
  refine ⟨10647197102427433389318487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14196262803236577852424649 10647197102427433389318487)
  ·
    refine ⟨15970795653641150083977731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10647197102427433389318487 15970795653641150083977731)
    ·
      refine ⟨23956193480461725125966597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15970795653641150083977731 23956193480461725125966597)
      ·
        refine ⟨4491786277586573461118737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23956193480461725125966597 4491786277586573461118737)
        ·
          refine ⟨3368839708189930095839053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4491786277586573461118737 3368839708189930095839053)
          ·
            refine ⟨1263314890571223785939645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3368839708189930095839053 1263314890571223785939645)
            ·
              refine ⟨473743083964208919727367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1263314890571223785939645 473743083964208919727367)
              ·
                refine ⟨710614625946313379591051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 473743083964208919727367 710614625946313379591051)
                ·
                  refine ⟨1065921938919470069386577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 710614625946313379591051 1065921938919470069386577)
                  ·
                    refine ⟨799441454189602552039933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1065921938919470069386577 799441454189602552039933)
                    ·
                      refine ⟨299790545321100957014975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 799441454189602552039933 299790545321100957014975)
                      ·
                        rfl

theorem cell23_583840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_583840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583840 prefixEnd_583840 := by exact prefixLift 583840
  have htrace : WordTrace (prefixWord ++ tailWord_583840) baseStart_583840 baseEnd_583840 := by
    simpa [prefixWord, tailWord_583840, baseEnd_583840] using wordTrace_append hprefix tailTrace_583840
  have hstable : (prefixWord ++ tailWord_583840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583840).length < 2 ^ (prefixWord ++ tailWord_583840).sum := by decide
  have hdescent : baseEnd_583840 < baseStart_583840 := by decide
  rcases family_descends (prefixWord ++ tailWord_583840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583863 : List Nat := [1, 1, 3, 1, 4, 2, 1, 2, 3, 3, 2]
def baseStart_583863 : Nat := 118140960795 + 583863 * 2 ^ 59
def prefixEnd_583863 : Nat := 4983230072969 + 3 ^ 40 * 583863 * 2
def baseEnd_583863 : Nat := 299802355376154367027369

theorem tailTrace_583863 : CollatzResearch.WordTrace tailWord_583863 prefixEnd_583863 299802355376154367027369 := by
  unfold tailWord_583863
  simp only [CollatzResearch.WordTrace]
  refine ⟨21295233083771541706724243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14196822055847694471149495 21295233083771541706724243)
  ·
    refine ⟨31942849625657312560086365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21295233083771541706724243 31942849625657312560086365)
    ·
      refine ⟨11978568609621492210032387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31942849625657312560086365 11978568609621492210032387)
      ·
        refine ⟨17967852914432238315048581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11978568609621492210032387 17967852914432238315048581)
        ·
          refine ⟨3368972421456044684071609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17967852914432238315048581 3368972421456044684071609)
          ·
            refine ⟨2526729316092033513053707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3368972421456044684071609 2526729316092033513053707)
            ·
              refine ⟨3790093974138050269580561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2526729316092033513053707 3790093974138050269580561)
              ·
                refine ⟨2842570480603537702185421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3790093974138050269580561 2842570480603537702185421)
                ·
                  refine ⟨1065963930226326638319533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2842570480603537702185421 1065963930226326638319533)
                  ·
                    refine ⟨399736473834872489369825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1065963930226326638319533 399736473834872489369825)
                    ·
                      refine ⟨299802355376154367027369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 399736473834872489369825 299802355376154367027369)
                      ·
                        rfl

theorem cell23_583863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 3, 2].length) (baseStart_583863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583863 prefixEnd_583863 := by exact prefixLift 583863
  have htrace : WordTrace (prefixWord ++ tailWord_583863) baseStart_583863 baseEnd_583863 := by
    simpa [prefixWord, tailWord_583863, baseEnd_583863] using wordTrace_append hprefix tailTrace_583863
  have hstable : (prefixWord ++ tailWord_583863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583863).length < 2 ^ (prefixWord ++ tailWord_583863).sum := by decide
  have hdescent : baseEnd_583863 < baseStart_583863 := by decide
  rcases family_descends (prefixWord ++ tailWord_583863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583870 : List Nat := [4, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3]
def baseStart_583870 : Nat := 118140960795 + 583870 * 2 ^ 59
def prefixEnd_583870 : Nat := 4983230072969 + 3 ^ 40 * 583870 * 2
def baseEnd_583870 : Nat := 299805949740735839639837

theorem tailTrace_583870 : CollatzResearch.WordTrace tailWord_583870 prefixEnd_583870 299805949740735839639837 := by
  unfold tailWord_583870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2661936049343272737778633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14196992263164121268152709 2661936049343272737778633)
  ·
    refine ⟨1996452037007454553333975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2661936049343272737778633 1996452037007454553333975)
    ·
      refine ⟨2994678055511181830000963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1996452037007454553333975 2994678055511181830000963)
      ·
        refine ⟨4492017083266772745001445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2994678055511181830000963 4492017083266772745001445)
        ·
          refine ⟨842253203112519889687771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4492017083266772745001445 842253203112519889687771)
          ·
            refine ⟨1263379804668779834531657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842253203112519889687771 1263379804668779834531657)
            ·
              refine ⟨947534853501584875898743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1263379804668779834531657 947534853501584875898743)
              ·
                refine ⟨1421302280252377313848115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 947534853501584875898743 1421302280252377313848115)
                ·
                  refine ⟨2131953420378565970772173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1421302280252377313848115 2131953420378565970772173)
                  ·
                    refine ⟨799482532641962239039565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2131953420378565970772173 799482532641962239039565)
                    ·
                      refine ⟨299805949740735839639837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 799482532641962239039565 299805949740735839639837)
                      ·
                        rfl

theorem cell23_583870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_583870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583870 prefixEnd_583870 := by exact prefixLift 583870
  have htrace : WordTrace (prefixWord ++ tailWord_583870) baseStart_583870 baseEnd_583870 := by
    simpa [prefixWord, tailWord_583870, baseEnd_583870] using wordTrace_append hprefix tailTrace_583870
  have hstable : (prefixWord ++ tailWord_583870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583870).length < 2 ^ (prefixWord ++ tailWord_583870).sum := by decide
  have hdescent : baseEnd_583870 < baseStart_583870 := by decide
  rcases family_descends (prefixWord ++ tailWord_583870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583916 : List Nat := [2, 2, 1, 1, 2, 3, 4, 1, 7]
def baseStart_583916 : Nat := 118140960795 + 583916 * 2 ^ 59
def prefixEnd_583916 : Nat := 4983230072969 + 3 ^ 40 * 583916 * 2
def baseEnd_583916 : Nat := 33314396650093628851625

theorem tailTrace_583916 : CollatzResearch.WordTrace tailWord_583916 prefixEnd_583916 33314396650093628851625 := by
  unfold tailWord_583916
  simp only [CollatzResearch.WordTrace]
  refine ⟨10648583076289765879201801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14198110768386354505602401 10648583076289765879201801)
  ·
    refine ⟨7986437307217324409401351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10648583076289765879201801 7986437307217324409401351)
    ·
      refine ⟨11979655960825986614102027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7986437307217324409401351 11979655960825986614102027)
      ·
        refine ⟨17969483941238979921153041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11979655960825986614102027 17969483941238979921153041)
        ·
          refine ⟨13477112955929234940864781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17969483941238979921153041 13477112955929234940864781)
          ·
            refine ⟨5053917358473463102824293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13477112955929234940864781 5053917358473463102824293)
            ·
              refine ⟨947609504713774331779555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5053917358473463102824293 947609504713774331779555)
              ·
                refine ⟨1421414257070661497669333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 947609504713774331779555 1421414257070661497669333)
                ·
                  refine ⟨33314396650093628851625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1421414257070661497669333 33314396650093628851625)
                  ·
                    rfl

theorem cell23_583916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 7].length) (baseStart_583916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583916 prefixEnd_583916 := by exact prefixLift 583916
  have htrace : WordTrace (prefixWord ++ tailWord_583916) baseStart_583916 baseEnd_583916 := by
    simpa [prefixWord, tailWord_583916, baseEnd_583916] using wordTrace_append hprefix tailTrace_583916
  have hstable : (prefixWord ++ tailWord_583916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583916).length < 2 ^ (prefixWord ++ tailWord_583916).sum := by decide
  have hdescent : baseEnd_583916 < baseStart_583916 := by decide
  rcases family_descends (prefixWord ++ tailWord_583916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583946 : List Nat := [3, 1, 2, 2, 1, 1, 4, 1, 1, 7]
def baseStart_583946 : Nat := 118140960795 + 583946 * 2 ^ 59
def prefixEnd_583946 : Nat := 4983230072969 + 3 ^ 40 * 583946 * 2
def baseEnd_583946 : Nat := 99948324756825847429829

theorem tailTrace_583946 : CollatzResearch.WordTrace tailWord_583946 prefixEnd_583946 99948324756825847429829 := by
  unfold tailWord_583946
  simp only [CollatzResearch.WordTrace]
  refine ⟨5324565085617711720498923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14198840228313897921330461 5324565085617711720498923)
  ·
    refine ⟨7986847628426567580748385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5324565085617711720498923 7986847628426567580748385)
    ·
      refine ⟨5990135721319925685561289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7986847628426567580748385 5990135721319925685561289)
      ·
        refine ⟨4492601790989944264170967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5990135721319925685561289 4492601790989944264170967)
        ·
          refine ⟨6738902686484916396256451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4492601790989944264170967 6738902686484916396256451)
          ·
            refine ⟨10108354029727374594384677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6738902686484916396256451 10108354029727374594384677)
            ·
              refine ⟨1895316380573882736447127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10108354029727374594384677 1895316380573882736447127)
              ·
                refine ⟨2842974570860824104670691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1895316380573882736447127 2842974570860824104670691)
                ·
                  refine ⟨4264461856291236157006037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2842974570860824104670691 4264461856291236157006037)
                  ·
                    refine ⟨99948324756825847429829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4264461856291236157006037 99948324756825847429829)
                    ·
                      rfl

theorem cell23_583946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_583946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583946 prefixEnd_583946 := by exact prefixLift 583946
  have htrace : WordTrace (prefixWord ++ tailWord_583946) baseStart_583946 baseEnd_583946 := by
    simpa [prefixWord, tailWord_583946, baseEnd_583946] using wordTrace_append hprefix tailTrace_583946
  have hstable : (prefixWord ++ tailWord_583946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583946).length < 2 ^ (prefixWord ++ tailWord_583946).sum := by decide
  have hdescent : baseEnd_583946 < baseStart_583946 := by decide
  rcases family_descends (prefixWord ++ tailWord_583946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583973 : List Nat := [1, 3, 1, 2, 5, 1, 1, 1, 1, 2, 5]
def baseStart_583973 : Nat := 118140960795 + 583973 * 2 ^ 59
def prefixEnd_583973 : Nat := 4983230072969 + 3 ^ 40 * 583973 * 2
def baseEnd_583973 : Nat := 299858838248148936651863

theorem tailTrace_583973 : CollatzResearch.WordTrace tailWord_583973 prefixEnd_583973 299858838248148936651863 := by
  unfold tailWord_583973
  simp only [CollatzResearch.WordTrace]
  refine ⟨21299245113373030493228573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14199496742248686995485715 21299245113373030493228573)
  ·
    refine ⟨7987216917514886434960715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21299245113373030493228573 7987216917514886434960715)
    ·
      refine ⟨11980825376272329652441073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7987216917514886434960715 11980825376272329652441073)
      ·
        refine ⟨8985619032204247239330805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11980825376272329652441073 8985619032204247239330805)
        ·
          refine ⟨842401784269148178687263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8985619032204247239330805 842401784269148178687263)
          ·
            refine ⟨1263602676403722268030895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842401784269148178687263 1263602676403722268030895)
            ·
              refine ⟨1895404014605583402046343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1263602676403722268030895 1895404014605583402046343)
              ·
                refine ⟨2843106021908375103069515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1895404014605583402046343 2843106021908375103069515)
                ·
                  refine ⟨4264659032862562654604273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2843106021908375103069515 4264659032862562654604273)
                  ·
                    refine ⟨3198494274646921990953205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4264659032862562654604273 3198494274646921990953205)
                    ·
                      refine ⟨299858838248148936651863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3198494274646921990953205 299858838248148936651863)
                      ·
                        rfl

theorem cell23_583973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_583973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583973 prefixEnd_583973 := by exact prefixLift 583973
  have htrace : WordTrace (prefixWord ++ tailWord_583973) baseStart_583973 baseEnd_583973 := by
    simpa [prefixWord, tailWord_583973, baseEnd_583973] using wordTrace_append hprefix tailTrace_583973
  have hstable : (prefixWord ++ tailWord_583973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583973).length < 2 ^ (prefixWord ++ tailWord_583973).sum := by decide
  have hdescent : baseEnd_583973 < baseStart_583973 := by decide
  rcases family_descends (prefixWord ++ tailWord_583973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583978 : List Nat := [3, 1, 4, 2, 3, 1, 2, 1, 2, 2, 2]
def baseStart_583978 : Nat := 118140960795 + 583978 * 2 ^ 59
def prefixEnd_583978 : Nat := 4983230072969 + 3 ^ 40 * 583978 * 2
def baseEnd_583978 : Nat := 299861405651421417089341

theorem tailTrace_583978 : CollatzResearch.WordTrace tailWord_583978 prefixEnd_583978 299861405651421417089341 := by
  unfold tailWord_583978
  simp only [CollatzResearch.WordTrace]
  refine ⟨5324856869588729086790147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14199618318903277564773725 5324856869588729086790147)
  ·
    refine ⟨7987285304383093630185221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5324856869588729086790147 7987285304383093630185221)
    ·
      refine ⟨1497615994571830055659729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7987285304383093630185221 1497615994571830055659729)
      ·
        refine ⟨1123211995928872541744797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1497615994571830055659729 1123211995928872541744797)
        ·
          refine ⟨421204498473327203154299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1123211995928872541744797 421204498473327203154299)
          ·
            refine ⟨631806747709990804731449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421204498473327203154299 631806747709990804731449)
            ·
              refine ⟨473855060782493103548587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 631806747709990804731449 473855060782493103548587)
              ·
                refine ⟨710782591173739655322881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 473855060782493103548587 710782591173739655322881)
                ·
                  refine ⟨533086943380304741492161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 710782591173739655322881 533086943380304741492161)
                  ·
                    refine ⟨399815207535228556119121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 533086943380304741492161 399815207535228556119121)
                    ·
                      refine ⟨299861405651421417089341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 399815207535228556119121 299861405651421417089341)
                      ·
                        rfl

theorem cell23_583978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_583978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583978 prefixEnd_583978 := by exact prefixLift 583978
  have htrace : WordTrace (prefixWord ++ tailWord_583978) baseStart_583978 baseEnd_583978 := by
    simpa [prefixWord, tailWord_583978, baseEnd_583978] using wordTrace_append hprefix tailTrace_583978
  have hstable : (prefixWord ++ tailWord_583978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583978).length < 2 ^ (prefixWord ++ tailWord_583978).sum := by decide
  have hdescent : baseEnd_583978 < baseStart_583978 := by decide
  rcases family_descends (prefixWord ++ tailWord_583978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583983 : List Nat := [1, 1, 2, 1, 2, 1, 4, 3, 2, 4, 2]
def baseStart_583983 : Nat := 118140960795 + 583983 * 2 ^ 59
def prefixEnd_583983 : Nat := 4983230072969 + 3 ^ 40 * 583983 * 2
def baseEnd_583983 : Nat := 299863973054693897526817

theorem tailTrace_583983 : CollatzResearch.WordTrace tailWord_583983 prefixEnd_583983 299863973054693897526817 := by
  unfold tailWord_583983
  simp only [CollatzResearch.WordTrace]
  refine ⟨21299609843336802201092603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14199739895557868134061735 21299609843336802201092603)
  ·
    refine ⟨31949414765005203301638905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21299609843336802201092603 31949414765005203301638905)
    ·
      refine ⟨23962061073753902476229179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31949414765005203301638905 23962061073753902476229179)
      ·
        refine ⟨35943091610630853714343769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23962061073753902476229179 35943091610630853714343769)
        ·
          refine ⟨26957318707973140285757827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35943091610630853714343769 26957318707973140285757827)
          ·
            refine ⟨40435978061959710428636741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26957318707973140285757827 40435978061959710428636741)
            ·
              refine ⟨7581745886617445705369389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40435978061959710428636741 7581745886617445705369389)
              ·
                refine ⟨2843154707481542139513521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7581745886617445705369389 2843154707481542139513521)
                ·
                  refine ⟨2132366030611156604635141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2843154707481542139513521 2132366030611156604635141)
                  ·
                    refine ⟨399818630739591863369089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2132366030611156604635141 399818630739591863369089)
                    ·
                      refine ⟨299863973054693897526817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 399818630739591863369089 299863973054693897526817)
                      ·
                        rfl

theorem cell23_583983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 4, 2].length) (baseStart_583983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_583983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_583983 prefixEnd_583983 := by exact prefixLift 583983
  have htrace : WordTrace (prefixWord ++ tailWord_583983) baseStart_583983 baseEnd_583983 := by
    simpa [prefixWord, tailWord_583983, baseEnd_583983] using wordTrace_append hprefix tailTrace_583983
  have hstable : (prefixWord ++ tailWord_583983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583983).length < 2 ^ (prefixWord ++ tailWord_583983).sum := by decide
  have hdescent : baseEnd_583983 < baseStart_583983 := by decide
  rcases family_descends (prefixWord ++ tailWord_583983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584003 : List Nat := [1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 3]
def baseStart_584003 : Nat := 118140960795 + 584003 * 2 ^ 59
def prefixEnd_584003 : Nat := 4983230072969 + 3 ^ 40 * 584003 * 2
def baseEnd_584003 : Nat := 299874242667783819276725

theorem tailTrace_584003 : CollatzResearch.WordTrace tailWord_584003 prefixEnd_584003 299874242667783819276725 := by
  unfold tailWord_584003
  simp only [CollatzResearch.WordTrace]
  refine ⟨21300339303264345616820663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14200226202176230411213775 21300339303264345616820663)
  ·
    refine ⟨31950508954896518425230995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21300339303264345616820663 31950508954896518425230995)
    ·
      refine ⟨47925763432344777637846493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31950508954896518425230995 47925763432344777637846493)
      ·
        refine ⟨17972161287129291614192435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47925763432344777637846493 17972161287129291614192435)
        ·
          refine ⟨26958241930693937421288653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17972161287129291614192435 26958241930693937421288653)
          ·
            refine ⟨10109340724010226532983245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26958241930693937421288653 10109340724010226532983245)
            ·
              refine ⟨3791002771503834949868717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10109340724010226532983245 3791002771503834949868717)
              ·
                refine ⟨1421626039313938106200769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3791002771503834949868717 1421626039313938106200769)
                ·
                  refine ⟨1066219529485453579650577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1421626039313938106200769 1066219529485453579650577)
                  ·
                    refine ⟨799664647114090184737933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1066219529485453579650577 799664647114090184737933)
                    ·
                      refine ⟨299874242667783819276725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 799664647114090184737933 299874242667783819276725)
                      ·
                        rfl

theorem cell23_584003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 3].length) (baseStart_584003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584003 prefixEnd_584003 := by exact prefixLift 584003
  have htrace : WordTrace (prefixWord ++ tailWord_584003) baseStart_584003 baseEnd_584003 := by
    simpa [prefixWord, tailWord_584003, baseEnd_584003] using wordTrace_append hprefix tailTrace_584003
  have hstable : (prefixWord ++ tailWord_584003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584003).length < 2 ^ (prefixWord ++ tailWord_584003).sum := by decide
  have hdescent : baseEnd_584003 < baseStart_584003 := by decide
  rcases family_descends (prefixWord ++ tailWord_584003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584020 : List Nat := [2, 4, 1, 1, 2, 2, 2, 2, 2, 2, 3]
def baseStart_584020 : Nat := 118140960795 + 584020 * 2 ^ 59
def prefixEnd_584020 : Nat := 4983230072969 + 3 ^ 40 * 584020 * 2
def baseEnd_584020 : Nat := 299882971838910252764147

theorem tailTrace_584020 : CollatzResearch.WordTrace tailWord_584020 prefixEnd_584020 299882971838910252764147 := by
  unfold tailWord_584020
  simp only [CollatzResearch.WordTrace]
  refine ⟨10650479672101378760094757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14200639562801838346793009 10650479672101378760094757)
  ·
    refine ⟨1996964938519008517517767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10650479672101378760094757 1996964938519008517517767)
    ·
      refine ⟨2995447407778512776276651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1996964938519008517517767 2995447407778512776276651)
      ·
        refine ⟨4493171111667769164414977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2995447407778512776276651 4493171111667769164414977)
        ·
          refine ⟨3369878333750826873311233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4493171111667769164414977 3369878333750826873311233)
          ·
            refine ⟨2527408750313120154983425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3369878333750826873311233 2527408750313120154983425)
            ·
              refine ⟨1895556562734840116237569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2527408750313120154983425 1895556562734840116237569)
              ·
                refine ⟨1421667422051130087178177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1895556562734840116237569 1421667422051130087178177)
                ·
                  refine ⟨1066250566538347565383633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1421667422051130087178177 1066250566538347565383633)
                  ·
                    refine ⟨799687924903760674037725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1066250566538347565383633 799687924903760674037725)
                    ·
                      refine ⟨299882971838910252764147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 799687924903760674037725 299882971838910252764147)
                      ·
                        rfl

theorem cell23_584020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_584020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584020 prefixEnd_584020 := by exact prefixLift 584020
  have htrace : WordTrace (prefixWord ++ tailWord_584020) baseStart_584020 baseEnd_584020 := by
    simpa [prefixWord, tailWord_584020, baseEnd_584020] using wordTrace_append hprefix tailTrace_584020
  have hstable : (prefixWord ++ tailWord_584020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584020).length < 2 ^ (prefixWord ++ tailWord_584020).sum := by decide
  have hdescent : baseEnd_584020 < baseStart_584020 := by decide
  rcases family_descends (prefixWord ++ tailWord_584020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584023 : List Nat := [1, 1, 3, 2, 3, 1, 4, 2, 6]
def baseStart_584023 : Nat := 118140960795 + 584023 * 2 ^ 59
def prefixEnd_584023 : Nat := 4983230072969 + 3 ^ 40 * 584023 * 2
def baseEnd_584023 : Nat := 33320501364541526780737

theorem tailTrace_584023 : CollatzResearch.WordTrace tailWord_584023 prefixEnd_584023 33320501364541526780737 := by
  unfold tailWord_584023
  simp only [CollatzResearch.WordTrace]
  refine ⟨21301068763191889032548723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14200712508794592688365815 21301068763191889032548723)
  ·
    refine ⟨31951603144787833548823085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21301068763191889032548723 31951603144787833548823085)
    ·
      refine ⟨11981851179295437580808657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31951603144787833548823085 11981851179295437580808657)
      ·
        refine ⟨8986388384471578185606493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11981851179295437580808657 8986388384471578185606493)
        ·
          refine ⟨3369895644176841819602435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8986388384471578185606493 3369895644176841819602435)
          ·
            refine ⟨5054843466265262729403653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3369895644176841819602435 5054843466265262729403653)
            ·
              refine ⟨947783149924736761763185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5054843466265262729403653 947783149924736761763185)
              ·
                refine ⟨710837362443552571322389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 947783149924736761763185 710837362443552571322389)
                ·
                  refine ⟨33320501364541526780737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 710837362443552571322389 33320501364541526780737)
                  ·
                    rfl

theorem cell23_584023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 6].length) (baseStart_584023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584023 prefixEnd_584023 := by exact prefixLift 584023
  have htrace : WordTrace (prefixWord ++ tailWord_584023) baseStart_584023 baseEnd_584023 := by
    simpa [prefixWord, tailWord_584023, baseEnd_584023] using wordTrace_append hprefix tailTrace_584023
  have hstable : (prefixWord ++ tailWord_584023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584023).length < 2 ^ (prefixWord ++ tailWord_584023).sum := by decide
  have hdescent : baseEnd_584023 < baseStart_584023 := by decide
  rcases family_descends (prefixWord ++ tailWord_584023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584026 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6]
def baseStart_584026 : Nat := 118140960795 + 584026 * 2 ^ 59
def prefixEnd_584026 : Nat := 4983230072969 + 3 ^ 40 * 584026 * 2
def baseEnd_584026 : Nat := 299886052722837229289119

theorem tailTrace_584026 : CollatzResearch.WordTrace tailWord_584026 prefixEnd_584026 299886052722837229289119 := by
  unfold tailWord_584026
  simp only [CollatzResearch.WordTrace]
  refine ⟨5325294545545255136226983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14200785454787347029938621 5325294545545255136226983)
  ·
    refine ⟨7987941818317882704340475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5325294545545255136226983 7987941818317882704340475)
    ·
      refine ⟨11981912727476824056510713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7987941818317882704340475 11981912727476824056510713)
      ·
        refine ⟨8986434545607618042383035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11981912727476824056510713 8986434545607618042383035)
        ·
          refine ⟨13479651818411427063574553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8986434545607618042383035 13479651818411427063574553)
          ·
            refine ⟨10109738863808570297680915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13479651818411427063574553 10109738863808570297680915)
            ·
              refine ⟨15164608295712855446521373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10109738863808570297680915 15164608295712855446521373)
              ·
                refine ⟨5686728110892320792445515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15164608295712855446521373 5686728110892320792445515)
                ·
                  refine ⟨8530092166338481188668273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5686728110892320792445515 8530092166338481188668273)
                  ·
                    refine ⟨6397569124753860891501205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8530092166338481188668273 6397569124753860891501205)
                    ·
                      refine ⟨299886052722837229289119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6397569124753860891501205 299886052722837229289119)
                      ·
                        rfl

theorem cell23_584026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_584026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584026 prefixEnd_584026 := by exact prefixLift 584026
  have htrace : WordTrace (prefixWord ++ tailWord_584026) baseStart_584026 baseEnd_584026 := by
    simpa [prefixWord, tailWord_584026, baseEnd_584026] using wordTrace_append hprefix tailTrace_584026
  have hstable : (prefixWord ++ tailWord_584026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584026).length < 2 ^ (prefixWord ++ tailWord_584026).sum := by decide
  have hdescent : baseEnd_584026 < baseStart_584026 := by decide
  rcases family_descends (prefixWord ++ tailWord_584026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584043 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 3, 5, 2]
def baseStart_584043 : Nat := 118140960795 + 584043 * 2 ^ 59
def prefixEnd_584043 : Nat := 4983230072969 + 3 ^ 40 * 584043 * 2
def baseEnd_584043 : Nat := 299894781893963662776541

theorem tailTrace_584043 : CollatzResearch.WordTrace tailWord_584043 prefixEnd_584043 299894781893963662776541 := by
  unfold tailWord_584043
  simp only [CollatzResearch.WordTrace]
  refine ⟨21301798223119432448276783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14201198815412954965517855 21301798223119432448276783)
  ·
    refine ⟨31952697334679148672415175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21301798223119432448276783 31952697334679148672415175)
    ·
      refine ⟨47929046002018723008622763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31952697334679148672415175 47929046002018723008622763)
      ·
        refine ⟨71893569003028084512934145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47929046002018723008622763 71893569003028084512934145)
        ·
          refine ⟨53920176752271063384700609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71893569003028084512934145 53920176752271063384700609)
          ·
            refine ⟨40440132564203297538525457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53920176752271063384700609 40440132564203297538525457)
            ·
              refine ⟨30330099423152473153894093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40440132564203297538525457 30330099423152473153894093)
              ·
                refine ⟨11373787283682177432710285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30330099423152473153894093 11373787283682177432710285)
                ·
                  refine ⟨4265170231380816537266357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11373787283682177432710285 4265170231380816537266357)
                  ·
                    refine ⟨399859709191951550368721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4265170231380816537266357 399859709191951550368721)
                    ·
                      refine ⟨299894781893963662776541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 399859709191951550368721 299894781893963662776541)
                      ·
                        rfl

theorem cell23_584043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 5, 2].length) (baseStart_584043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584043 prefixEnd_584043 := by exact prefixLift 584043
  have htrace : WordTrace (prefixWord ++ tailWord_584043) baseStart_584043 baseEnd_584043 := by
    simpa [prefixWord, tailWord_584043, baseEnd_584043] using wordTrace_append hprefix tailTrace_584043
  have hstable : (prefixWord ++ tailWord_584043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584043).length < 2 ^ (prefixWord ++ tailWord_584043).sum := by decide
  have hdescent : baseEnd_584043 < baseStart_584043 := by decide
  rcases family_descends (prefixWord ++ tailWord_584043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584050 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 5, 1, 3]
def baseStart_584050 : Nat := 118140960795 + 584050 * 2 ^ 59
def prefixEnd_584050 : Nat := 4983230072969 + 3 ^ 40 * 584050 * 2
def baseEnd_584050 : Nat := 299898376258545135389009

theorem tailTrace_584050 : CollatzResearch.WordTrace tailWord_584050 prefixEnd_584050 299898376258545135389009 := by
  unfold tailWord_584050
  simp only [CollatzResearch.WordTrace]
  refine ⟨5325513383523518160945401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14201369022729381762521069 5325513383523518160945401)
  ·
    refine ⟨3994135037642638620709051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5325513383523518160945401 3994135037642638620709051)
    ·
      refine ⟨5991202556463957931063577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3994135037642638620709051 5991202556463957931063577)
      ·
        refine ⟨4493401917347968448297683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5991202556463957931063577 4493401917347968448297683)
        ·
          refine ⟨6740102876021952672446525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4493401917347968448297683 6740102876021952672446525)
          ·
            refine ⟨2527538578508232252167447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6740102876021952672446525 2527538578508232252167447)
            ·
              refine ⟨3791307867762348378251171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2527538578508232252167447 3791307867762348378251171)
              ·
                refine ⟨5686961801643522567376757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3791307867762348378251171 5686961801643522567376757)
                ·
                  refine ⟨533152668904080240691571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5686961801643522567376757 533152668904080240691571)
                  ·
                    refine ⟨799729003356120361037357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 533152668904080240691571 799729003356120361037357)
                    ·
                      refine ⟨299898376258545135389009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 799729003356120361037357 299898376258545135389009)
                      ·
                        rfl

theorem cell23_584050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_584050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584050 prefixEnd_584050 := by exact prefixLift 584050
  have htrace : WordTrace (prefixWord ++ tailWord_584050) baseStart_584050 baseEnd_584050 := by
    simpa [prefixWord, tailWord_584050, baseEnd_584050] using wordTrace_append hprefix tailTrace_584050
  have hstable : (prefixWord ++ tailWord_584050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584050).length < 2 ^ (prefixWord ++ tailWord_584050).sum := by decide
  have hdescent : baseEnd_584050 < baseStart_584050 := by decide
  rcases family_descends (prefixWord ++ tailWord_584050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584060 : List Nat := [2, 2, 2, 1, 1, 1, 2, 5, 2, 3, 2]
def baseStart_584060 : Nat := 118140960795 + 584060 * 2 ^ 59
def prefixEnd_584060 : Nat := 4983230072969 + 3 ^ 40 * 584060 * 2
def baseEnd_584060 : Nat := 299903511065090096263963

theorem tailTrace_584060 : CollatzResearch.WordTrace tailWord_584060 prefixEnd_584060 299903511065090096263963 := by
  unfold tailWord_584060
  simp only [CollatzResearch.WordTrace]
  refine ⟨10651209132028922175822817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14201612176038562901097089 10651209132028922175822817)
  ·
    refine ⟨7988406849021691631867113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10651209132028922175822817 7988406849021691631867113)
    ·
      refine ⟨5991305136766268723900335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7988406849021691631867113 5991305136766268723900335)
      ·
        refine ⟨8986957705149403085850503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5991305136766268723900335 8986957705149403085850503)
        ·
          refine ⟨13480436557724104628775755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8986957705149403085850503 13480436557724104628775755)
          ·
            refine ⟨20220654836586156943163633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13480436557724104628775755 20220654836586156943163633)
            ·
              refine ⟨15165491127439617707372725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20220654836586156943163633 15165491127439617707372725)
              ·
                refine ⟨1421764793197464160066193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15165491127439617707372725 1421764793197464160066193)
                ·
                  refine ⟨1066323594898098120049645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1421764793197464160066193 1066323594898098120049645)
                  ·
                    refine ⟨399871348086786795018617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1066323594898098120049645 399871348086786795018617)
                    ·
                      refine ⟨299903511065090096263963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 399871348086786795018617 299903511065090096263963)
                      ·
                        rfl

theorem cell23_584060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 2, 3, 2].length) (baseStart_584060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584060 prefixEnd_584060 := by exact prefixLift 584060
  have htrace : WordTrace (prefixWord ++ tailWord_584060) baseStart_584060 baseEnd_584060 := by
    simpa [prefixWord, tailWord_584060, baseEnd_584060] using wordTrace_append hprefix tailTrace_584060
  have hstable : (prefixWord ++ tailWord_584060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584060).length < 2 ^ (prefixWord ++ tailWord_584060).sum := by decide
  have hdescent : baseEnd_584060 < baseStart_584060 := by decide
  rcases family_descends (prefixWord ++ tailWord_584060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584074 : List Nat := [3, 1, 2, 5, 2, 1, 1, 2, 6]
def baseStart_584074 : Nat := 118140960795 + 584074 * 2 ^ 59
def prefixEnd_584074 : Nat := 4983230072969 + 3 ^ 40 * 584074 * 2
def baseEnd_584074 : Nat := 33323411088250337943211

theorem tailTrace_584074 : CollatzResearch.WordTrace tailWord_584074 prefixEnd_584074 33323411088250337943211 := by
  unfold tailWord_584074
  simp only [CollatzResearch.WordTrace]
  refine ⟨5325732221501781185663819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14201952590671416495103517 5325732221501781185663819)
  ·
    refine ⟨7988598332252671778495729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5325732221501781185663819 7988598332252671778495729)
    ·
      refine ⟨5991448749189503833871797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7988598332252671778495729 5991448749189503833871797)
      ·
        refine ⟨561698320236515984425481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5991448749189503833871797 561698320236515984425481)
        ·
          refine ⟨421273740177386988319111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 561698320236515984425481 421273740177386988319111)
          ·
            refine ⟨631910610266080482478667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421273740177386988319111 631910610266080482478667)
            ·
              refine ⟨947865915399120723718001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 631910610266080482478667 947865915399120723718001)
              ·
                refine ⟨710899436549340542788501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 947865915399120723718001 710899436549340542788501)
                ·
                  refine ⟨33323411088250337943211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 710899436549340542788501 33323411088250337943211)
                  ·
                    rfl

theorem cell23_584074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 6].length) (baseStart_584074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584074 prefixEnd_584074 := by exact prefixLift 584074
  have htrace : WordTrace (prefixWord ++ tailWord_584074) baseStart_584074 baseEnd_584074 := by
    simpa [prefixWord, tailWord_584074, baseEnd_584074] using wordTrace_append hprefix tailTrace_584074
  have hstable : (prefixWord ++ tailWord_584074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584074).length < 2 ^ (prefixWord ++ tailWord_584074).sum := by decide
  have hdescent : baseEnd_584074 < baseStart_584074 := by decide
  rcases family_descends (prefixWord ++ tailWord_584074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584084 : List Nat := [2, 4, 2, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_584084 : Nat := 118140960795 + 584084 * 2 ^ 59
def prefixEnd_584084 : Nat := 4983230072969 + 3 ^ 40 * 584084 * 2
def baseEnd_584084 : Nat := 299915834600798002363853

theorem tailTrace_584084 : CollatzResearch.WordTrace tailWord_584084 prefixEnd_584084 299915834600798002363853 := by
  unfold tailWord_584084
  simp only [CollatzResearch.WordTrace]
  refine ⟨10651646807985448225259653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14202195743980597633679537 10651646807985448225259653)
  ·
    refine ⟨1997183776497271542236185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10651646807985448225259653 1997183776497271542236185)
    ·
      refine ⟨1497887832372953656677139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1997183776497271542236185 1497887832372953656677139)
      ·
        refine ⟨2246831748559430485015709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1497887832372953656677139 2246831748559430485015709)
        ·
          refine ⟨842561905709786431880891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2246831748559430485015709 842561905709786431880891)
          ·
            refine ⟨1263842858564679647821337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842561905709786431880891 1263842858564679647821337)
            ·
              refine ⟨947882143923509735866003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1263842858564679647821337 947882143923509735866003)
              ·
                refine ⟨1421823215885264603799005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 947882143923509735866003 1421823215885264603799005)
                ·
                  refine ⟨533183705956974226424627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1421823215885264603799005 533183705956974226424627)
                  ·
                    refine ⟨799775558935461339636941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 533183705956974226424627 799775558935461339636941)
                    ·
                      refine ⟨299915834600798002363853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 799775558935461339636941 299915834600798002363853)
                      ·
                        rfl

theorem cell23_584084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_584084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584084 prefixEnd_584084 := by exact prefixLift 584084
  have htrace : WordTrace (prefixWord ++ tailWord_584084) baseStart_584084 baseEnd_584084 := by
    simpa [prefixWord, tailWord_584084, baseEnd_584084] using wordTrace_append hprefix tailTrace_584084
  have hstable : (prefixWord ++ tailWord_584084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584084).length < 2 ^ (prefixWord ++ tailWord_584084).sum := by decide
  have hdescent : baseEnd_584084 < baseStart_584084 := by decide
  rcases family_descends (prefixWord ++ tailWord_584084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584100 : List Nat := [2, 3, 1, 2, 1, 1, 2, 5, 2, 4]
def baseStart_584100 : Nat := 118140960795 + 584100 * 2 ^ 59
def prefixEnd_584100 : Nat := 4983230072969 + 3 ^ 40 * 584100 * 2
def baseEnd_584100 : Nat := 99974683430423313254593

theorem tailTrace_584100 : CollatzResearch.WordTrace tailWord_584100 prefixEnd_584100 99974683430423313254593 := by
  unfold tailWord_584100
  simp only [CollatzResearch.WordTrace]
  refine ⟨10651938591956465591550877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14202584789275287455401169 10651938591956465591550877)
  ·
    refine ⟨3994476971983674596831579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10651938591956465591550877 3994476971983674596831579)
    ·
      refine ⟨5991715457975511895247369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3994476971983674596831579 5991715457975511895247369)
      ·
        refine ⟨4493786593481633921435527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5991715457975511895247369 4493786593481633921435527)
        ·
          refine ⟨6740679890222450882153291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4493786593481633921435527 6740679890222450882153291)
          ·
            refine ⟨10111019835333676323229937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6740679890222450882153291 10111019835333676323229937)
            ·
              refine ⟨7583264876500257242422453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10111019835333676323229937 7583264876500257242422453)
              ·
                refine ⟨710931082171899116477105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7583264876500257242422453 710931082171899116477105)
                ·
                  refine ⟨533198311628924337357829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 710931082171899116477105 533198311628924337357829)
                  ·
                    refine ⟨99974683430423313254593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 533198311628924337357829 99974683430423313254593)
                    ·
                      rfl

theorem cell23_584100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_584100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584100 prefixEnd_584100 := by exact prefixLift 584100
  have htrace : WordTrace (prefixWord ++ tailWord_584100) baseStart_584100 baseEnd_584100 := by
    simpa [prefixWord, tailWord_584100, baseEnd_584100] using wordTrace_append hprefix tailTrace_584100
  have hstable : (prefixWord ++ tailWord_584100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584100).length < 2 ^ (prefixWord ++ tailWord_584100).sum := by decide
  have hdescent : baseEnd_584100 < baseStart_584100 := by decide
  rcases family_descends (prefixWord ++ tailWord_584100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584113 : List Nat := [1, 2, 2, 4, 1, 3, 1, 9]
def baseStart_584113 : Nat := 118140960795 + 584113 * 2 ^ 59
def prefixEnd_584113 : Nat := 4983230072969 + 3 ^ 40 * 584113 * 2
def baseEnd_584113 : Nat := 11108545390362162551897

theorem tailTrace_584113 : CollatzResearch.WordTrace tailWord_584113 prefixEnd_584113 11108545390362162551897 := by
  unfold tailWord_584113
  simp only [CollatzResearch.WordTrace]
  refine ⟨21304351332865834403324993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14202900888577222935549995 21304351332865834403324993)
  ·
    refine ⟨15978263499649375802493745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21304351332865834403324993 15978263499649375802493745)
    ·
      refine ⟨11983697624737031851870309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15978263499649375802493745 11983697624737031851870309)
      ·
        refine ⟨2246943304638193472225683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11983697624737031851870309 2246943304638193472225683)
        ·
          refine ⟨3370414956957290208338525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2246943304638193472225683 3370414956957290208338525)
          ·
            refine ⟨1263905608858983828126947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3370414956957290208338525 1263905608858983828126947)
            ·
              refine ⟨1895858413288475742190421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1263905608858983828126947 1895858413288475742190421)
              ·
                refine ⟨11108545390362162551897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1895858413288475742190421 11108545390362162551897)
                ·
                  rfl

theorem cell23_584113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 9].length) (baseStart_584113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584113 prefixEnd_584113 := by exact prefixLift 584113
  have htrace : WordTrace (prefixWord ++ tailWord_584113) baseStart_584113 baseEnd_584113 := by
    simpa [prefixWord, tailWord_584113, baseEnd_584113] using wordTrace_append hprefix tailTrace_584113
  have hstable : (prefixWord ++ tailWord_584113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584113).length < 2 ^ (prefixWord ++ tailWord_584113).sum := by decide
  have hdescent : baseEnd_584113 < baseStart_584113 := by decide
  rcases family_descends (prefixWord ++ tailWord_584113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584150 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_584150 : Nat := 118140960795 + 584150 * 2 ^ 59
def prefixEnd_584150 : Nat := 4983230072969 + 3 ^ 40 * 584150 * 2
def baseEnd_584150 : Nat := 299949724323994744138549

theorem tailTrace_584150 : CollatzResearch.WordTrace tailWord_584150 prefixEnd_584150 299949724323994744138549 := by
  unfold tailWord_584150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1331606302108236857651369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14203800555821193148281269 1331606302108236857651369)
  ·
    refine ⟨998704726581177643238527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1331606302108236857651369 998704726581177643238527)
    ·
      refine ⟨1498057089871766464857791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 998704726581177643238527 1498057089871766464857791)
      ·
        refine ⟨2247085634807649697286687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1498057089871766464857791 2247085634807649697286687)
        ·
          refine ⟨3370628452211474545930031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2247085634807649697286687 3370628452211474545930031)
          ·
            refine ⟨5055942678317211818895047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3370628452211474545930031 5055942678317211818895047)
            ·
              refine ⟨7583914017475817728342571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5055942678317211818895047 7583914017475817728342571)
              ·
                refine ⟨11375871026213726592513857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7583914017475817728342571 11375871026213726592513857)
                ·
                  refine ⟨8531903269660294944385393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11375871026213726592513857 8531903269660294944385393)
                  ·
                    refine ⟨6398927452245221208289045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8531903269660294944385393 6398927452245221208289045)
                    ·
                      refine ⟨299949724323994744138549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6398927452245221208289045 299949724323994744138549)
                      ·
                        rfl

theorem cell23_584150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_584150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584150 prefixEnd_584150 := by exact prefixLift 584150
  have htrace : WordTrace (prefixWord ++ tailWord_584150) baseStart_584150 baseEnd_584150 := by
    simpa [prefixWord, tailWord_584150, baseEnd_584150] using wordTrace_append hprefix tailTrace_584150
  have hstable : (prefixWord ++ tailWord_584150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584150).length < 2 ^ (prefixWord ++ tailWord_584150).sum := by decide
  have hdescent : baseEnd_584150 < baseStart_584150 := by decide
  rcases family_descends (prefixWord ++ tailWord_584150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584167 : List Nat := [1, 1, 5, 2, 1, 1, 3, 1, 3, 3, 2]
def baseStart_584167 : Nat := 118140960795 + 584167 * 2 ^ 59
def prefixEnd_584167 : Nat := 4983230072969 + 3 ^ 40 * 584167 * 2
def baseEnd_584167 : Nat := 299958453495121177625971

theorem tailTrace_584167 : CollatzResearch.WordTrace tailWord_584167 prefixEnd_584167 299958453495121177625971 := by
  unfold tailWord_584167
  simp only [CollatzResearch.WordTrace]
  refine ⟨21306320874670201625790755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14204213916446801083860503 21306320874670201625790755)
  ·
    refine ⟨31959481312005302438686133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21306320874670201625790755 31959481312005302438686133)
    ·
      refine ⟨2996201373000497103626825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31959481312005302438686133 2996201373000497103626825)
      ·
        refine ⟨2247151029750372827720119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2996201373000497103626825 2247151029750372827720119)
        ·
          refine ⟨3370726544625559241580179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2247151029750372827720119 3370726544625559241580179)
          ·
            refine ⟨5056089816938338862370269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3370726544625559241580179 5056089816938338862370269)
            ·
              refine ⟨1896033681351877073388851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5056089816938338862370269 1896033681351877073388851)
              ·
                refine ⟨2844050522027815610083277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1896033681351877073388851 2844050522027815610083277)
                ·
                  refine ⟨1066518945760430853781229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2844050522027815610083277 1066518945760430853781229)
                  ·
                    refine ⟨399944604660161570167961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1066518945760430853781229 399944604660161570167961)
                    ·
                      refine ⟨299958453495121177625971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 399944604660161570167961 299958453495121177625971)
                      ·
                        rfl

theorem cell23_584167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_584167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584167 prefixEnd_584167 := by exact prefixLift 584167
  have htrace : WordTrace (prefixWord ++ tailWord_584167) baseStart_584167 baseEnd_584167 := by
    simpa [prefixWord, tailWord_584167, baseEnd_584167] using wordTrace_append hprefix tailTrace_584167
  have hstable : (prefixWord ++ tailWord_584167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584167).length < 2 ^ (prefixWord ++ tailWord_584167).sum := by decide
  have hdescent : baseEnd_584167 < baseStart_584167 := by decide
  rcases family_descends (prefixWord ++ tailWord_584167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584184 : List Nat := [2, 1, 2, 1, 1, 4, 5, 1, 1, 3, 2]
def baseStart_584184 : Nat := 118140960795 + 584184 * 2 ^ 59
def prefixEnd_584184 : Nat := 4983230072969 + 3 ^ 40 * 584184 * 2
def baseEnd_584184 : Nat := 299967182666247611113393

theorem tailTrace_584184 : CollatzResearch.WordTrace tailWord_584184 prefixEnd_584184 299967182666247611113393 := by
  unfold tailWord_584184
  simp only [CollatzResearch.WordTrace]
  refine ⟨10653470457804306764579803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14204627277072409019439737 10653470457804306764579803)
  ·
    refine ⟨15980205686706460146869705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10653470457804306764579803 15980205686706460146869705)
    ·
      refine ⟨11985154265029845110152279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15980205686706460146869705 11985154265029845110152279)
      ·
        refine ⟨17977731397544767665228419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11985154265029845110152279 17977731397544767665228419)
        ·
          refine ⟨26966597096317151497842629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17977731397544767665228419 26966597096317151497842629)
          ·
            refine ⟨5056236955559465905845493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26966597096317151497842629 5056236955559465905845493)
            ·
              refine ⟨474022214583699928673015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5056236955559465905845493 474022214583699928673015)
              ·
                refine ⟨711033321875549893009523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474022214583699928673015 711033321875549893009523)
                ·
                  refine ⟨1066549982813324839514285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 711033321875549893009523 1066549982813324839514285)
                  ·
                    refine ⟨399956243554996814817857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1066549982813324839514285 399956243554996814817857)
                    ·
                      refine ⟨299967182666247611113393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 399956243554996814817857 299967182666247611113393)
                      ·
                        rfl

theorem cell23_584184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 1, 3, 2].length) (baseStart_584184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584184 prefixEnd_584184 := by exact prefixLift 584184
  have htrace : WordTrace (prefixWord ++ tailWord_584184) baseStart_584184 baseEnd_584184 := by
    simpa [prefixWord, tailWord_584184, baseEnd_584184] using wordTrace_append hprefix tailTrace_584184
  have hstable : (prefixWord ++ tailWord_584184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584184).length < 2 ^ (prefixWord ++ tailWord_584184).sum := by decide
  have hdescent : baseEnd_584184 < baseStart_584184 := by decide
  rcases family_descends (prefixWord ++ tailWord_584184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584197 : List Nat := [1, 3, 1, 1, 2, 2, 2, 3, 4, 2, 2]
def baseStart_584197 : Nat := 118140960795 + 584197 * 2 ^ 59
def prefixEnd_584197 : Nat := 4983230072969 + 3 ^ 40 * 584197 * 2
def baseEnd_584197 : Nat := 299973857914756060250833

theorem tailTrace_584197 : CollatzResearch.WordTrace tailWord_584197 prefixEnd_584197 299973857914756060250833 := by
  unfold tailWord_584197
  simp only [CollatzResearch.WordTrace]
  refine ⟨21307415064561516749382845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14204943376374344499588563 21307415064561516749382845)
  ·
    refine ⟨7990280649210568781018567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21307415064561516749382845 7990280649210568781018567)
    ·
      refine ⟨11985420973815853171527851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7990280649210568781018567 11985420973815853171527851)
      ·
        refine ⟨17978131460723779757291777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11985420973815853171527851 17978131460723779757291777)
        ·
          refine ⟨13483598595542834817968833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17978131460723779757291777 13483598595542834817968833)
          ·
            refine ⟨10112698946657126113476625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13483598595542834817968833 10112698946657126113476625)
            ·
              refine ⟨7584524209992844585107469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10112698946657126113476625 7584524209992844585107469)
              ·
                refine ⟨2844196578747316719415301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7584524209992844585107469 2844196578747316719415301)
                ·
                  refine ⟨533286858515121884890369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2844196578747316719415301 533286858515121884890369)
                  ·
                    refine ⟨399965143886341413667777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 533286858515121884890369 399965143886341413667777)
                    ·
                      refine ⟨299973857914756060250833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 399965143886341413667777 299973857914756060250833)
                      ·
                        rfl

theorem cell23_584197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 2, 2].length) (baseStart_584197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584197 prefixEnd_584197 := by exact prefixLift 584197
  have htrace : WordTrace (prefixWord ++ tailWord_584197) baseStart_584197 baseEnd_584197 := by
    simpa [prefixWord, tailWord_584197, baseEnd_584197] using wordTrace_append hprefix tailTrace_584197
  have hstable : (prefixWord ++ tailWord_584197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584197).length < 2 ^ (prefixWord ++ tailWord_584197).sum := by decide
  have hdescent : baseEnd_584197 < baseStart_584197 := by decide
  rcases family_descends (prefixWord ++ tailWord_584197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584220 : List Nat := [2, 2, 3, 1, 2, 3, 1, 2, 7]
def baseStart_584220 : Nat := 118140960795 + 584220 * 2 ^ 59
def prefixEnd_584220 : Nat := 4983230072969 + 3 ^ 40 * 584220 * 2
def baseEnd_584220 : Nat := 33331740885534385584803

theorem tailTrace_584220 : CollatzResearch.WordTrace tailWord_584220 prefixEnd_584220 33331740885534385584803 := by
  unfold tailWord_584220
  simp only [CollatzResearch.WordTrace]
  refine ⟨10654126971739095838735057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14205502628985461118313409 10654126971739095838735057)
  ·
    refine ⟨7990595228804321879051293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10654126971739095838735057 7990595228804321879051293)
    ·
      refine ⟨2996473210801620704644235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7990595228804321879051293 2996473210801620704644235)
      ·
        refine ⟨4494709816202431056966353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2996473210801620704644235 4494709816202431056966353)
        ·
          refine ⟨3371032362151823292724765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4494709816202431056966353 3371032362151823292724765)
          ·
            refine ⟨1264137135806933734771787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3371032362151823292724765 1264137135806933734771787)
            ·
              refine ⟨1896205703710400602157681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1264137135806933734771787 1896205703710400602157681)
              ·
                refine ⟨1422154277782800451618261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1896205703710400602157681 1422154277782800451618261)
                ·
                  refine ⟨33331740885534385584803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1422154277782800451618261 33331740885534385584803)
                  ·
                    rfl

theorem cell23_584220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 7].length) (baseStart_584220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584220 prefixEnd_584220 := by exact prefixLift 584220
  have htrace : WordTrace (prefixWord ++ tailWord_584220) baseStart_584220 baseEnd_584220 := by
    simpa [prefixWord, tailWord_584220, baseEnd_584220] using wordTrace_append hprefix tailTrace_584220
  have hstable : (prefixWord ++ tailWord_584220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584220).length < 2 ^ (prefixWord ++ tailWord_584220).sum := by decide
  have hdescent : baseEnd_584220 < baseStart_584220 := by decide
  rcases family_descends (prefixWord ++ tailWord_584220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584254 : List Nat := [4, 2, 1, 4, 1, 1, 2, 1, 7]
def baseStart_584254 : Nat := 118140960795 + 584254 * 2 ^ 59
def prefixEnd_584254 : Nat := 4983230072969 + 3 ^ 40 * 584254 * 2
def baseEnd_584254 : Nat := 33333680701340259693119

theorem tailTrace_584254 : CollatzResearch.WordTrace tailWord_584254 prefixEnd_584254 33333680701340259693119 := by
  unfold tailWord_584254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2663686753169376935525977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14206329350236676989471877 2663686753169376935525977)
  ·
    refine ⟨1997765064877032701644483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2663686753169376935525977 1997765064877032701644483)
    ·
      refine ⟨2996647597315549052466725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1997765064877032701644483 2996647597315549052466725)
      ·
        refine ⟨561871424496665447337511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2996647597315549052466725 561871424496665447337511)
        ·
          refine ⟨842807136744998171006267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561871424496665447337511 842807136744998171006267)
          ·
            refine ⟨1264210705117497256509401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842807136744998171006267 1264210705117497256509401)
            ·
              refine ⟨948158028838122942382051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1264210705117497256509401 948158028838122942382051)
              ·
                refine ⟨1422237043257184413573077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 948158028838122942382051 1422237043257184413573077)
                ·
                  refine ⟨33333680701340259693119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1422237043257184413573077 33333680701340259693119)
                  ·
                    rfl

theorem cell23_584254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_584254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584254 prefixEnd_584254 := by exact prefixLift 584254
  have htrace : WordTrace (prefixWord ++ tailWord_584254) baseStart_584254 baseEnd_584254 := by
    simpa [prefixWord, tailWord_584254, baseEnd_584254] using wordTrace_append hprefix tailTrace_584254
  have hstable : (prefixWord ++ tailWord_584254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584254).length < 2 ^ (prefixWord ++ tailWord_584254).sum := by decide
  have hdescent : baseEnd_584254 < baseStart_584254 := by decide
  rcases family_descends (prefixWord ++ tailWord_584254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584270 : List Nat := [4, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4]
def baseStart_584270 : Nat := 118140960795 + 584270 * 2 ^ 59
def prefixEnd_584270 : Nat := 4983230072969 + 3 ^ 40 * 584270 * 2
def baseEnd_584270 : Nat := 300011342002534274637997

theorem tailTrace_584270 : CollatzResearch.WordTrace tailWord_584270 prefixEnd_584270 300011342002534274637997 := by
  unfold tailWord_584270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2663759699162131277098783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14206718395531366811193509 2663759699162131277098783)
  ·
    refine ⟨3995639548743196915648175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2663759699162131277098783 3995639548743196915648175)
    ·
      refine ⟨5993459323114795373472263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3995639548743196915648175 5993459323114795373472263)
      ·
        refine ⟨8990188984672193060208395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5993459323114795373472263 8990188984672193060208395)
        ·
          refine ⟨13485283477008289590312593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8990188984672193060208395 13485283477008289590312593)
          ·
            refine ⟨10113962607756217192734445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13485283477008289590312593 10113962607756217192734445)
            ·
              refine ⟨3792735977908581447275417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10113962607756217192734445 3792735977908581447275417)
              ·
                refine ⟨2844551983431436085456563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3792735977908581447275417 2844551983431436085456563)
                ·
                  refine ⟨4266827975147154128184845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2844551983431436085456563 4266827975147154128184845)
                  ·
                    refine ⟨1600060490680182798069317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4266827975147154128184845 1600060490680182798069317)
                    ·
                      refine ⟨300011342002534274637997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1600060490680182798069317 300011342002534274637997)
                      ·
                        rfl

theorem cell23_584270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_584270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584270 prefixEnd_584270 := by exact prefixLift 584270
  have htrace : WordTrace (prefixWord ++ tailWord_584270) baseStart_584270 baseEnd_584270 := by
    simpa [prefixWord, tailWord_584270, baseEnd_584270] using wordTrace_append hprefix tailTrace_584270
  have hstable : (prefixWord ++ tailWord_584270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584270).length < 2 ^ (prefixWord ++ tailWord_584270).sum := by decide
  have hdescent : baseEnd_584270 < baseStart_584270 := by decide
  rcases family_descends (prefixWord ++ tailWord_584270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584370 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 5, 6]
def baseStart_584370 : Nat := 118140960795 + 584370 * 2 ^ 59
def prefixEnd_584370 : Nat := 4983230072969 + 3 ^ 40 * 584370 * 2
def baseEnd_584370 : Nat := 100020896689327961129179

theorem tailTrace_584370 : CollatzResearch.WordTrace tailWord_584370 prefixEnd_584370 100020896689327961129179 := by
  unfold tailWord_584370
  simp only [CollatzResearch.WordTrace]
  refine ⟨5328431223233691823857641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14209149928623178196953709 5328431223233691823857641)
  ·
    refine ⟨3996323417425268867893231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5328431223233691823857641 3996323417425268867893231)
    ·
      refine ⟨5994485126137903301839847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3996323417425268867893231 5994485126137903301839847)
      ·
        refine ⟨8991727689206854952759771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5994485126137903301839847 8991727689206854952759771)
        ·
          refine ⟨13487591533810282429139657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8991727689206854952759771 13487591533810282429139657)
          ·
            refine ⟨10115693650357711821854743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13487591533810282429139657 10115693650357711821854743)
            ·
              refine ⟨15173540475536567732782115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10115693650357711821854743 15173540475536567732782115)
              ·
                refine ⟨22760310713304851599173173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15173540475536567732782115 22760310713304851599173173)
                ·
                  refine ⟨2133779129372329837422485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22760310713304851599173173 2133779129372329837422485)
                  ·
                    refine ⟨100020896689327961129179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2133779129372329837422485 100020896689327961129179)
                    ·
                      rfl

theorem cell23_584370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_584370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584370 prefixEnd_584370 := by exact prefixLift 584370
  have htrace : WordTrace (prefixWord ++ tailWord_584370) baseStart_584370 baseEnd_584370 := by
    simpa [prefixWord, tailWord_584370, baseEnd_584370] using wordTrace_append hprefix tailTrace_584370
  have hstable : (prefixWord ++ tailWord_584370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584370).length < 2 ^ (prefixWord ++ tailWord_584370).sum := by decide
  have hdescent : baseEnd_584370 < baseStart_584370 := by decide
  rcases family_descends (prefixWord ++ tailWord_584370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584371 : List Nat := [1, 1, 1, 2, 3, 5, 1, 4, 1, 1, 3]
def baseStart_584371 : Nat := 118140960795 + 584371 * 2 ^ 59
def prefixEnd_584371 : Nat := 4983230072969 + 3 ^ 40 * 584371 * 2
def baseEnd_584371 : Nat := 300063203548638379475033

theorem tailTrace_584371 : CollatzResearch.WordTrace tailWord_584371 prefixEnd_584371 300063203548638379475033 := by
  unfold tailWord_584371
  simp only [CollatzResearch.WordTrace]
  refine ⟨21313761365931144466216967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14209174243954096310811311 21313761365931144466216967)
  ·
    refine ⟨31970642048896716699325451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21313761365931144466216967 31970642048896716699325451)
    ·
      refine ⟨47955963073345075048988177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31970642048896716699325451 47955963073345075048988177)
      ·
        refine ⟨35966972305008806286741133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47955963073345075048988177 35966972305008806286741133)
        ·
          refine ⟨13487614614378302357527925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35966972305008806286741133 13487614614378302357527925)
          ·
            refine ⟨1264463870097965846018243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13487614614378302357527925 1264463870097965846018243)
            ·
              refine ⟨1896695805146948769027365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1264463870097965846018243 1896695805146948769027365)
              ·
                refine ⟨355630463465052894192631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1896695805146948769027365 355630463465052894192631)
                ·
                  refine ⟨533445695197579341288947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 355630463465052894192631 533445695197579341288947)
                  ·
                    refine ⟨800168542796369011933421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 533445695197579341288947 800168542796369011933421)
                    ·
                      refine ⟨300063203548638379475033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 800168542796369011933421 300063203548638379475033)
                      ·
                        rfl

theorem cell23_584371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 1, 1, 3].length) (baseStart_584371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584371 prefixEnd_584371 := by exact prefixLift 584371
  have htrace : WordTrace (prefixWord ++ tailWord_584371) baseStart_584371 baseEnd_584371 := by
    simpa [prefixWord, tailWord_584371, baseEnd_584371] using wordTrace_append hprefix tailTrace_584371
  have hstable : (prefixWord ++ tailWord_584371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584371).length < 2 ^ (prefixWord ++ tailWord_584371).sum := by decide
  have hdescent : baseEnd_584371 < baseStart_584371 := by decide
  rcases family_descends (prefixWord ++ tailWord_584371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584377 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 2, 6, 2]
def baseStart_584377 : Nat := 118140960795 + 584377 * 2 ^ 59
def prefixEnd_584377 : Nat := 4983230072969 + 3 ^ 40 * 584377 * 2
def baseEnd_584377 : Nat := 300066284432565356000005

theorem tailTrace_584377 : CollatzResearch.WordTrace tailWord_584377 prefixEnd_584377 300066284432565356000005 := by
  unfold tailWord_584377
  simp only [CollatzResearch.WordTrace]
  refine ⟨21313980203909407490935385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14209320135939604993956923 21313980203909407490935385)
  ·
    refine ⟨15985485152932055618201539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21313980203909407490935385 15985485152932055618201539)
    ·
      refine ⟨23978227729398083427302309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15985485152932055618201539 23978227729398083427302309)
      ·
        refine ⟨4495917699262140642619183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23978227729398083427302309 4495917699262140642619183)
        ·
          refine ⟨6743876548893210963928775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4495917699262140642619183 6743876548893210963928775)
          ·
            refine ⟨10115814823339816445893163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6743876548893210963928775 10115814823339816445893163)
            ·
              refine ⟨15173722235009724668839745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10115814823339816445893163 15173722235009724668839745)
              ·
                refine ⟨11380291676257293501629809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15173722235009724668839745 11380291676257293501629809)
                ·
                  refine ⟨8535218757192970126222357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11380291676257293501629809 8535218757192970126222357)
                  ·
                    refine ⟨400088379243420474666673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8535218757192970126222357 400088379243420474666673)
                    ·
                      refine ⟨300066284432565356000005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 400088379243420474666673 300066284432565356000005)
                      ·
                        rfl

theorem cell23_584377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_584377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584377 prefixEnd_584377 := by exact prefixLift 584377
  have htrace : WordTrace (prefixWord ++ tailWord_584377) baseStart_584377 baseEnd_584377 := by
    simpa [prefixWord, tailWord_584377, baseEnd_584377] using wordTrace_append hprefix tailTrace_584377
  have hstable : (prefixWord ++ tailWord_584377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584377).length < 2 ^ (prefixWord ++ tailWord_584377).sum := by decide
  have hdescent : baseEnd_584377 < baseStart_584377 := by decide
  rcases family_descends (prefixWord ++ tailWord_584377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584405 : List Nat := [1, 3, 2, 5, 1, 1, 2, 3, 1, 1, 3]
def baseStart_584405 : Nat := 118140960795 + 584405 * 2 ^ 59
def prefixEnd_584405 : Nat := 4983230072969 + 3 ^ 40 * 584405 * 2
def baseEnd_584405 : Nat := 300080661890891246449877

theorem tailTrace_584405 : CollatzResearch.WordTrace tailWord_584405 prefixEnd_584405 300080661890891246449877 := by
  unfold tailWord_584405
  simp only [CollatzResearch.WordTrace]
  refine ⟨21315001447807968272954669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14210000965205312181969779 21315001447807968272954669)
  ·
    refine ⟨7993125542927988102358001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21315001447807968272954669 7993125542927988102358001)
    ·
      refine ⟨5994844157195991076768501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7993125542927988102358001 5994844157195991076768501)
      ·
        refine ⟨562016639737124163447047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5994844157195991076768501 562016639737124163447047)
        ·
          refine ⟨843024959605686245170571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 562016639737124163447047 843024959605686245170571)
          ·
            refine ⟨1264537439408529367755857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 843024959605686245170571 1264537439408529367755857)
            ·
              refine ⟨948403079556397025816893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1264537439408529367755857 948403079556397025816893)
              ·
                refine ⟨355651154833648884681335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 948403079556397025816893 355651154833648884681335)
                ·
                  refine ⟨533476732250473327022003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 355651154833648884681335 533476732250473327022003)
                  ·
                    refine ⟨800215098375709990533005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 533476732250473327022003 800215098375709990533005)
                    ·
                      refine ⟨300080661890891246449877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 800215098375709990533005 300080661890891246449877)
                      ·
                        rfl

theorem cell23_584405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_584405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584405 prefixEnd_584405 := by exact prefixLift 584405
  have htrace : WordTrace (prefixWord ++ tailWord_584405) baseStart_584405 baseEnd_584405 := by
    simpa [prefixWord, tailWord_584405, baseEnd_584405] using wordTrace_append hprefix tailTrace_584405
  have hstable : (prefixWord ++ tailWord_584405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584405).length < 2 ^ (prefixWord ++ tailWord_584405).sum := by decide
  have hdescent : baseEnd_584405 < baseStart_584405 := by decide
  rcases family_descends (prefixWord ++ tailWord_584405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584407 : List Nat := [1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 4]
def baseStart_584407 : Nat := 118140960795 + 584407 * 2 ^ 59
def prefixEnd_584407 : Nat := 4983230072969 + 3 ^ 40 * 584407 * 2
def baseEnd_584407 : Nat := 300081688852200238624867

theorem tailTrace_584407 : CollatzResearch.WordTrace tailWord_584407 prefixEnd_584407 300081688852200238624867 := by
  unfold tailWord_584407
  simp only [CollatzResearch.WordTrace]
  refine ⟨21315074393800722614527475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14210049595867148409684983 21315074393800722614527475)
  ·
    refine ⟨31972611590701083921791213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21315074393800722614527475 31972611590701083921791213)
    ·
      refine ⟨11989729346512906470671705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31972611590701083921791213 11989729346512906470671705)
      ·
        refine ⟨8992297009884679853003779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11989729346512906470671705 8992297009884679853003779)
        ·
          refine ⟨13488445514827019779505669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8992297009884679853003779 13488445514827019779505669)
          ·
            refine ⟨2529083534030066208657313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13488445514827019779505669 2529083534030066208657313)
            ·
              refine ⟨1896812650522549656492985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2529083534030066208657313 1896812650522549656492985)
              ·
                refine ⟨1422609487891912242369739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1896812650522549656492985 1422609487891912242369739)
                ·
                  refine ⟨2133914231837868363554609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1422609487891912242369739 2133914231837868363554609)
                  ·
                    refine ⟨1600435673878401272665957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2133914231837868363554609 1600435673878401272665957)
                    ·
                      refine ⟨300081688852200238624867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1600435673878401272665957 300081688852200238624867)
                      ·
                        rfl

theorem cell23_584407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_584407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584407 prefixEnd_584407 := by exact prefixLift 584407
  have htrace : WordTrace (prefixWord ++ tailWord_584407) baseStart_584407 baseEnd_584407 := by
    simpa [prefixWord, tailWord_584407, baseEnd_584407] using wordTrace_append hprefix tailTrace_584407
  have hstable : (prefixWord ++ tailWord_584407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584407).length < 2 ^ (prefixWord ++ tailWord_584407).sum := by decide
  have hdescent : baseEnd_584407 < baseStart_584407 := by decide
  rcases family_descends (prefixWord ++ tailWord_584407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584421 : List Nat := [1, 3, 1, 4, 1, 4, 1, 2, 2, 4]
def baseStart_584421 : Nat := 118140960795 + 584421 * 2 ^ 59
def prefixEnd_584421 : Nat := 4983230072969 + 3 ^ 40 * 584421 * 2
def baseEnd_584421 : Nat := 100029625860454394616601

theorem tailTrace_584421 : CollatzResearch.WordTrace tailWord_584421 prefixEnd_584421 100029625860454394616601 := by
  unfold tailWord_584421
  simp only [CollatzResearch.WordTrace]
  refine ⟨21315585015750003005537117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14210390010500002003691411 21315585015750003005537117)
  ·
    refine ⟨7993344380906251127076419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21315585015750003005537117 7993344380906251127076419)
    ·
      refine ⟨11990016571359376690614629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7993344380906251127076419 11990016571359376690614629)
      ·
        refine ⟨2248128107129883129490243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11990016571359376690614629 2248128107129883129490243)
        ·
          refine ⟨3372192160694824694235365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2248128107129883129490243 3372192160694824694235365)
          ·
            refine ⟨632286030130279630169131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3372192160694824694235365 632286030130279630169131)
            ·
              refine ⟨948429045195419445253697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 632286030130279630169131 948429045195419445253697)
              ·
                refine ⟨711321783896564583940273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 948429045195419445253697 711321783896564583940273)
                ·
                  refine ⟨533491337922423437955205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 711321783896564583940273 533491337922423437955205)
                  ·
                    refine ⟨100029625860454394616601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 533491337922423437955205 100029625860454394616601)
                    ·
                      rfl

theorem cell23_584421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 2, 4].length) (baseStart_584421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584421 prefixEnd_584421 := by exact prefixLift 584421
  have htrace : WordTrace (prefixWord ++ tailWord_584421) baseStart_584421 baseEnd_584421 := by
    simpa [prefixWord, tailWord_584421, baseEnd_584421] using wordTrace_append hprefix tailTrace_584421
  have hstable : (prefixWord ++ tailWord_584421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584421).length < 2 ^ (prefixWord ++ tailWord_584421).sum := by decide
  have hdescent : baseEnd_584421 < baseStart_584421 := by decide
  rcases family_descends (prefixWord ++ tailWord_584421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584444 : List Nat := [2, 2, 2, 1, 3, 2, 3, 1, 1, 3, 3]
def baseStart_584444 : Nat := 118140960795 + 584444 * 2 ^ 59
def prefixEnd_584444 : Nat := 4983230072969 + 3 ^ 40 * 584444 * 2
def baseEnd_584444 : Nat := 300100687636416593862197

theorem tailTrace_584444 : CollatzResearch.WordTrace tailWord_584444 prefixEnd_584444 300100687636416593862197 := by
  unfold tailWord_584444
  simp only [CollatzResearch.WordTrace]
  refine ⟨10658211947333338966812193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14210949263111118622416257 10658211947333338966812193)
  ·
    refine ⟨7993658960500004225109145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10658211947333338966812193 7993658960500004225109145)
    ·
      refine ⟨5995244220375003168831859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7993658960500004225109145 5995244220375003168831859)
      ·
        refine ⟨8992866330562504753247789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5995244220375003168831859 8992866330562504753247789)
        ·
          refine ⟨3372324873960939282467921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8992866330562504753247789 3372324873960939282467921)
          ·
            refine ⟨2529243655470704461850941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3372324873960939282467921 2529243655470704461850941)
            ·
              refine ⟨948466370801514173194103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2529243655470704461850941 948466370801514173194103)
              ·
                refine ⟨1422699556202271259791155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 948466370801514173194103 1422699556202271259791155)
                ·
                  refine ⟨2134049334303406889686733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1422699556202271259791155 2134049334303406889686733)
                  ·
                    refine ⟨800268500363777583632525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2134049334303406889686733 800268500363777583632525)
                    ·
                      refine ⟨300100687636416593862197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 800268500363777583632525 300100687636416593862197)
                      ·
                        rfl

theorem cell23_584444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_584444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584444 prefixEnd_584444 := by exact prefixLift 584444
  have htrace : WordTrace (prefixWord ++ tailWord_584444) baseStart_584444 baseEnd_584444 := by
    simpa [prefixWord, tailWord_584444, baseEnd_584444] using wordTrace_append hprefix tailTrace_584444
  have hstable : (prefixWord ++ tailWord_584444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584444).length < 2 ^ (prefixWord ++ tailWord_584444).sum := by decide
  have hdescent : baseEnd_584444 < baseStart_584444 := by decide
  rcases family_descends (prefixWord ++ tailWord_584444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584497 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 1, 4, 4]
def baseStart_584497 : Nat := 118140960795 + 584497 * 2 ^ 59
def prefixEnd_584497 : Nat := 4983230072969 + 3 ^ 40 * 584497 * 2
def baseEnd_584497 : Nat := 300127902111104886499453

theorem tailTrace_584497 : CollatzResearch.WordTrace tailWord_584497 prefixEnd_584497 300127902111104886499453 := by
  unfold tailWord_584497
  simp only [CollatzResearch.WordTrace]
  refine ⟨21318356963474667985303745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14212237975649778656869163 21318356963474667985303745)
  ·
    refine ⟨15988767722606000988977809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21318356963474667985303745 15988767722606000988977809)
    ·
      refine ⟨11991575791954500741733357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15988767722606000988977809 11991575791954500741733357)
      ·
        refine ⟨4496840921982937778150009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11991575791954500741733357 4496840921982937778150009)
        ·
          refine ⟨3372630691487203333612507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4496840921982937778150009 3372630691487203333612507)
          ·
            refine ⟨5058946037230805000418761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3372630691487203333612507 5058946037230805000418761)
            ·
              refine ⟨3794209527923103750314071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5058946037230805000418761 3794209527923103750314071)
              ·
                refine ⟨5691314291884655625471107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3794209527923103750314071 5691314291884655625471107)
                ·
                  refine ⟨8536971437826983438206661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5691314291884655625471107 8536971437826983438206661)
                  ·
                    refine ⟨1600682144592559394663749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8536971437826983438206661 1600682144592559394663749)
                    ·
                      refine ⟨300127902111104886499453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1600682144592559394663749 300127902111104886499453)
                      ·
                        rfl

theorem cell23_584497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_584497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584497 prefixEnd_584497 := by exact prefixLift 584497
  have htrace : WordTrace (prefixWord ++ tailWord_584497) baseStart_584497 baseEnd_584497 := by
    simpa [prefixWord, tailWord_584497, baseEnd_584497] using wordTrace_append hprefix tailTrace_584497
  have hstable : (prefixWord ++ tailWord_584497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584497).length < 2 ^ (prefixWord ++ tailWord_584497).sum := by decide
  have hdescent : baseEnd_584497 < baseStart_584497 := by decide
  rcases family_descends (prefixWord ++ tailWord_584497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584517 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 3, 5, 3]
def baseStart_584517 : Nat := 118140960795 + 584517 * 2 ^ 59
def prefixEnd_584517 : Nat := 4983230072969 + 3 ^ 40 * 584517 * 2
def baseEnd_584517 : Nat := 300138171724194808249361

theorem tailTrace_584517 : CollatzResearch.WordTrace tailWord_584517 prefixEnd_584517 300138171724194808249361 := by
  unfold tailWord_584517
  simp only [CollatzResearch.WordTrace]
  refine ⟨21319086423402211401031805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14212724282268140934021203 21319086423402211401031805)
  ·
    refine ⟨7994657408775829275386927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21319086423402211401031805 7994657408775829275386927)
    ·
      refine ⟨11991986113163743913080391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7994657408775829275386927 11991986113163743913080391)
      ·
        refine ⟨17987979169745615869620587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11991986113163743913080391 17987979169745615869620587)
        ·
          refine ⟨26981968754618423804430881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17987979169745615869620587 26981968754618423804430881)
          ·
            refine ⟨20236476565963817853323161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26981968754618423804430881 20236476565963817853323161)
            ·
              refine ⟨15177357424472863389992371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20236476565963817853323161 15177357424472863389992371)
              ·
                refine ⟨22766036136709295084988557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15177357424472863389992371 22766036136709295084988557)
                ·
                  refine ⟨8537263551265985656870709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22766036136709295084988557 8537263551265985656870709)
                  ·
                    refine ⟨800368457931186155331629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8537263551265985656870709 800368457931186155331629)
                    ·
                      refine ⟨300138171724194808249361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 800368457931186155331629 300138171724194808249361)
                      ·
                        rfl

theorem cell23_584517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 5, 3].length) (baseStart_584517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584517 prefixEnd_584517 := by exact prefixLift 584517
  have htrace : WordTrace (prefixWord ++ tailWord_584517) baseStart_584517 baseEnd_584517 := by
    simpa [prefixWord, tailWord_584517, baseEnd_584517] using wordTrace_append hprefix tailTrace_584517
  have hstable : (prefixWord ++ tailWord_584517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584517).length < 2 ^ (prefixWord ++ tailWord_584517).sum := by decide
  have hdescent : baseEnd_584517 < baseStart_584517 := by decide
  rcases family_descends (prefixWord ++ tailWord_584517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584544 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 1, 7, 2]
def baseStart_584544 : Nat := 118140960795 + 584544 * 2 ^ 59
def prefixEnd_584544 : Nat := 4983230072969 + 3 ^ 40 * 584544 * 2
def baseEnd_584544 : Nat := 300152035701866202611737

theorem tailTrace_584544 : CollatzResearch.WordTrace tailWord_584544 prefixEnd_584544 300152035701866202611737 := by
  unfold tailWord_584544
  simp only [CollatzResearch.WordTrace]
  refine ⟨10660035597152197506132343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14213380796202930008176457 10660035597152197506132343)
  ·
    refine ⟨15990053395728296259198515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10660035597152197506132343 15990053395728296259198515)
    ·
      refine ⟨23985080093592444388797773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15990053395728296259198515 23985080093592444388797773)
      ·
        refine ⟨8994405035097166645799165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23985080093592444388797773 8994405035097166645799165)
        ·
          refine ⟨3372901888161437492174687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8994405035097166645799165 3372901888161437492174687)
          ·
            refine ⟨5059352832242156238262031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3372901888161437492174687 5059352832242156238262031)
            ·
              refine ⟨7589029248363234357393047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5059352832242156238262031 7589029248363234357393047)
              ·
                refine ⟨11383543872544851536089571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7589029248363234357393047 11383543872544851536089571)
                ·
                  refine ⟨17075315808817277304134357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11383543872544851536089571 17075315808817277304134357)
                  ·
                    refine ⟨400202714269154936815649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17075315808817277304134357 400202714269154936815649)
                    ·
                      refine ⟨300152035701866202611737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 400202714269154936815649 300152035701866202611737)
                      ·
                        rfl

theorem cell23_584544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 1, 7, 2].length) (baseStart_584544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584544 prefixEnd_584544 := by exact prefixLift 584544
  have htrace : WordTrace (prefixWord ++ tailWord_584544) baseStart_584544 baseEnd_584544 := by
    simpa [prefixWord, tailWord_584544, baseEnd_584544] using wordTrace_append hprefix tailTrace_584544
  have hstable : (prefixWord ++ tailWord_584544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584544).length < 2 ^ (prefixWord ++ tailWord_584544).sum := by decide
  have hdescent : baseEnd_584544 < baseStart_584544 := by decide
  rcases family_descends (prefixWord ++ tailWord_584544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584587 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 6]
def baseStart_584587 : Nat := 118140960795 + 584587 * 2 ^ 59
def prefixEnd_584587 : Nat := 4983230072969 + 3 ^ 40 * 584587 * 2
def baseEnd_584587 : Nat := 300174115370009534374039

theorem tailTrace_584587 : CollatzResearch.WordTrace tailWord_584587 prefixEnd_584587 300174115370009534374039 := by
  unfold tailWord_584587
  simp only [CollatzResearch.WordTrace]
  refine ⟨21321639533148613356080015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14214426355432408904053343 21321639533148613356080015)
  ·
    refine ⟨31982459299722920034120023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21321639533148613356080015 31982459299722920034120023)
    ·
      refine ⟨47973688949584380051180035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31982459299722920034120023 47973688949584380051180035)
      ·
        refine ⟨71960533424376570076770053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47973688949584380051180035 71960533424376570076770053)
        ·
          refine ⟨13492600017070606889394385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71960533424376570076770053 13492600017070606889394385)
          ·
            refine ⟨10119450012802955167045789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13492600017070606889394385 10119450012802955167045789)
            ·
              refine ⟨3794793754801108187642171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10119450012802955167045789 3794793754801108187642171)
              ·
                refine ⟨5692190632201662281463257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3794793754801108187642171 5692190632201662281463257)
                ·
                  refine ⟨4269142974151246711097443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5692190632201662281463257 4269142974151246711097443)
                  ·
                    refine ⟨6403714461226870066646165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4269142974151246711097443 6403714461226870066646165)
                    ·
                      refine ⟨300174115370009534374039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6403714461226870066646165 300174115370009534374039)
                      ·
                        rfl

theorem cell23_584587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 6].length) (baseStart_584587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584587 prefixEnd_584587 := by exact prefixLift 584587
  have htrace : WordTrace (prefixWord ++ tailWord_584587) baseStart_584587 baseEnd_584587 := by
    simpa [prefixWord, tailWord_584587, baseEnd_584587] using wordTrace_append hprefix tailTrace_584587
  have hstable : (prefixWord ++ tailWord_584587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584587).length < 2 ^ (prefixWord ++ tailWord_584587).sum := by decide
  have hdescent : baseEnd_584587 < baseStart_584587 := by decide
  rcases family_descends (prefixWord ++ tailWord_584587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584617 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 1, 2, 6]
def baseStart_584617 : Nat := 118140960795 + 584617 * 2 ^ 59
def prefixEnd_584617 : Nat := 4983230072969 + 3 ^ 40 * 584617 * 2
def baseEnd_584617 : Nat := 300189519789644416998901

theorem tailTrace_584617 : CollatzResearch.WordTrace tailWord_584617 prefixEnd_584617 300189519789644416998901 := by
  unfold tailWord_584617
  simp only [CollatzResearch.WordTrace]
  refine ⟨21322733723039928479672105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14215155815359952319781403 21322733723039928479672105)
  ·
    refine ⟨15992050292279946359754079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21322733723039928479672105 15992050292279946359754079)
    ·
      refine ⟨23988075438419919539631119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15992050292279946359754079 23988075438419919539631119)
      ·
        refine ⟨35982113157629879309446679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23988075438419919539631119 35982113157629879309446679)
        ·
          refine ⟨53973169736444818964170019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35982113157629879309446679 53973169736444818964170019)
          ·
            refine ⟨80959754604667228446255029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53973169736444818964170019 80959754604667228446255029)
            ·
              refine ⟨7589976994187552666836409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80959754604667228446255029 7589976994187552666836409)
              ·
                refine ⟨5692482745640664500127307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7589976994187552666836409 5692482745640664500127307)
                ·
                  refine ⟨8538724118460996750190961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5692482745640664500127307 8538724118460996750190961)
                  ·
                    refine ⟨6404043088845747562643221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8538724118460996750190961 6404043088845747562643221)
                    ·
                      refine ⟨300189519789644416998901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6404043088845747562643221 300189519789644416998901)
                      ·
                        rfl

theorem cell23_584617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_584617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584617 prefixEnd_584617 := by exact prefixLift 584617
  have htrace : WordTrace (prefixWord ++ tailWord_584617) baseStart_584617 baseEnd_584617 := by
    simpa [prefixWord, tailWord_584617, baseEnd_584617] using wordTrace_append hprefix tailTrace_584617
  have hstable : (prefixWord ++ tailWord_584617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584617).length < 2 ^ (prefixWord ++ tailWord_584617).sum := by decide
  have hdescent : baseEnd_584617 < baseStart_584617 := by decide
  rcases family_descends (prefixWord ++ tailWord_584617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584628 : List Nat := [2, 5, 2, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_584628 : Nat := 118140960795 + 584628 * 2 ^ 59
def prefixEnd_584628 : Nat := 4983230072969 + 3 ^ 40 * 584628 * 2
def baseEnd_584628 : Nat := 300195168076843873961351

theorem tailTrace_584628 : CollatzResearch.WordTrace tailWord_584628 prefixEnd_584628 300195168076843873961351 := by
  unfold tailWord_584628
  simp only [CollatzResearch.WordTrace]
  refine ⟨10661567463000038679161269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14215423284000051572215025 10661567463000038679161269)
  ·
    refine ⟨999521949656253626171369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10661567463000038679161269 999521949656253626171369)
    ·
      refine ⟨749641462242190219628527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 999521949656253626171369 749641462242190219628527)
      ·
        refine ⟨1124462193363285329442791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 749641462242190219628527 1124462193363285329442791)
        ·
          refine ⟨1686693290044927994164187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124462193363285329442791 1686693290044927994164187)
          ·
            refine ⟨2530039935067391991246281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1686693290044927994164187 2530039935067391991246281)
            ·
              refine ⟨1897529951300543993434711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2530039935067391991246281 1897529951300543993434711)
              ·
                refine ⟨2846294926950815990152067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1897529951300543993434711 2846294926950815990152067)
                ·
                  refine ⟨4269442390426223985228101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2846294926950815990152067 4269442390426223985228101)
                  ·
                    refine ⟨800520448204916997230269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4269442390426223985228101 800520448204916997230269)
                    ·
                      refine ⟨300195168076843873961351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 800520448204916997230269 300195168076843873961351)
                      ·
                        rfl

theorem cell23_584628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_584628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584628 prefixEnd_584628 := by exact prefixLift 584628
  have htrace : WordTrace (prefixWord ++ tailWord_584628) baseStart_584628 baseEnd_584628 := by
    simpa [prefixWord, tailWord_584628, baseEnd_584628] using wordTrace_append hprefix tailTrace_584628
  have hstable : (prefixWord ++ tailWord_584628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584628).length < 2 ^ (prefixWord ++ tailWord_584628).sum := by decide
  have hdescent : baseEnd_584628 < baseStart_584628 := by decide
  rcases family_descends (prefixWord ++ tailWord_584628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584651 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 4, 3, 2]
def baseStart_584651 : Nat := 118140960795 + 584651 * 2 ^ 59
def prefixEnd_584651 : Nat := 4983230072969 + 3 ^ 40 * 584651 * 2
def baseEnd_584651 : Nat := 300206978131897283973745

theorem tailTrace_584651 : CollatzResearch.WordTrace tailWord_584651 prefixEnd_584651 300206978131897283973745 := by
  unfold tailWord_584651
  simp only [CollatzResearch.WordTrace]
  refine ⟨21323973804916752286409807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14215982536611168190939871 21323973804916752286409807)
  ·
    refine ⟨31985960707375128429614711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21323973804916752286409807 31985960707375128429614711)
    ·
      refine ⟨47978941061062692644422067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31985960707375128429614711 47978941061062692644422067)
      ·
        refine ⟨71968411591594038966633101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47978941061062692644422067 71968411591594038966633101)
        ·
          refine ⟨26988154346847764612487413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71968411591594038966633101 26988154346847764612487413)
          ·
            refine ⟨2530139470016977932420695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26988154346847764612487413 2530139470016977932420695)
            ·
              refine ⟨3795209205025466898631043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2530139470016977932420695 3795209205025466898631043)
              ·
                refine ⟨5692813807538200347946565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3795209205025466898631043 5692813807538200347946565)
                ·
                  refine ⟨1067402588913412565239981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5692813807538200347946565 1067402588913412565239981)
                  ·
                    refine ⟨400275970842529711964993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1067402588913412565239981 400275970842529711964993)
                    ·
                      refine ⟨300206978131897283973745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 400275970842529711964993 300206978131897283973745)
                      ·
                        rfl

theorem cell23_584651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 3, 2].length) (baseStart_584651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584651 prefixEnd_584651 := by exact prefixLift 584651
  have htrace : WordTrace (prefixWord ++ tailWord_584651) baseStart_584651 baseEnd_584651 := by
    simpa [prefixWord, tailWord_584651, baseEnd_584651] using wordTrace_append hprefix tailTrace_584651
  have hstable : (prefixWord ++ tailWord_584651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584651).length < 2 ^ (prefixWord ++ tailWord_584651).sum := by decide
  have hdescent : baseEnd_584651 < baseStart_584651 := by decide
  rcases family_descends (prefixWord ++ tailWord_584651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584765 : List Nat := [1, 4, 1, 3, 1, 2, 3, 2, 2, 1, 3]
def baseStart_584765 : Nat := 118140960795 + 584765 * 2 ^ 59
def prefixEnd_584765 : Nat := 4983230072969 + 3 ^ 40 * 584765 * 2
def baseEnd_584765 : Nat := 300265514926509837948221

theorem tailTrace_584765 : CollatzResearch.WordTrace tailWord_584765 prefixEnd_584765 300265514926509837948221 := by
  unfold tailWord_584765
  simp only [CollatzResearch.WordTrace]
  refine ⟨21328131726503749756059749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14218754484335833170706499 21328131726503749756059749)
  ·
    refine ⟨3999024698719453079261203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21328131726503749756059749 3999024698719453079261203)
    ·
      refine ⟨5998537048079179618891805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3999024698719453079261203 5998537048079179618891805)
      ·
        refine ⟨2249451393029692357084427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5998537048079179618891805 2249451393029692357084427)
        ·
          refine ⟨3374177089544538535626641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2249451393029692357084427 3374177089544538535626641)
          ·
            refine ⟨2530632817158403901719981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3374177089544538535626641 2530632817158403901719981)
            ·
              refine ⟨948987306434401463144993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2530632817158403901719981 948987306434401463144993)
              ·
                refine ⟨711740479825801097358745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 948987306434401463144993 711740479825801097358745)
                ·
                  refine ⟨533805359869350823019059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 711740479825801097358745 533805359869350823019059)
                  ·
                    refine ⟨800708039804026234528589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 533805359869350823019059 800708039804026234528589)
                    ·
                      refine ⟨300265514926509837948221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 800708039804026234528589 300265514926509837948221)
                      ·
                        rfl

theorem cell23_584765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_584765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584765 prefixEnd_584765 := by exact prefixLift 584765
  have htrace : WordTrace (prefixWord ++ tailWord_584765) baseStart_584765 baseEnd_584765 := by
    simpa [prefixWord, tailWord_584765, baseEnd_584765] using wordTrace_append hprefix tailTrace_584765
  have hstable : (prefixWord ++ tailWord_584765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584765).length < 2 ^ (prefixWord ++ tailWord_584765).sum := by decide
  have hdescent : baseEnd_584765 < baseStart_584765 := by decide
  rcases family_descends (prefixWord ++ tailWord_584765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584794 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 9]
def baseStart_584794 : Nat := 118140960795 + 584794 * 2 ^ 59
def prefixEnd_584794 : Nat := 4983230072969 + 3 ^ 40 * 584794 * 2
def baseEnd_584794 : Nat := 33364489540610024942843

theorem tailTrace_584794 : CollatzResearch.WordTrace tailWord_584794 prefixEnd_584794 33364489540610024942843 := by
  unfold tailWord_584794
  simp only [CollatzResearch.WordTrace]
  refine ⟨5332297360849671927216359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14219459628932458472576957 5332297360849671927216359)
  ·
    refine ⟨7998446041274507890824539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5332297360849671927216359 7998446041274507890824539)
    ·
      refine ⟨11997669061911761836236809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7998446041274507890824539 11997669061911761836236809)
      ·
        refine ⟨8998251796433821377177607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11997669061911761836236809 8998251796433821377177607)
        ·
          refine ⟨13497377694650732065766411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8998251796433821377177607 13497377694650732065766411)
          ·
            refine ⟨20246066541976098098649617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13497377694650732065766411 20246066541976098098649617)
            ·
              refine ⟨15184549906482073573987213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20246066541976098098649617 15184549906482073573987213)
              ·
                refine ⟨5694206214930777590245205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15184549906482073573987213 5694206214930777590245205)
                ·
                  refine ⟨33364489540610024942843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5694206214930777590245205 33364489540610024942843)
                  ·
                    rfl

theorem cell23_584794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 9].length) (baseStart_584794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584794 prefixEnd_584794 := by exact prefixLift 584794
  have htrace : WordTrace (prefixWord ++ tailWord_584794) baseStart_584794 baseEnd_584794 := by
    simpa [prefixWord, tailWord_584794, baseEnd_584794] using wordTrace_append hprefix tailTrace_584794
  have hstable : (prefixWord ++ tailWord_584794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584794).length < 2 ^ (prefixWord ++ tailWord_584794).sum := by decide
  have hdescent : baseEnd_584794 < baseStart_584794 := by decide
  rcases family_descends (prefixWord ++ tailWord_584794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584822 : List Nat := [5, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2]
def baseStart_584822 : Nat := 118140960795 + 584822 * 2 ^ 59
def prefixEnd_584822 : Nat := 4983230072969 + 3 ^ 40 * 584822 * 2
def baseEnd_584822 : Nat := 300294783323816114935459

theorem tailTrace_584822 : CollatzResearch.WordTrace tailWord_584822 prefixEnd_584822 300294783323816114935459 := by
  unfold tailWord_584822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1333138167956078030680295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14220140458198165660589813 1333138167956078030680295)
  ·
    refine ⟨1999707251934117046020443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1333138167956078030680295 1999707251934117046020443)
    ·
      refine ⟨2999560877901175569030665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1999707251934117046020443 2999560877901175569030665)
      ·
        refine ⟨2249670658425881676772999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2999560877901175569030665 2249670658425881676772999)
        ·
          refine ⟨3374505987638822515159499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2249670658425881676772999 3374505987638822515159499)
          ·
            refine ⟨5061758981458233772739249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3374505987638822515159499 5061758981458233772739249)
            ·
              refine ⟨3796319236093675329554437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5061758981458233772739249 3796319236093675329554437)
              ·
                refine ⟨711809856767564124291457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3796319236093675329554437 711809856767564124291457)
                ·
                  refine ⟨533857392575673093218593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 711809856767564124291457 533857392575673093218593)
                  ·
                    refine ⟨400393044431754819913945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 533857392575673093218593 400393044431754819913945)
                    ·
                      refine ⟨300294783323816114935459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 400393044431754819913945 300294783323816114935459)
                      ·
                        rfl

theorem cell23_584822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_584822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584822 prefixEnd_584822 := by exact prefixLift 584822
  have htrace : WordTrace (prefixWord ++ tailWord_584822) baseStart_584822 baseEnd_584822 := by
    simpa [prefixWord, tailWord_584822, baseEnd_584822] using wordTrace_append hprefix tailTrace_584822
  have hstable : (prefixWord ++ tailWord_584822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584822).length < 2 ^ (prefixWord ++ tailWord_584822).sum := by decide
  have hdescent : baseEnd_584822 < baseStart_584822 := by decide
  rcases family_descends (prefixWord ++ tailWord_584822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584858 : List Nat := [3, 1, 1, 5, 1, 1, 1, 3, 2, 5]
def baseStart_584858 : Nat := 118140960795 + 584858 * 2 ^ 59
def prefixEnd_584858 : Nat := 4983230072969 + 3 ^ 40 * 584858 * 2
def baseEnd_584858 : Nat := 100104422875792658028431

theorem tailTrace_584858 : CollatzResearch.WordTrace tailWord_584858 prefixEnd_584858 100104422875792658028431 := by
  unfold tailWord_584858
  simp only [CollatzResearch.WordTrace]
  refine ⟨5332880928791706659798807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14221015810111217759463485 5332880928791706659798807)
  ·
    refine ⟨7999321393187559989698211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5332880928791706659798807 7999321393187559989698211)
    ·
      refine ⟨11998982089781339984547317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7999321393187559989698211 11998982089781339984547317)
      ·
        refine ⟨1124904570917000623551311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11998982089781339984547317 1124904570917000623551311)
        ·
          refine ⟨1687356856375500935326967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124904570917000623551311 1687356856375500935326967)
          ·
            refine ⟨2531035284563251402990451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1687356856375500935326967 2531035284563251402990451)
            ·
              refine ⟨3796552926844877104485677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2531035284563251402990451 3796552926844877104485677)
              ·
                refine ⟨1423707347566828914182129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3796552926844877104485677 1423707347566828914182129)
                ·
                  refine ⟨1067780510675121685636597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1423707347566828914182129 1067780510675121685636597)
                  ·
                    refine ⟨100104422875792658028431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1067780510675121685636597 100104422875792658028431)
                    ·
                      rfl

theorem cell23_584858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 2, 5].length) (baseStart_584858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584858 prefixEnd_584858 := by exact prefixLift 584858
  have htrace : WordTrace (prefixWord ++ tailWord_584858) baseStart_584858 baseEnd_584858 := by
    simpa [prefixWord, tailWord_584858, baseEnd_584858] using wordTrace_append hprefix tailTrace_584858
  have hstable : (prefixWord ++ tailWord_584858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584858).length < 2 ^ (prefixWord ++ tailWord_584858).sum := by decide
  have hdescent : baseEnd_584858 < baseStart_584858 := by decide
  rcases family_descends (prefixWord ++ tailWord_584858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584909 : List Nat := [1, 6, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_584909 : Nat := 118140960795 + 584909 * 2 ^ 59
def prefixEnd_584909 : Nat := 4983230072969 + 3 ^ 40 * 584909 * 2
def baseEnd_584909 : Nat := 100113152046919091515853

theorem tailTrace_584909 : CollatzResearch.WordTrace tailWord_584909 prefixEnd_584909 100113152046919091515853 := by
  unfold tailWord_584909
  simp only [CollatzResearch.WordTrace]
  refine ⟨21333383837982062349301781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14222255891988041566201187 21333383837982062349301781)
  ·
    refine ⟨1000002367405409172623521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21333383837982062349301781 1000002367405409172623521)
    ·
      refine ⟨750001775554056879467641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1000002367405409172623521 750001775554056879467641)
      ·
        refine ⟨562501331665542659600731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 750001775554056879467641 562501331665542659600731)
        ·
          refine ⟨843751997498313989401097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 562501331665542659600731 843751997498313989401097)
          ·
            refine ⟨632813998123735492050823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 843751997498313989401097 632813998123735492050823)
            ·
              refine ⟨949220997185603238076235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 632813998123735492050823 949220997185603238076235)
              ·
                refine ⟨1423831495778404857114353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 949220997185603238076235 1423831495778404857114353)
                ·
                  refine ⟨1067873621833803642835765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1423831495778404857114353 1067873621833803642835765)
                  ·
                    refine ⟨100113152046919091515853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1067873621833803642835765 100113152046919091515853)
                    ·
                      rfl

theorem cell23_584909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_584909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584909 prefixEnd_584909 := by exact prefixLift 584909
  have htrace : WordTrace (prefixWord ++ tailWord_584909) baseStart_584909 baseEnd_584909 := by
    simpa [prefixWord, tailWord_584909, baseEnd_584909] using wordTrace_append hprefix tailTrace_584909
  have hstable : (prefixWord ++ tailWord_584909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584909).length < 2 ^ (prefixWord ++ tailWord_584909).sum := by decide
  have hdescent : baseEnd_584909 < baseStart_584909 := by decide
  rcases family_descends (prefixWord ++ tailWord_584909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584911 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 3]
def baseStart_584911 : Nat := 118140960795 + 584911 * 2 ^ 59
def prefixEnd_584911 : Nat := 4983230072969 + 3 ^ 40 * 584911 * 2
def baseEnd_584911 : Nat := 300340483102066266722549

theorem tailTrace_584911 : CollatzResearch.WordTrace tailWord_584911 prefixEnd_584911 300340483102066266722549 := by
  unfold tailWord_584911
  simp only [CollatzResearch.WordTrace]
  refine ⟨21333456783974816690874587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14222304522649877793916391 21333456783974816690874587)
  ·
    refine ⟨32000185175962225036311881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21333456783974816690874587 32000185175962225036311881)
    ·
      refine ⟨24000138881971668777233911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32000185175962225036311881 24000138881971668777233911)
      ·
        refine ⟨36000208322957503165850867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24000138881971668777233911 36000208322957503165850867)
        ·
          refine ⟨54000312484436254748776301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36000208322957503165850867 54000312484436254748776301)
          ·
            refine ⟨20250117181663595530791113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54000312484436254748776301 20250117181663595530791113)
            ·
              refine ⟨15187587886247696648093335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20250117181663595530791113 15187587886247696648093335)
              ·
                refine ⟨22781381829371544972140003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15187587886247696648093335 22781381829371544972140003)
                ·
                  refine ⟨34172072744057317458210005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22781381829371544972140003 34172072744057317458210005)
                  ·
                    refine ⟨800907954938843377926797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34172072744057317458210005 800907954938843377926797)
                    ·
                      refine ⟨300340483102066266722549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 800907954938843377926797 300340483102066266722549)
                      ·
                        rfl

theorem cell23_584911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 3].length) (baseStart_584911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584911 prefixEnd_584911 := by exact prefixLift 584911
  have htrace : WordTrace (prefixWord ++ tailWord_584911) baseStart_584911 baseEnd_584911 := by
    simpa [prefixWord, tailWord_584911, baseEnd_584911] using wordTrace_append hprefix tailTrace_584911
  have hstable : (prefixWord ++ tailWord_584911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584911).length < 2 ^ (prefixWord ++ tailWord_584911).sum := by decide
  have hdescent : baseEnd_584911 < baseStart_584911 := by decide
  rcases family_descends (prefixWord ++ tailWord_584911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584988 : List Nat := [2, 2, 3, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_584988 : Nat := 118140960795 + 584988 * 2 ^ 59
def prefixEnd_584988 : Nat := 4983230072969 + 3 ^ 40 * 584988 * 2
def baseEnd_584988 : Nat := 300380021112462465459695

theorem tailTrace_584988 : CollatzResearch.WordTrace tailWord_584988 prefixEnd_584988 300380021112462465459695 := by
  unfold tailWord_584988
  simp only [CollatzResearch.WordTrace]
  refine ⟨10668132602347929420713809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14224176803130572560951745 10668132602347929420713809)
  ·
    refine ⟨8001099451760947065535357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10668132602347929420713809 8001099451760947065535357)
    ·
      refine ⟨3000412294410355149575759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8001099451760947065535357 3000412294410355149575759)
      ·
        refine ⟨4500618441615532724363639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3000412294410355149575759 4500618441615532724363639)
        ·
          refine ⟨6750927662423299086545459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4500618441615532724363639 6750927662423299086545459)
          ·
            refine ⟨10126391493634948629818189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6750927662423299086545459 10126391493634948629818189)
            ·
              refine ⟨3797396810113105736181821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10126391493634948629818189 3797396810113105736181821)
              ·
                refine ⟨1424023803792414651068183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3797396810113105736181821 1424023803792414651068183)
                ·
                  refine ⟨2136035705688621976602275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1424023803792414651068183 2136035705688621976602275)
                  ·
                    refine ⟨3204053558532932964903413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2136035705688621976602275 3204053558532932964903413)
                    ·
                      refine ⟨300380021112462465459695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3204053558532932964903413 300380021112462465459695)
                      ·
                        rfl

theorem cell23_584988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_584988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_584988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_584988 prefixEnd_584988 := by exact prefixLift 584988
  have htrace : WordTrace (prefixWord ++ tailWord_584988) baseStart_584988 baseEnd_584988 := by
    simpa [prefixWord, tailWord_584988, baseEnd_584988] using wordTrace_append hprefix tailTrace_584988
  have hstable : (prefixWord ++ tailWord_584988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584988).length < 2 ^ (prefixWord ++ tailWord_584988).sum := by decide
  have hdescent : baseEnd_584988 < baseStart_584988 := by decide
  rcases family_descends (prefixWord ++ tailWord_584988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585012 : List Nat := [2, 5, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_585012 : Nat := 118140960795 + 585012 * 2 ^ 59
def prefixEnd_585012 : Nat := 4983230072969 + 3 ^ 40 * 585012 * 2
def baseEnd_585012 : Nat := 100130781549390123853195

theorem tailTrace_585012 : CollatzResearch.WordTrace tailWord_585012 prefixEnd_585012 100130781549390123853195 := by
  unfold tailWord_585012
  simp only [CollatzResearch.WordTrace]
  refine ⟨10668570278304455470150645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14224760371072607293534193 10668570278304455470150645)
  ·
    refine ⟨1000178463591042700326623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10668570278304455470150645 1000178463591042700326623)
    ·
      refine ⟨1500267695386564050489935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1000178463591042700326623 1500267695386564050489935)
      ·
        refine ⟨2250401543079846075734903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1500267695386564050489935 2250401543079846075734903)
        ·
          refine ⟨3375602314619769113602355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2250401543079846075734903 3375602314619769113602355)
          ·
            refine ⟨5063403471929653670403533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3375602314619769113602355 5063403471929653670403533)
            ·
              refine ⟨1898776301973620126401325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5063403471929653670403533 1898776301973620126401325)
              ·
                refine ⟨712041113240107547400497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1898776301973620126401325 712041113240107547400497)
                ·
                  refine ⟨534030834930080660550373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 712041113240107547400497 534030834930080660550373)
                  ·
                    refine ⟨100130781549390123853195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 534030834930080660550373 100130781549390123853195)
                    ·
                      rfl

theorem cell23_585012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_585012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585012 prefixEnd_585012 := by exact prefixLift 585012
  have htrace : WordTrace (prefixWord ++ tailWord_585012) baseStart_585012 baseEnd_585012 := by
    simpa [prefixWord, tailWord_585012, baseEnd_585012] using wordTrace_append hprefix tailTrace_585012
  have hstable : (prefixWord ++ tailWord_585012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585012).length < 2 ^ (prefixWord ++ tailWord_585012).sum := by decide
  have hdescent : baseEnd_585012 < baseStart_585012 := by decide
  rcases family_descends (prefixWord ++ tailWord_585012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585068 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 1, 8]
def baseStart_585068 : Nat := 118140960795 + 585068 * 2 ^ 59
def prefixEnd_585068 : Nat := 4983230072969 + 3 ^ 40 * 585068 * 2
def baseEnd_585068 : Nat := 100140366521607384153109

theorem tailTrace_585068 : CollatzResearch.WordTrace tailWord_585068 prefixEnd_585068 100140366521607384153109 := by
  unfold tailWord_585068
  simp only [CollatzResearch.WordTrace]
  refine ⟨10669591522203016252169929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14226122029604021669559905 10669591522203016252169929)
  ·
    refine ⟨8002193641652262189127447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10669591522203016252169929 8002193641652262189127447)
    ·
      refine ⟨12003290462478393283691171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8002193641652262189127447 12003290462478393283691171)
      ·
        refine ⟨18004935693717589925536757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12003290462478393283691171 18004935693717589925536757)
        ·
          refine ⟨1687962721286024055519071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18004935693717589925536757 1687962721286024055519071)
          ·
            refine ⟨2531944081929036083278607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1687962721286024055519071 2531944081929036083278607)
            ·
              refine ⟨3797916122893554124917911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2531944081929036083278607 3797916122893554124917911)
              ·
                refine ⟨5696874184340331187376867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3797916122893554124917911 5696874184340331187376867)
                ·
                  refine ⟨8545311276510496781065301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5696874184340331187376867 8545311276510496781065301)
                  ·
                    refine ⟨100140366521607384153109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8545311276510496781065301 100140366521607384153109)
                    ·
                      rfl

theorem cell23_585068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_585068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585068 prefixEnd_585068 := by exact prefixLift 585068
  have htrace : WordTrace (prefixWord ++ tailWord_585068) baseStart_585068 baseEnd_585068 := by
    simpa [prefixWord, tailWord_585068, baseEnd_585068] using wordTrace_append hprefix tailTrace_585068
  have hstable : (prefixWord ++ tailWord_585068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585068).length < 2 ^ (prefixWord ++ tailWord_585068).sum := by decide
  have hdescent : baseEnd_585068 < baseStart_585068 := by decide
  rcases family_descends (prefixWord ++ tailWord_585068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585092 : List Nat := [2, 3, 2, 1, 1, 3, 2, 2, 1, 4, 2]
def baseStart_585092 : Nat := 118140960795 + 585092 * 2 ^ 59
def prefixEnd_585092 : Nat := 4983230072969 + 3 ^ 40 * 585092 * 2
def baseEnd_585092 : Nat := 300433423100530058559217

theorem tailTrace_585092 : CollatzResearch.WordTrace tailWord_585092 prefixEnd_585092 300433423100530058559217 := by
  unfold tailWord_585092
  simp only [CollatzResearch.WordTrace]
  refine ⟨10670029198159542301606765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14226705597546056402142353 10670029198159542301606765)
  ·
    refine ⟨4001260949309828363102537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10670029198159542301606765 4001260949309828363102537)
    ·
      refine ⟨3000945711982371272326903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4001260949309828363102537 3000945711982371272326903)
      ·
        refine ⟨4501418567973556908490355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3000945711982371272326903 4501418567973556908490355)
        ·
          refine ⟨6752127851960335362735533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4501418567973556908490355 6752127851960335362735533)
          ·
            refine ⟨2532047944485125761025825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6752127851960335362735533 2532047944485125761025825)
            ·
              refine ⟨1899035958363844320769369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2532047944485125761025825 1899035958363844320769369)
              ·
                refine ⟨1424276968772883240577027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1899035958363844320769369 1424276968772883240577027)
                ·
                  refine ⟨2136415453159324860865541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1424276968772883240577027 2136415453159324860865541)
                  ·
                    refine ⟨400577897467373411412289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2136415453159324860865541 400577897467373411412289)
                    ·
                      refine ⟨300433423100530058559217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 400577897467373411412289 300433423100530058559217)
                      ·
                        rfl

theorem cell23_585092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_585092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585092 prefixEnd_585092 := by exact prefixLift 585092
  have htrace : WordTrace (prefixWord ++ tailWord_585092) baseStart_585092 baseEnd_585092 := by
    simpa [prefixWord, tailWord_585092, baseEnd_585092] using wordTrace_append hprefix tailTrace_585092
  have hstable : (prefixWord ++ tailWord_585092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585092).length < 2 ^ (prefixWord ++ tailWord_585092).sum := by decide
  have hdescent : baseEnd_585092 < baseStart_585092 := by decide
  rcases family_descends (prefixWord ++ tailWord_585092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585096 : List Nat := [2, 1, 3, 3, 1, 4, 2, 1, 1, 3, 2]
def baseStart_585096 : Nat := 118140960795 + 585096 * 2 ^ 59
def prefixEnd_585096 : Nat := 4983230072969 + 3 ^ 40 * 585096 * 2
def baseEnd_585096 : Nat := 300435477023148042909199

theorem tailTrace_585096 : CollatzResearch.WordTrace tailWord_585096 prefixEnd_585096 300435477023148042909199 := by
  unfold tailWord_585096
  simp only [CollatzResearch.WordTrace]
  refine ⟨10670102144152296643179571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14226802858869728857572761 10670102144152296643179571)
  ·
    refine ⟨16005153216228444964769357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10670102144152296643179571 16005153216228444964769357)
    ·
      refine ⟨6001932456085666861788509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16005153216228444964769357 6001932456085666861788509)
      ·
        refine ⟨2250724671032125073170691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6001932456085666861788509 2250724671032125073170691)
        ·
          refine ⟨3376087006548187609756037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2250724671032125073170691 3376087006548187609756037)
          ·
            refine ⟨633016313727785176829257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3376087006548187609756037 633016313727785176829257)
            ·
              refine ⟨474762235295838882621943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 633016313727785176829257 474762235295838882621943)
              ·
                refine ⟨712143352943758323932915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474762235295838882621943 712143352943758323932915)
                ·
                  refine ⟨1068215029415637485899373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 712143352943758323932915 1068215029415637485899373)
                  ·
                    refine ⟨400580636030864057212265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1068215029415637485899373 400580636030864057212265)
                    ·
                      refine ⟨300435477023148042909199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 400580636030864057212265 300435477023148042909199)
                      ·
                        rfl

theorem cell23_585096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_585096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585096 prefixEnd_585096 := by exact prefixLift 585096
  have htrace : WordTrace (prefixWord ++ tailWord_585096) baseStart_585096 baseEnd_585096 := by
    simpa [prefixWord, tailWord_585096, baseEnd_585096] using wordTrace_append hprefix tailTrace_585096
  have hstable : (prefixWord ++ tailWord_585096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585096).length < 2 ^ (prefixWord ++ tailWord_585096).sum := by decide
  have hdescent : baseEnd_585096 < baseStart_585096 := by decide
  rcases family_descends (prefixWord ++ tailWord_585096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585109 : List Nat := [1, 3, 2, 1, 1, 2, 5, 2, 2, 2, 2]
def baseStart_585109 : Nat := 118140960795 + 585109 * 2 ^ 59
def prefixEnd_585109 : Nat := 4983230072969 + 3 ^ 40 * 585109 * 2
def baseEnd_585109 : Nat := 300442152271656492046639

theorem tailTrace_585109 : CollatzResearch.WordTrace tailWord_585109 prefixEnd_585109 300442152271656492046639 := by
  unfold tailWord_585109
  simp only [CollatzResearch.WordTrace]
  refine ⟨21340678437257496506582381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14227118958171664337721587 21340678437257496506582381)
  ·
    refine ⟨8002754413971561189968393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21340678437257496506582381 8002754413971561189968393)
    ·
      refine ⟨6002065810478670892476295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8002754413971561189968393 6002065810478670892476295)
      ·
        refine ⟨9003098715718006338714443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6002065810478670892476295 9003098715718006338714443)
        ·
          refine ⟨13504648073577009508071665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9003098715718006338714443 13504648073577009508071665)
          ·
            refine ⟨10128486055182757131053749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13504648073577009508071665 10128486055182757131053749)
            ·
              refine ⟨949545567673383481036289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10128486055182757131053749 949545567673383481036289)
              ·
                refine ⟨712159175755037610777217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 949545567673383481036289 712159175755037610777217)
                ·
                  refine ⟨534119381816278208082913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 712159175755037610777217 534119381816278208082913)
                  ·
                    refine ⟨400589536362208656062185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 534119381816278208082913 400589536362208656062185)
                    ·
                      refine ⟨300442152271656492046639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 400589536362208656062185 300442152271656492046639)
                      ·
                        rfl

theorem cell23_585109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 2, 2].length) (baseStart_585109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585109 prefixEnd_585109 := by exact prefixLift 585109
  have htrace : WordTrace (prefixWord ++ tailWord_585109) baseStart_585109 baseEnd_585109 := by
    simpa [prefixWord, tailWord_585109, baseEnd_585109] using wordTrace_append hprefix tailTrace_585109
  have hstable : (prefixWord ++ tailWord_585109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585109).length < 2 ^ (prefixWord ++ tailWord_585109).sum := by decide
  have hdescent : baseEnd_585109 < baseStart_585109 := by decide
  rcases family_descends (prefixWord ++ tailWord_585109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585135 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 2, 5, 2]
def baseStart_585135 : Nat := 118140960795 + 585135 * 2 ^ 59
def prefixEnd_585135 : Nat := 4983230072969 + 3 ^ 40 * 585135 * 2
def baseEnd_585135 : Nat := 300455502768673390321519

theorem tailTrace_585135 : CollatzResearch.WordTrace tailWord_585135 prefixEnd_585135 300455502768673390321519 := by
  unfold tailWord_585135
  simp only [CollatzResearch.WordTrace]
  refine ⟨21341626735163302947028859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14227751156775535298019239 21341626735163302947028859)
  ·
    refine ⟨32012440102744954420543289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21341626735163302947028859 32012440102744954420543289)
    ·
      refine ⟨24009330077058715815407467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32012440102744954420543289 24009330077058715815407467)
      ·
        refine ⟨36013995115588073723111201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24009330077058715815407467 36013995115588073723111201)
        ·
          refine ⟨27010496336691055292333401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36013995115588073723111201 27010496336691055292333401)
          ·
            refine ⟨20257872252518291469250051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27010496336691055292333401 20257872252518291469250051)
            ·
              refine ⟨30386808378777437203875077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20257872252518291469250051 30386808378777437203875077)
              ·
                refine ⟨5697526571020769475726577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30386808378777437203875077 5697526571020769475726577)
                ·
                  refine ⟨4273144928265577106794933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5697526571020769475726577 4273144928265577106794933)
                  ·
                    refine ⟨400607337024897853762025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4273144928265577106794933 400607337024897853762025)
                    ·
                      refine ⟨300455502768673390321519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 400607337024897853762025 300455502768673390321519)
                      ·
                        rfl

theorem cell23_585135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 5, 2].length) (baseStart_585135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585135 prefixEnd_585135 := by exact prefixLift 585135
  have htrace : WordTrace (prefixWord ++ tailWord_585135) baseStart_585135 baseEnd_585135 := by
    simpa [prefixWord, tailWord_585135, baseEnd_585135] using wordTrace_append hprefix tailTrace_585135
  have hstable : (prefixWord ++ tailWord_585135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585135).length < 2 ^ (prefixWord ++ tailWord_585135).sum := by decide
  have hdescent : baseEnd_585135 < baseStart_585135 := by decide
  rcases family_descends (prefixWord ++ tailWord_585135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585138 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7]
def baseStart_585138 : Nat := 118140960795 + 585138 * 2 ^ 59
def prefixEnd_585138 : Nat := 4983230072969 + 3 ^ 40 * 585138 * 2
def baseEnd_585138 : Nat := 300457043210636878584005

theorem tailTrace_585138 : CollatzResearch.WordTrace tailWord_585138 prefixEnd_585138 300457043210636878584005 := by
  unfold tailWord_585138
  simp only [CollatzResearch.WordTrace]
  refine ⟨5335434038538108614847017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14227824102768289639592045 5335434038538108614847017)
  ·
    refine ⟨4001575528903581461135263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5335434038538108614847017 4001575528903581461135263)
    ·
      refine ⟨6002363293355372191702895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4001575528903581461135263 6002363293355372191702895)
      ·
        refine ⟨9003544940033058287554343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6002363293355372191702895 9003544940033058287554343)
        ·
          refine ⟨13505317410049587431331515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9003544940033058287554343 13505317410049587431331515)
          ·
            refine ⟨20257976115074381146997273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13505317410049587431331515 20257976115074381146997273)
            ·
              refine ⟨15193482086305785860247955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20257976115074381146997273 15193482086305785860247955)
              ·
                refine ⟨22790223129458678790371933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15193482086305785860247955 22790223129458678790371933)
                ·
                  refine ⟨8546333673547004546389475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22790223129458678790371933 8546333673547004546389475)
                  ·
                    refine ⟨12819500510320506819584213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8546333673547004546389475 12819500510320506819584213)
                    ·
                      refine ⟨300457043210636878584005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 12819500510320506819584213 300457043210636878584005)
                      ·
                        rfl

theorem cell23_585138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_585138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585138 prefixEnd_585138 := by exact prefixLift 585138
  have htrace : WordTrace (prefixWord ++ tailWord_585138) baseStart_585138 baseEnd_585138 := by
    simpa [prefixWord, tailWord_585138, baseEnd_585138] using wordTrace_append hprefix tailTrace_585138
  have hstable : (prefixWord ++ tailWord_585138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585138).length < 2 ^ (prefixWord ++ tailWord_585138).sum := by decide
  have hdescent : baseEnd_585138 < baseStart_585138 := by decide
  rcases family_descends (prefixWord ++ tailWord_585138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585168 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 5]
def baseStart_585168 : Nat := 118140960795 + 585168 * 2 ^ 59
def prefixEnd_585168 : Nat := 4983230072969 + 3 ^ 40 * 585168 * 2
def baseEnd_585168 : Nat := 300472447630271761208867

theorem tailTrace_585168 : CollatzResearch.WordTrace tailWord_585168 prefixEnd_585168 300472447630271761208867 := by
  unfold tailWord_585168
  simp only [CollatzResearch.WordTrace]
  refine ⟨10671415172021874791490079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14228553562695833055320105 10671415172021874791490079)
  ·
    refine ⟨16007122758032812187235119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10671415172021874791490079 16007122758032812187235119)
    ·
      refine ⟨24010684137049218280852679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16007122758032812187235119 24010684137049218280852679)
      ·
        refine ⟨36016026205573827421279019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24010684137049218280852679 36016026205573827421279019)
        ·
          refine ⟨54024039308360741131918529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36016026205573827421279019 54024039308360741131918529)
          ·
            refine ⟨40518029481270555848938897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54024039308360741131918529 40518029481270555848938897)
            ·
              refine ⟨30388522110952916886704173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40518029481270555848938897 30388522110952916886704173)
              ·
                refine ⟨11395695791607343832514065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30388522110952916886704173 11395695791607343832514065)
                ·
                  refine ⟨8546771843705507874385549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11395695791607343832514065 8546771843705507874385549)
                  ·
                    refine ⟨3205039441389565452894581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8546771843705507874385549 3205039441389565452894581)
                    ·
                      refine ⟨300472447630271761208867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3205039441389565452894581 300472447630271761208867)
                      ·
                        rfl

theorem cell23_585168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 5].length) (baseStart_585168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585168 prefixEnd_585168 := by exact prefixLift 585168
  have htrace : WordTrace (prefixWord ++ tailWord_585168) baseStart_585168 baseEnd_585168 := by
    simpa [prefixWord, tailWord_585168, baseEnd_585168] using wordTrace_append hprefix tailTrace_585168
  have hstable : (prefixWord ++ tailWord_585168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585168).length < 2 ^ (prefixWord ++ tailWord_585168).sum := by decide
  have hdescent : baseEnd_585168 < baseStart_585168 := by decide
  rcases family_descends (prefixWord ++ tailWord_585168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585172 : List Nat := [2, 4, 1, 2, 3, 1, 1, 1, 1, 2, 5]
def baseStart_585172 : Nat := 118140960795 + 585172 * 2 ^ 59
def prefixEnd_585172 : Nat := 4983230072969 + 3 ^ 40 * 585172 * 2
def baseEnd_585172 : Nat := 300474501552889745558849

theorem tailTrace_585172 : CollatzResearch.WordTrace tailWord_585172 prefixEnd_585172 300474501552889745558849 := by
  unfold tailWord_585172
  simp only [CollatzResearch.WordTrace]
  refine ⟨10671488118014629133062885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14228650824019505510750513 10671488118014629133062885)
  ·
    refine ⟨2000904022127742962449291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10671488118014629133062885 2000904022127742962449291)
    ·
      refine ⟨3001356033191614443673937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2000904022127742962449291 3001356033191614443673937)
      ·
        refine ⟨2251017024893710832755453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3001356033191614443673937 2251017024893710832755453)
        ·
          refine ⟨844131384335141562283295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2251017024893710832755453 844131384335141562283295)
          ·
            refine ⟨1266197076502712343424943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 844131384335141562283295 1266197076502712343424943)
            ·
              refine ⟨1899295614754068515137415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1266197076502712343424943 1899295614754068515137415)
              ·
                refine ⟨2848943422131102772706123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1899295614754068515137415 2848943422131102772706123)
                ·
                  refine ⟨4273415133196654159059185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2848943422131102772706123 4273415133196654159059185)
                  ·
                    refine ⟨3205061349897490619294389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4273415133196654159059185 3205061349897490619294389)
                    ·
                      refine ⟨300474501552889745558849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3205061349897490619294389 300474501552889745558849)
                      ·
                        rfl

theorem cell23_585172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_585172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585172 prefixEnd_585172 := by exact prefixLift 585172
  have htrace : WordTrace (prefixWord ++ tailWord_585172) baseStart_585172 baseEnd_585172 := by
    simpa [prefixWord, tailWord_585172, baseEnd_585172] using wordTrace_append hprefix tailTrace_585172
  have hstable : (prefixWord ++ tailWord_585172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585172).length < 2 ^ (prefixWord ++ tailWord_585172).sum := by decide
  have hdescent : baseEnd_585172 < baseStart_585172 := by decide
  rcases family_descends (prefixWord ++ tailWord_585172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585226 : List Nat := [3, 1, 2, 2, 2, 2, 4, 2, 1, 4]
def baseStart_585226 : Nat := 118140960795 + 585226 * 2 ^ 59
def prefixEnd_585226 : Nat := 4983230072969 + 3 ^ 40 * 585226 * 2
def baseEnd_585226 : Nat := 100167409836077511427867

theorem tailTrace_585226 : CollatzResearch.WordTrace tailWord_585226 prefixEnd_585226 100167409836077511427867 := by
  unfold tailWord_585226
  simp only [CollatzResearch.WordTrace]
  refine ⟨5336236444458406372147883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14229963851889083659061021 5336236444458406372147883)
  ·
    refine ⟨8004354666687609558221825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5336236444458406372147883 8004354666687609558221825)
    ·
      refine ⟨6003266000015707168666369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8004354666687609558221825 6003266000015707168666369)
      ·
        refine ⟨4502449500011780376499777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6003266000015707168666369 4502449500011780376499777)
        ·
          refine ⟨3376837125008835282374833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4502449500011780376499777 3376837125008835282374833)
          ·
            refine ⟨2532627843756626461781125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3376837125008835282374833 2532627843756626461781125)
            ·
              refine ⟨474867720704367461583961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2532627843756626461781125 474867720704367461583961)
              ·
                refine ⟨356150790528275596187971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 474867720704367461583961 356150790528275596187971)
                ·
                  refine ⟨534226185792413394281957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 356150790528275596187971 534226185792413394281957)
                  ·
                    refine ⟨100167409836077511427867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 534226185792413394281957 100167409836077511427867)
                    ·
                      rfl

theorem cell23_585226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_585226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585226 prefixEnd_585226 := by exact prefixLift 585226
  have htrace : WordTrace (prefixWord ++ tailWord_585226) baseStart_585226 baseEnd_585226 := by
    simpa [prefixWord, tailWord_585226, baseEnd_585226] using wordTrace_append hprefix tailTrace_585226
  have hstable : (prefixWord ++ tailWord_585226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585226).length < 2 ^ (prefixWord ++ tailWord_585226).sum := by decide
  have hdescent : baseEnd_585226 < baseStart_585226 := by decide
  rcases family_descends (prefixWord ++ tailWord_585226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585235 : List Nat := [1, 1, 1, 2, 1, 6, 1, 2, 3, 5]
def baseStart_585235 : Nat := 118140960795 + 585235 * 2 ^ 59
def prefixEnd_585235 : Nat := 4983230072969 + 3 ^ 40 * 585235 * 2
def baseEnd_585235 : Nat := 100168950278040999690353

theorem tailTrace_585235 : CollatzResearch.WordTrace tailWord_585235 prefixEnd_585235 100168950278040999690353 := by
  unfold tailWord_585235
  simp only [CollatzResearch.WordTrace]
  refine ⟨21345274034801020025669159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14230182689867346683779439 21345274034801020025669159)
  ·
    refine ⟨32017911052201530038503739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21345274034801020025669159 32017911052201530038503739)
    ·
      refine ⟨48026866578302295057755609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32017911052201530038503739 48026866578302295057755609)
      ·
        refine ⟨36020149933726721293316707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48026866578302295057755609 36020149933726721293316707)
        ·
          refine ⟨54030224900590081939975061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36020149933726721293316707 54030224900590081939975061)
          ·
            refine ⟨2532666792215160090936331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 54030224900590081939975061 2532666792215160090936331)
            ·
              refine ⟨3799000188322740136404497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2532666792215160090936331 3799000188322740136404497)
              ·
                refine ⟨2849250141242055102303373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3799000188322740136404497 2849250141242055102303373)
                ·
                  refine ⟨1068468802965770663363765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2849250141242055102303373 1068468802965770663363765)
                  ·
                    refine ⟨100168950278040999690353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1068468802965770663363765 100168950278040999690353)
                    ·
                      rfl

theorem cell23_585235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 5].length) (baseStart_585235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585235 prefixEnd_585235 := by exact prefixLift 585235
  have htrace : WordTrace (prefixWord ++ tailWord_585235) baseStart_585235 baseEnd_585235 := by
    simpa [prefixWord, tailWord_585235, baseEnd_585235] using wordTrace_append hprefix tailTrace_585235
  have hstable : (prefixWord ++ tailWord_585235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585235).length < 2 ^ (prefixWord ++ tailWord_585235).sum := by decide
  have hdescent : baseEnd_585235 < baseStart_585235 := by decide
  rcases family_descends (prefixWord ++ tailWord_585235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585242 : List Nat := [3, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2]
def baseStart_585242 : Nat := 118140960795 + 585242 * 2 ^ 59
def prefixEnd_585242 : Nat := 4983230072969 + 3 ^ 40 * 585242 * 2
def baseEnd_585242 : Nat := 300510445198704471683527

theorem tailTrace_585242 : CollatzResearch.WordTrace tailWord_585242 prefixEnd_585242 300510445198704471683527 := by
  unfold tailWord_585242
  simp only [CollatzResearch.WordTrace]
  refine ⟨5336382336443915055293495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14230352897183773480782653 5336382336443915055293495)
  ·
    refine ⟨8004573504665872582940243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5336382336443915055293495 8004573504665872582940243)
    ·
      refine ⟨12006860256998808874410365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8004573504665872582940243 12006860256998808874410365)
      ·
        refine ⟨4502572596374553327903887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12006860256998808874410365 4502572596374553327903887)
        ·
          refine ⟨6753858894561829991855831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4502572596374553327903887 6753858894561829991855831)
          ·
            refine ⟨10130788341842744987783747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6753858894561829991855831 10130788341842744987783747)
            ·
              refine ⟨15196182512764117481675621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10130788341842744987783747 15196182512764117481675621)
              ·
                refine ⟨2849284221143272027814179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15196182512764117481675621 2849284221143272027814179)
                ·
                  refine ⟨4273926331714908041721269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2849284221143272027814179 4273926331714908041721269)
                  ·
                    refine ⟨400680593598272628911369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4273926331714908041721269 400680593598272628911369)
                    ·
                      refine ⟨300510445198704471683527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 400680593598272628911369 300510445198704471683527)
                      ·
                        rfl

theorem cell23_585242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_585242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585242 prefixEnd_585242 := by exact prefixLift 585242
  have htrace : WordTrace (prefixWord ++ tailWord_585242) baseStart_585242 baseEnd_585242 := by
    simpa [prefixWord, tailWord_585242, baseEnd_585242] using wordTrace_append hprefix tailTrace_585242
  have hstable : (prefixWord ++ tailWord_585242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585242).length < 2 ^ (prefixWord ++ tailWord_585242).sum := by decide
  have hdescent : baseEnd_585242 < baseStart_585242 := by decide
  rcases family_descends (prefixWord ++ tailWord_585242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585245 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_585245 : Nat := 118140960795 + 585245 * 2 ^ 59
def prefixEnd_585245 : Nat := 4983230072969 + 3 ^ 40 * 585245 * 2
def baseEnd_585245 : Nat := 300511985640667959946013

theorem tailTrace_585245 : CollatzResearch.WordTrace tailWord_585245 prefixEnd_585245 300511985640667959946013 := by
  unfold tailWord_585245
  simp only [CollatzResearch.WordTrace]
  refine ⟨21345638764764791733533189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14230425843176527822355459 21345638764764791733533189)
  ·
    refine ⟨4002307268393398450037473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21345638764764791733533189 4002307268393398450037473)
    ·
      refine ⟨3001730451295048837528105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4002307268393398450037473 3001730451295048837528105)
      ·
        refine ⟨2251297838471286628146079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3001730451295048837528105 2251297838471286628146079)
        ·
          refine ⟨3376946757706929942219119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2251297838471286628146079 3376946757706929942219119)
          ·
            refine ⟨5065420136560394913328679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3376946757706929942219119 5065420136560394913328679)
            ·
              refine ⟨7598130204840592369993019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5065420136560394913328679 7598130204840592369993019)
              ·
                refine ⟨11397195307260888554989529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7598130204840592369993019 11397195307260888554989529)
                ·
                  refine ⟨8547896480445666416242147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11397195307260888554989529 8547896480445666416242147)
                  ·
                    refine ⟨12821844720668499624363221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8547896480445666416242147 12821844720668499624363221)
                    ·
                      refine ⟨300511985640667959946013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 12821844720668499624363221 300511985640667959946013)
                      ·
                        rfl

theorem cell23_585245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_585245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585245 prefixEnd_585245 := by exact prefixLift 585245
  have htrace : WordTrace (prefixWord ++ tailWord_585245) baseStart_585245 baseEnd_585245 := by
    simpa [prefixWord, tailWord_585245, baseEnd_585245] using wordTrace_append hprefix tailTrace_585245
  have hstable : (prefixWord ++ tailWord_585245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585245).length < 2 ^ (prefixWord ++ tailWord_585245).sum := by decide
  have hdescent : baseEnd_585245 < baseStart_585245 := by decide
  rcases family_descends (prefixWord ++ tailWord_585245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585249 : List Nat := [1, 2, 3, 2, 2, 3, 1, 2, 3, 1, 3]
def baseStart_585249 : Nat := 118140960795 + 585249 * 2 ^ 59
def prefixEnd_585249 : Nat := 4983230072969 + 3 ^ 40 * 585249 * 2
def baseEnd_585249 : Nat := 300514039563285944295995

theorem tailTrace_585249 : CollatzResearch.WordTrace tailWord_585249 prefixEnd_585249 300514039563285944295995 := by
  unfold tailWord_585249
  simp only [CollatzResearch.WordTrace]
  refine ⟨21345784656750300416678801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14230523104500200277785867 21345784656750300416678801)
  ·
    refine ⟨16009338492562725312509101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21345784656750300416678801 16009338492562725312509101)
    ·
      refine ⟨6003501934711021992190913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16009338492562725312509101 6003501934711021992190913)
      ·
        refine ⟨4502626451033266494143185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6003501934711021992190913 4502626451033266494143185)
        ·
          refine ⟨3376969838274949870607389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4502626451033266494143185 3376969838274949870607389)
          ·
            refine ⟨1266363689353106201477771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3376969838274949870607389 1266363689353106201477771)
            ·
              refine ⟨1899545534029659302216657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1266363689353106201477771 1899545534029659302216657)
              ·
                refine ⟨1424659150522244476662493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1899545534029659302216657 1424659150522244476662493)
                ·
                  refine ⟨534247181445841678748435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1424659150522244476662493 534247181445841678748435)
                  ·
                    refine ⟨801370772168762518122653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 534247181445841678748435 801370772168762518122653)
                    ·
                      refine ⟨300514039563285944295995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 801370772168762518122653 300514039563285944295995)
                      ·
                        rfl

theorem cell23_585249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_585249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585249 prefixEnd_585249 := by exact prefixLift 585249
  have htrace : WordTrace (prefixWord ++ tailWord_585249) baseStart_585249 baseEnd_585249 := by
    simpa [prefixWord, tailWord_585249, baseEnd_585249] using wordTrace_append hprefix tailTrace_585249
  have hstable : (prefixWord ++ tailWord_585249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585249).length < 2 ^ (prefixWord ++ tailWord_585249).sum := by decide
  have hdescent : baseEnd_585249 < baseStart_585249 := by decide
  rcases family_descends (prefixWord ++ tailWord_585249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585269 : List Nat := [1, 3, 3, 1, 1, 3, 4, 1, 1, 5]
def baseStart_585269 : Nat := 118140960795 + 585269 * 2 ^ 59
def prefixEnd_585269 : Nat := 4983230072969 + 3 ^ 40 * 585269 * 2
def baseEnd_585269 : Nat := 100174769725458622015301

theorem tailTrace_585269 : CollatzResearch.WordTrace tailWord_585269 prefixEnd_585269 100174769725458622015301 := by
  unfold tailWord_585269
  simp only [CollatzResearch.WordTrace]
  refine ⟨21346514116677843832406861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14231009411118562554937907 21346514116677843832406861)
  ·
    refine ⟨8004942793754191437152573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21346514116677843832406861 8004942793754191437152573)
    ·
      refine ⟨3001853547657821788932215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8004942793754191437152573 3001853547657821788932215)
      ·
        refine ⟨4502780321486732683398323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3001853547657821788932215 4502780321486732683398323)
        ·
          refine ⟨6754170482230099025097485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4502780321486732683398323 6754170482230099025097485)
          ·
            refine ⟨2532813930836287134411557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6754170482230099025097485 2532813930836287134411557)
            ·
              refine ⟨474902612031803837702167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2532813930836287134411557 474902612031803837702167)
              ·
                refine ⟨712353918047705756553251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474902612031803837702167 712353918047705756553251)
                ·
                  refine ⟨1068530877071558634829877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 712353918047705756553251 1068530877071558634829877)
                  ·
                    refine ⟨100174769725458622015301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1068530877071558634829877 100174769725458622015301)
                    ·
                      rfl

theorem cell23_585269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_585269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585269 prefixEnd_585269 := by exact prefixLift 585269
  have htrace : WordTrace (prefixWord ++ tailWord_585269) baseStart_585269 baseEnd_585269 := by
    simpa [prefixWord, tailWord_585269, baseEnd_585269] using wordTrace_append hprefix tailTrace_585269
  have hstable : (prefixWord ++ tailWord_585269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585269).length < 2 ^ (prefixWord ++ tailWord_585269).sum := by decide
  have hdescent : baseEnd_585269 < baseStart_585269 := by decide
  rcases family_descends (prefixWord ++ tailWord_585269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585285 : List Nat := [1, 3, 1, 1, 1, 4, 2, 2, 1, 1, 6]
def baseStart_585285 : Nat := 118140960795 + 585285 * 2 ^ 59
def prefixEnd_585285 : Nat := 4983230072969 + 3 ^ 40 * 585285 * 2
def baseEnd_585285 : Nat := 300532524866847803445829

theorem tailTrace_585285 : CollatzResearch.WordTrace tailWord_585285 prefixEnd_585285 300532524866847803445829 := by
  unfold tailWord_585285
  simp only [CollatzResearch.WordTrace]
  refine ⟨21347097684619878564989309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14231398456413252376659539 21347097684619878564989309)
  ·
    refine ⟨8005161631732454461870991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21347097684619878564989309 8005161631732454461870991)
    ·
      refine ⟨12007742447598681692806487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8005161631732454461870991 12007742447598681692806487)
      ·
        refine ⟨18011613671398022539209731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12007742447598681692806487 18011613671398022539209731)
        ·
          refine ⟨27017420507097033808814597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18011613671398022539209731 27017420507097033808814597)
          ·
            refine ⟨5065766345080693839152737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27017420507097033808814597 5065766345080693839152737)
            ·
              refine ⟨3799324758810520379364553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5065766345080693839152737 3799324758810520379364553)
              ·
                refine ⟨2849493569107890284523415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3799324758810520379364553 2849493569107890284523415)
                ·
                  refine ⟨4274240353661835426785123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2849493569107890284523415 4274240353661835426785123)
                  ·
                    refine ⟨6411360530492753140177685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4274240353661835426785123 6411360530492753140177685)
                    ·
                      refine ⟨300532524866847803445829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6411360530492753140177685 300532524866847803445829)
                      ·
                        rfl

theorem cell23_585285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_585285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585285 prefixEnd_585285 := by exact prefixLift 585285
  have htrace : WordTrace (prefixWord ++ tailWord_585285) baseStart_585285 baseEnd_585285 := by
    simpa [prefixWord, tailWord_585285, baseEnd_585285] using wordTrace_append hprefix tailTrace_585285
  have hstable : (prefixWord ++ tailWord_585285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585285).length < 2 ^ (prefixWord ++ tailWord_585285).sum := by decide
  have hdescent : baseEnd_585285 < baseStart_585285 := by decide
  rcases family_descends (prefixWord ++ tailWord_585285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585292 : List Nat := [2, 2, 1, 3, 1, 4, 1, 2, 1, 1, 5]
def baseStart_585292 : Nat := 118140960795 + 585292 * 2 ^ 59
def prefixEnd_585292 : Nat := 4983230072969 + 3 ^ 40 * 585292 * 2
def baseEnd_585292 : Nat := 300536119231429276058297

theorem tailTrace_585292 : CollatzResearch.WordTrace tailWord_585292 prefixEnd_585292 300536119231429276058297 := by
  unfold tailWord_585292
  simp only [CollatzResearch.WordTrace]
  refine ⟨10673676497797259380247065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14231568663729679173662753 10673676497797259380247065)
  ·
    refine ⟨8005257373347944535185299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10673676497797259380247065 8005257373347944535185299)
    ·
      refine ⟨12007886060021916802777949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8005257373347944535185299 12007886060021916802777949)
      ·
        refine ⟨4502957272508218801041731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12007886060021916802777949 4502957272508218801041731)
        ·
          refine ⟨6754435908762328201562597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4502957272508218801041731 6754435908762328201562597)
          ·
            refine ⟨1266456732892936537792987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6754435908762328201562597 1266456732892936537792987)
            ·
              refine ⟨1899685099339404806689481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1266456732892936537792987 1899685099339404806689481)
              ·
                refine ⟨1424763824504553605017111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1899685099339404806689481 1424763824504553605017111)
                ·
                  refine ⟨2137145736756830407525667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1424763824504553605017111 2137145736756830407525667)
                  ·
                    refine ⟨3205718605135245611288501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2137145736756830407525667 3205718605135245611288501)
                    ·
                      refine ⟨300536119231429276058297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3205718605135245611288501 300536119231429276058297)
                      ·
                        rfl

theorem cell23_585292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_585292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585292 prefixEnd_585292 := by exact prefixLift 585292
  have htrace : WordTrace (prefixWord ++ tailWord_585292) baseStart_585292 baseEnd_585292 := by
    simpa [prefixWord, tailWord_585292, baseEnd_585292] using wordTrace_append hprefix tailTrace_585292
  have hstable : (prefixWord ++ tailWord_585292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585292).length < 2 ^ (prefixWord ++ tailWord_585292).sum := by decide
  have hdescent : baseEnd_585292 < baseStart_585292 := by decide
  rcases family_descends (prefixWord ++ tailWord_585292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585335 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 5]
def baseStart_585335 : Nat := 118140960795 + 585335 * 2 ^ 59
def prefixEnd_585335 : Nat := 4983230072969 + 3 ^ 40 * 585335 * 2
def baseEnd_585335 : Nat := 300558198899572607820599

theorem tailTrace_585335 : CollatzResearch.WordTrace tailWord_585335 prefixEnd_585335 300558198899572607820599 := by
  unfold tailWord_585335
  simp only [CollatzResearch.WordTrace]
  refine ⟨21348921334438737104309459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14232614222959158069539639 21348921334438737104309459)
  ·
    refine ⟨32023382001658105656464189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21348921334438737104309459 32023382001658105656464189)
    ·
      refine ⟨12008768250621789621174071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32023382001658105656464189 12008768250621789621174071)
      ·
        refine ⟨18013152375932684431761107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12008768250621789621174071 18013152375932684431761107)
        ·
          refine ⟨27019728563899026647641661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18013152375932684431761107 27019728563899026647641661)
          ·
            refine ⟨10132398211462134992865623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27019728563899026647641661 10132398211462134992865623)
            ·
              refine ⟨15198597317193202489298435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10132398211462134992865623 15198597317193202489298435)
              ·
                refine ⟨22797895975789803733947653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15198597317193202489298435 22797895975789803733947653)
                ·
                  refine ⟨4274605495460588200115185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22797895975789803733947653 4274605495460588200115185)
                  ·
                    refine ⟨3205954121595441150086389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4274605495460588200115185 3205954121595441150086389)
                    ·
                      refine ⟨300558198899572607820599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3205954121595441150086389 300558198899572607820599)
                      ·
                        rfl

theorem cell23_585335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_585335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585335 prefixEnd_585335 := by exact prefixLift 585335
  have htrace : WordTrace (prefixWord ++ tailWord_585335) baseStart_585335 baseEnd_585335 := by
    simpa [prefixWord, tailWord_585335, baseEnd_585335] using wordTrace_append hprefix tailTrace_585335
  have hstable : (prefixWord ++ tailWord_585335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585335).length < 2 ^ (prefixWord ++ tailWord_585335).sum := by decide
  have hdescent : baseEnd_585335 < baseStart_585335 := by decide
  rcases family_descends (prefixWord ++ tailWord_585335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585339 : List Nat := [1, 1, 1, 1, 1, 4, 4, 4, 2, 1, 3]
def baseStart_585339 : Nat := 118140960795 + 585339 * 2 ^ 59
def prefixEnd_585339 : Nat := 4983230072969 + 3 ^ 40 * 585339 * 2
def baseEnd_585339 : Nat := 300560252822190592170581

theorem tailTrace_585339 : CollatzResearch.WordTrace tailWord_585339 prefixEnd_585339 300560252822190592170581 := by
  unfold tailWord_585339
  simp only [CollatzResearch.WordTrace]
  refine ⟨21349067226424245787455071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14232711484282830524970047 21349067226424245787455071)
  ·
    refine ⟨32023600839636368681182607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21349067226424245787455071 32023600839636368681182607)
    ·
      refine ⟨48035401259454553021773911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32023600839636368681182607 48035401259454553021773911)
      ·
        refine ⟨72053101889181829532660867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48035401259454553021773911 72053101889181829532660867)
        ·
          refine ⟨108079652833772744298991301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72053101889181829532660867 108079652833772744298991301)
          ·
            refine ⟨20264934906332389556060869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108079652833772744298991301 20264934906332389556060869)
            ·
              refine ⟨3799675294937323041761413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20264934906332389556060869 3799675294937323041761413)
              ·
                refine ⟨712439117800748070330265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3799675294937323041761413 712439117800748070330265)
                ·
                  refine ⟨534329338350561052747699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 712439117800748070330265 534329338350561052747699)
                  ·
                    refine ⟨801494007525841579121549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 534329338350561052747699 801494007525841579121549)
                    ·
                      refine ⟨300560252822190592170581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 801494007525841579121549 300560252822190592170581)
                      ·
                        rfl

theorem cell23_585339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 1, 3].length) (baseStart_585339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585339 prefixEnd_585339 := by exact prefixLift 585339
  have htrace : WordTrace (prefixWord ++ tailWord_585339) baseStart_585339 baseEnd_585339 := by
    simpa [prefixWord, tailWord_585339, baseEnd_585339] using wordTrace_append hprefix tailTrace_585339
  have hstable : (prefixWord ++ tailWord_585339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585339).length < 2 ^ (prefixWord ++ tailWord_585339).sum := by decide
  have hdescent : baseEnd_585339 < baseStart_585339 := by decide
  rcases family_descends (prefixWord ++ tailWord_585339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585349 : List Nat := [1, 3, 1, 1, 4, 1, 2, 2, 3, 3, 2]
def baseStart_585349 : Nat := 118140960795 + 585349 * 2 ^ 59
def prefixEnd_585349 : Nat := 4983230072969 + 3 ^ 40 * 585349 * 2
def baseEnd_585349 : Nat := 300565387628735553045535

theorem tailTrace_585349 : CollatzResearch.WordTrace tailWord_585349 prefixEnd_585349 300565387628735553045535 := by
  unfold tailWord_585349
  simp only [CollatzResearch.WordTrace]
  refine ⟨21349431956388017495319101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14232954637592011663546067 21349431956388017495319101)
  ·
    refine ⟨8006036983645506560744663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21349431956388017495319101 8006036983645506560744663)
    ·
      refine ⟨12009055475468259841116995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8006036983645506560744663 12009055475468259841116995)
      ·
        refine ⟨18013583213202389761675493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12009055475468259841116995 18013583213202389761675493)
        ·
          refine ⟨3377546852475448080314155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18013583213202389761675493 3377546852475448080314155)
          ·
            refine ⟨5066320278713172120471233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3377546852475448080314155 5066320278713172120471233)
            ·
              refine ⟨3799740209034879090353425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5066320278713172120471233 3799740209034879090353425)
              ·
                refine ⟨2849805156776159317765069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3799740209034879090353425 2849805156776159317765069)
                ·
                  refine ⟨1068676933791059744161901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2849805156776159317765069 1068676933791059744161901)
                  ·
                    refine ⟨400753850171647404060713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1068676933791059744161901 400753850171647404060713)
                    ·
                      refine ⟨300565387628735553045535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 400753850171647404060713 300565387628735553045535)
                      ·
                        rfl

theorem cell23_585349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 3, 2].length) (baseStart_585349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585349 prefixEnd_585349 := by exact prefixLift 585349
  have htrace : WordTrace (prefixWord ++ tailWord_585349) baseStart_585349 baseEnd_585349 := by
    simpa [prefixWord, tailWord_585349, baseEnd_585349] using wordTrace_append hprefix tailTrace_585349
  have hstable : (prefixWord ++ tailWord_585349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585349).length < 2 ^ (prefixWord ++ tailWord_585349).sum := by decide
  have hdescent : baseEnd_585349 < baseStart_585349 := by decide
  rcases family_descends (prefixWord ++ tailWord_585349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585355 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 1, 8]
def baseStart_585355 : Nat := 118140960795 + 585355 * 2 ^ 59
def prefixEnd_585355 : Nat := 4983230072969 + 3 ^ 40 * 585355 * 2
def baseEnd_585355 : Nat := 100189489504220843190169

theorem tailTrace_585355 : CollatzResearch.WordTrace tailWord_585355 prefixEnd_585355 100189489504220843190169 := by
  unfold tailWord_585355
  simp only [CollatzResearch.WordTrace]
  refine ⟨21349650794366280520037519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14233100529577520346691679 21349650794366280520037519)
  ·
    refine ⟨32024476191549420780056279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21349650794366280520037519 32024476191549420780056279)
    ·
      refine ⟨48036714287324131170084419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32024476191549420780056279 48036714287324131170084419)
      ·
        refine ⟨72055071430986196755126629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48036714287324131170084419 72055071430986196755126629)
        ·
          refine ⟨13510325893309911891586243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72055071430986196755126629 13510325893309911891586243)
          ·
            refine ⟨20265488839964867837379365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13510325893309911891586243 20265488839964867837379365)
            ·
              refine ⟨3799779157493412719508631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20265488839964867837379365 3799779157493412719508631)
              ·
                refine ⟨5699668736240119079262947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3799779157493412719508631 5699668736240119079262947)
                ·
                  refine ⟨8549503104360178618894421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5699668736240119079262947 8549503104360178618894421)
                  ·
                    refine ⟨100189489504220843190169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8549503104360178618894421 100189489504220843190169)
                    ·
                      rfl

theorem cell23_585355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 8].length) (baseStart_585355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585355 prefixEnd_585355 := by exact prefixLift 585355
  have htrace : WordTrace (prefixWord ++ tailWord_585355) baseStart_585355 baseEnd_585355 := by
    simpa [prefixWord, tailWord_585355, baseEnd_585355] using wordTrace_append hprefix tailTrace_585355
  have hstable : (prefixWord ++ tailWord_585355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585355).length < 2 ^ (prefixWord ++ tailWord_585355).sum := by decide
  have hdescent : baseEnd_585355 < baseStart_585355 := by decide
  rcases family_descends (prefixWord ++ tailWord_585355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585379 : List Nat := [1, 1, 1, 4, 1, 1, 5, 2, 1, 4, 2]
def baseStart_585379 : Nat := 118140960795 + 585379 * 2 ^ 59
def prefixEnd_585379 : Nat := 4983230072969 + 3 ^ 40 * 585379 * 2
def baseEnd_585379 : Nat := 300580792048370435670397

theorem tailTrace_585379 : CollatzResearch.WordTrace tailWord_585379 prefixEnd_585379 300580792048370435670397 := by
  unfold tailWord_585379
  simp only [CollatzResearch.WordTrace]
  refine ⟨21350526146279332618911191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14233684097519555079274127 21350526146279332618911191)
  ·
    refine ⟨32025789219418998928366787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21350526146279332618911191 32025789219418998928366787)
    ·
      refine ⟨48038683829128498392550181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32025789219418998928366787 48038683829128498392550181)
      ·
        refine ⟨9007253217961593448603159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48038683829128498392550181 9007253217961593448603159)
        ·
          refine ⟨13510879826942390172904739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9007253217961593448603159 13510879826942390172904739)
          ·
            refine ⟨20266319740413585259357109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13510879826942390172904739 20266319740413585259357109)
            ·
              refine ⟨1899967475663773618064729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20266319740413585259357109 1899967475663773618064729)
              ·
                refine ⟨1424975606747830213548547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1899967475663773618064729 1424975606747830213548547)
                ·
                  refine ⟨2137463410121745320322821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1424975606747830213548547 2137463410121745320322821)
                  ·
                    refine ⟨400774389397827247560529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2137463410121745320322821 400774389397827247560529)
                    ·
                      refine ⟨300580792048370435670397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 400774389397827247560529 300580792048370435670397)
                      ·
                        rfl

theorem cell23_585379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 4, 2].length) (baseStart_585379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585379 prefixEnd_585379 := by exact prefixLift 585379
  have htrace : WordTrace (prefixWord ++ tailWord_585379) baseStart_585379 baseEnd_585379 := by
    simpa [prefixWord, tailWord_585379, baseEnd_585379] using wordTrace_append hprefix tailTrace_585379
  have hstable : (prefixWord ++ tailWord_585379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585379).length < 2 ^ (prefixWord ++ tailWord_585379).sum := by decide
  have hdescent : baseEnd_585379 < baseStart_585379 := by decide
  rcases family_descends (prefixWord ++ tailWord_585379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585390 : List Nat := [4, 1, 4, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_585390 : Nat := 118140960795 + 585390 * 2 ^ 59
def prefixEnd_585390 : Nat := 4983230072969 + 3 ^ 40 * 585390 * 2
def baseEnd_585390 : Nat := 300586440335569892632847

theorem tailTrace_585390 : CollatzResearch.WordTrace tailWord_585390 prefixEnd_585390 300586440335569892632847 := by
  unfold tailWord_585390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2668865918654935187195203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14233951566159654331707749 2668865918654935187195203)
  ·
    refine ⟨4003298877982402780792805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2668865918654935187195203 4003298877982402780792805)
    ·
      refine ⟨750618539621700521398651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4003298877982402780792805 750618539621700521398651)
      ·
        refine ⟨1125927809432550782097977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 750618539621700521398651 1125927809432550782097977)
        ·
          refine ⟨844445857074413086573483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1125927809432550782097977 844445857074413086573483)
          ·
            refine ⟨1266668785611619629860225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 844445857074413086573483 1266668785611619629860225)
            ·
              refine ⟨950001589208714722395169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1266668785611619629860225 950001589208714722395169)
              ·
                refine ⟨712501191906536041796377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 950001589208714722395169 712501191906536041796377)
                ·
                  refine ⟨534375893929902031347283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 712501191906536041796377 534375893929902031347283)
                  ·
                    refine ⟨801563840894853047020925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 534375893929902031347283 801563840894853047020925)
                    ·
                      refine ⟨300586440335569892632847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 801563840894853047020925 300586440335569892632847)
                      ·
                        rfl

theorem cell23_585390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_585390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585390 prefixEnd_585390 := by exact prefixLift 585390
  have htrace : WordTrace (prefixWord ++ tailWord_585390) baseStart_585390 baseEnd_585390 := by
    simpa [prefixWord, tailWord_585390, baseEnd_585390] using wordTrace_append hprefix tailTrace_585390
  have hstable : (prefixWord ++ tailWord_585390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585390).length < 2 ^ (prefixWord ++ tailWord_585390).sum := by decide
  have hdescent : baseEnd_585390 < baseStart_585390 := by decide
  rcases family_descends (prefixWord ++ tailWord_585390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585432 : List Nat := [2, 1, 2, 2, 3, 1, 3, 1, 1, 7]
def baseStart_585432 : Nat := 118140960795 + 585432 * 2 ^ 59
def prefixEnd_585432 : Nat := 4983230072969 + 3 ^ 40 * 585432 * 2
def baseEnd_585432 : Nat := 100202668841019576102551

theorem tailTrace_585432 : CollatzResearch.WordTrace tailWord_585432 prefixEnd_585432 100202668841019576102551 := by
  unfold tailWord_585432
  simp only [CollatzResearch.WordTrace]
  refine ⟨10676229607543661335295275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14234972810058215113727033 10676229607543661335295275)
  ·
    refine ⟨16014344411315492002942913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10676229607543661335295275 16014344411315492002942913)
    ·
      refine ⟨12010758308486619002207185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16014344411315492002942913 12010758308486619002207185)
      ·
        refine ⟨9008068731364964251655389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12010758308486619002207185 9008068731364964251655389)
        ·
          refine ⟨3378025774261861594370771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9008068731364964251655389 3378025774261861594370771)
          ·
            refine ⟨5067038661392792391556157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3378025774261861594370771 5067038661392792391556157)
            ·
              refine ⟨1900139498022297146833559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5067038661392792391556157 1900139498022297146833559)
              ·
                refine ⟨2850209247033445720250339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1900139498022297146833559 2850209247033445720250339)
                ·
                  refine ⟨4275313870550168580375509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2850209247033445720250339 4275313870550168580375509)
                  ·
                    refine ⟨100202668841019576102551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4275313870550168580375509 100202668841019576102551)
                    ·
                      rfl

theorem cell23_585432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_585432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585432 prefixEnd_585432 := by exact prefixLift 585432
  have htrace : WordTrace (prefixWord ++ tailWord_585432) baseStart_585432 baseEnd_585432 := by
    simpa [prefixWord, tailWord_585432, baseEnd_585432] using wordTrace_append hprefix tailTrace_585432
  have hstable : (prefixWord ++ tailWord_585432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585432).length < 2 ^ (prefixWord ++ tailWord_585432).sum := by decide
  have hdescent : baseEnd_585432 < baseStart_585432 := by decide
  rcases family_descends (prefixWord ++ tailWord_585432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585447 : List Nat := [1, 1, 5, 4, 1, 2, 1, 2, 2, 2, 2]
def baseStart_585447 : Nat := 118140960795 + 585447 * 2 ^ 59
def prefixEnd_585447 : Nat := 4983230072969 + 3 ^ 40 * 585447 * 2
def baseEnd_585447 : Nat := 300615708732876169620085

theorem tailTrace_585447 : CollatzResearch.WordTrace tailWord_585447 prefixEnd_585447 300615708732876169620085 := by
  unfold tailWord_585447
  simp only [CollatzResearch.WordTrace]
  refine ⟨21353006310032980232386595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14235337540021986821591063 21353006310032980232386595)
  ·
    refine ⟨32029509465049470348579893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21353006310032980232386595 32029509465049470348579893)
    ·
      refine ⟨3002766512348387845179365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32029509465049470348579893 3002766512348387845179365)
      ·
        refine ⟨563018721065322720971131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3002766512348387845179365 563018721065322720971131)
        ·
          refine ⟨844528081597984081456697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563018721065322720971131 844528081597984081456697)
          ·
            refine ⟨633396061198488061092523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 844528081597984081456697 633396061198488061092523)
            ·
              refine ⟨950094091797732091638785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 633396061198488061092523 950094091797732091638785)
              ·
                refine ⟨712570568848299068729089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 950094091797732091638785 712570568848299068729089)
                ·
                  refine ⟨534427926636224301546817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 712570568848299068729089 534427926636224301546817)
                  ·
                    refine ⟨400820944977168226160113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 534427926636224301546817 400820944977168226160113)
                    ·
                      refine ⟨300615708732876169620085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 400820944977168226160113 300615708732876169620085)
                      ·
                        rfl

theorem cell23_585447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_585447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585447 prefixEnd_585447 := by exact prefixLift 585447
  have htrace : WordTrace (prefixWord ++ tailWord_585447) baseStart_585447 baseEnd_585447 := by
    simpa [prefixWord, tailWord_585447, baseEnd_585447] using wordTrace_append hprefix tailTrace_585447
  have hstable : (prefixWord ++ tailWord_585447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585447).length < 2 ^ (prefixWord ++ tailWord_585447).sum := by decide
  have hdescent : baseEnd_585447 < baseStart_585447 := by decide
  rcases family_descends (prefixWord ++ tailWord_585447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585469 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 1, 6, 2]
def baseStart_585469 : Nat := 118140960795 + 585469 * 2 ^ 59
def prefixEnd_585469 : Nat := 4983230072969 + 3 ^ 40 * 585469 * 2
def baseEnd_585469 : Nat := 300627005307275083544983

theorem tailTrace_585469 : CollatzResearch.WordTrace tailWord_585469 prefixEnd_585469 300627005307275083544983 := by
  unfold tailWord_585469
  simp only [CollatzResearch.WordTrace]
  refine ⟨21353808715953277989687461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14235872477302185326458307 21353808715953277989687461)
  ·
    refine ⟨4003839134241239623066399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21353808715953277989687461 4003839134241239623066399)
    ·
      refine ⟨6005758701361859434599599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4003839134241239623066399 6005758701361859434599599)
      ·
        refine ⟨9008638052042789151899399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6005758701361859434599599 9008638052042789151899399)
        ·
          refine ⟨13512957078064183727849099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9008638052042789151899399 13512957078064183727849099)
          ·
            refine ⟨20269435617096275591773649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13512957078064183727849099 20269435617096275591773649)
            ·
              refine ⟨15202076712822206693830237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20269435617096275591773649 15202076712822206693830237)
              ·
                refine ⟨5700778767308327510186339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15202076712822206693830237 5700778767308327510186339)
                ·
                  refine ⟨8551168150962491265279509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5700778767308327510186339 8551168150962491265279509)
                  ·
                    refine ⟨400836007076366778059977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8551168150962491265279509 400836007076366778059977)
                    ·
                      refine ⟨300627005307275083544983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 400836007076366778059977 300627005307275083544983)
                      ·
                        rfl

theorem cell23_585469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 6, 2].length) (baseStart_585469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585469 prefixEnd_585469 := by exact prefixLift 585469
  have htrace : WordTrace (prefixWord ++ tailWord_585469) baseStart_585469 baseEnd_585469 := by
    simpa [prefixWord, tailWord_585469, baseEnd_585469] using wordTrace_append hprefix tailTrace_585469
  have hstable : (prefixWord ++ tailWord_585469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585469).length < 2 ^ (prefixWord ++ tailWord_585469).sum := by decide
  have hdescent : baseEnd_585469 < baseStart_585469 := by decide
  rcases family_descends (prefixWord ++ tailWord_585469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585489 : List Nat := [1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 3]
def baseStart_585489 : Nat := 118140960795 + 585489 * 2 ^ 59
def prefixEnd_585489 : Nat := 4983230072969 + 3 ^ 40 * 585489 * 2
def baseEnd_585489 : Nat := 300637274920365005294891

theorem tailTrace_585489 : CollatzResearch.WordTrace tailWord_585489 prefixEnd_585489 300637274920365005294891 := by
  unfold tailWord_585489
  simp only [CollatzResearch.WordTrace]
  refine ⟨21354538175880821405415521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14236358783920547603610347 21354538175880821405415521)
  ·
    refine ⟨16015903631910616054061641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21354538175880821405415521 16015903631910616054061641)
    ·
      refine ⟨12011927723932962040546231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16015903631910616054061641 12011927723932962040546231)
      ·
        refine ⟨18017891585899443060819347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12011927723932962040546231 18017891585899443060819347)
        ·
          refine ⟨27026837378849164591229021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18017891585899443060819347 27026837378849164591229021)
          ·
            refine ⟨10135064017068436721710883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27026837378849164591229021 10135064017068436721710883)
            ·
              refine ⟨15202596025602655082566325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10135064017068436721710883 15202596025602655082566325)
              ·
                refine ⟨1425243377400248913990593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15202596025602655082566325 1425243377400248913990593)
                ·
                  refine ⟨1068932533050186685492945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1425243377400248913990593 1068932533050186685492945)
                  ·
                    refine ⟨801699399787640014119709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1068932533050186685492945 801699399787640014119709)
                    ·
                      refine ⟨300637274920365005294891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 801699399787640014119709 300637274920365005294891)
                      ·
                        rfl

theorem cell23_585489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 3].length) (baseStart_585489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585489 prefixEnd_585489 := by exact prefixLift 585489
  have htrace : WordTrace (prefixWord ++ tailWord_585489) baseStart_585489 baseEnd_585489 := by
    simpa [prefixWord, tailWord_585489, baseEnd_585489] using wordTrace_append hprefix tailTrace_585489
  have hstable : (prefixWord ++ tailWord_585489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585489).length < 2 ^ (prefixWord ++ tailWord_585489).sum := by decide
  have hdescent : baseEnd_585489 < baseStart_585489 := by decide
  rcases family_descends (prefixWord ++ tailWord_585489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585506 : List Nat := [3, 3, 1, 1, 2, 1, 3, 2, 2, 2, 3]
def baseStart_585506 : Nat := 118140960795 + 585506 * 2 ^ 59
def prefixEnd_585506 : Nat := 4983230072969 + 3 ^ 40 * 585506 * 2
def baseEnd_585506 : Nat := 300646004091491438782313

theorem tailTrace_585506 : CollatzResearch.WordTrace tailWord_585506 prefixEnd_585506 300646004091491438782313 := by
  unfold tailWord_585506
  simp only [CollatzResearch.WordTrace]
  refine ⟨5338789554204808327196093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14236772144546155539189581 5338789554204808327196093)
  ·
    refine ⟨2002046082826803122698535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5338789554204808327196093 2002046082826803122698535)
    ·
      refine ⟨3003069124240204684047803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2002046082826803122698535 3003069124240204684047803)
      ·
        refine ⟨4504603686360307026071705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3003069124240204684047803 4504603686360307026071705)
        ·
          refine ⟨3378452764770230269553779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4504603686360307026071705 3378452764770230269553779)
          ·
            refine ⟨5067679147155345404330669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3378452764770230269553779 5067679147155345404330669)
            ·
              refine ⟨1900379680183254526624001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5067679147155345404330669 1900379680183254526624001)
              ·
                refine ⟨1425284760137440894968001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1900379680183254526624001 1425284760137440894968001)
                ·
                  refine ⟨1068963570103080671226001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1425284760137440894968001 1068963570103080671226001)
                  ·
                    refine ⟨801722677577310503419501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1068963570103080671226001 801722677577310503419501)
                    ·
                      refine ⟨300646004091491438782313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 801722677577310503419501 300646004091491438782313)
                      ·
                        rfl

theorem cell23_585506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_585506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585506 prefixEnd_585506 := by exact prefixLift 585506
  have htrace : WordTrace (prefixWord ++ tailWord_585506) baseStart_585506 baseEnd_585506 := by
    simpa [prefixWord, tailWord_585506, baseEnd_585506] using wordTrace_append hprefix tailTrace_585506
  have hstable : (prefixWord ++ tailWord_585506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585506).length < 2 ^ (prefixWord ++ tailWord_585506).sum := by decide
  have hdescent : baseEnd_585506 < baseStart_585506 := by decide
  rcases family_descends (prefixWord ++ tailWord_585506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585539 : List Nat := [1, 1, 1, 3, 1, 6, 1, 1, 3, 5]
def baseStart_585539 : Nat := 118140960795 + 585539 * 2 ^ 59
def prefixEnd_585539 : Nat := 4983230072969 + 3 ^ 40 * 585539 * 2
def baseEnd_585539 : Nat := 100220982984363269889887

theorem tailTrace_585539 : CollatzResearch.WordTrace tailWord_585539 prefixEnd_585539 100220982984363269889887 := by
  unfold tailWord_585539
  simp only [CollatzResearch.WordTrace]
  refine ⟨21356361825699679944735671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14237574550466453296490447 21356361825699679944735671)
  ·
    refine ⟨32034542738549519917103507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21356361825699679944735671 32034542738549519917103507)
    ·
      refine ⟨48051814107824279875655261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32034542738549519917103507 48051814107824279875655261)
      ·
        refine ⟨18019430290434104953370723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48051814107824279875655261 18019430290434104953370723)
        ·
          refine ⟨27029145435651157430056085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18019430290434104953370723 27029145435651157430056085)
          ·
            refine ⟨1266991192296148004533879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27029145435651157430056085 1266991192296148004533879)
            ·
              refine ⟨1900486788444222006800819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1266991192296148004533879 1900486788444222006800819)
              ·
                refine ⟨2850730182666333010201229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1900486788444222006800819 2850730182666333010201229)
                ·
                  refine ⟨1069023818499874878825461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2850730182666333010201229 1069023818499874878825461)
                  ·
                    refine ⟨100220982984363269889887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1069023818499874878825461 100220982984363269889887)
                    ·
                      rfl

theorem cell23_585539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 5].length) (baseStart_585539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585539 prefixEnd_585539 := by exact prefixLift 585539
  have htrace : WordTrace (prefixWord ++ tailWord_585539) baseStart_585539 baseEnd_585539 := by
    simpa [prefixWord, tailWord_585539, baseEnd_585539] using wordTrace_append hprefix tailTrace_585539
  have hstable : (prefixWord ++ tailWord_585539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585539).length < 2 ^ (prefixWord ++ tailWord_585539).sum := by decide
  have hdescent : baseEnd_585539 < baseStart_585539 := by decide
  rcases family_descends (prefixWord ++ tailWord_585539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585564 : List Nat := [2, 2, 4, 2, 3, 1, 2, 2, 1, 4]
def baseStart_585564 : Nat := 118140960795 + 585564 * 2 ^ 59
def prefixEnd_585564 : Nat := 4983230072969 + 3 ^ 40 * 585564 * 2
def baseEnd_585564 : Nat := 100225261989817403952349

theorem tailTrace_585564 : CollatzResearch.WordTrace tailWord_585564 prefixEnd_585564 100225261989817403952349 := by
  unfold tailWord_585564
  simp only [CollatzResearch.WordTrace]
  refine ⟨10678636825304554607197873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14238182433739406142930497 10678636825304554607197873)
  ·
    refine ⟨8008977618978415955398405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10678636825304554607197873 8008977618978415955398405)
    ·
      refine ⟨1501683303558452991637201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8008977618978415955398405 1501683303558452991637201)
      ·
        refine ⟨1126262477668839743727901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1501683303558452991637201 1126262477668839743727901)
        ·
          refine ⟨422348429125814903897963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1126262477668839743727901 422348429125814903897963)
          ·
            refine ⟨633522643688722355846945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422348429125814903897963 633522643688722355846945)
            ·
              refine ⟨475141982766541766885209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 633522643688722355846945 475141982766541766885209)
              ·
                refine ⟨356356487074906325163907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 475141982766541766885209 356356487074906325163907)
                ·
                  refine ⟨534534730612359487745861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 356356487074906325163907 534534730612359487745861)
                  ·
                    refine ⟨100225261989817403952349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 534534730612359487745861 100225261989817403952349)
                    ·
                      rfl

theorem cell23_585564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_585564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585564 prefixEnd_585564 := by exact prefixLift 585564
  have htrace : WordTrace (prefixWord ++ tailWord_585564) baseStart_585564 baseEnd_585564 := by
    simpa [prefixWord, tailWord_585564, baseEnd_585564] using wordTrace_append hprefix tailTrace_585564
  have hstable : (prefixWord ++ tailWord_585564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585564).length < 2 ^ (prefixWord ++ tailWord_585564).sum := by decide
  have hdescent : baseEnd_585564 < baseStart_585564 := by decide
  rcases family_descends (prefixWord ++ tailWord_585564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585593 : List Nat := [1, 2, 1, 3, 2, 2, 3, 2, 3, 2, 2]
def baseStart_585593 : Nat := 118140960795 + 585593 * 2 ^ 59
def prefixEnd_585593 : Nat := 4983230072969 + 3 ^ 40 * 585593 * 2
def baseEnd_585593 : Nat := 300690676908432598394413

theorem tailTrace_585593 : CollatzResearch.WordTrace tailWord_585593 prefixEnd_585593 300690676908432598394413 := by
  unfold tailWord_585593
  simp only [CollatzResearch.WordTrace]
  refine ⟨21358331367504047167201433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14238887578336031444800955 21358331367504047167201433)
  ·
    refine ⟨16018748525628035375401075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21358331367504047167201433 16018748525628035375401075)
    ·
      refine ⟨24028122788442053063101613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16018748525628035375401075 24028122788442053063101613)
      ·
        refine ⟨9010546045665769898663105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24028122788442053063101613 9010546045665769898663105)
        ·
          refine ⟨6757909534249327423997329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9010546045665769898663105 6757909534249327423997329)
          ·
            refine ⟨5068432150686995567997997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6757909534249327423997329 5068432150686995567997997)
            ·
              refine ⟨1900662056507623337999249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5068432150686995567997997 1900662056507623337999249)
              ·
                refine ⟨1425496542380717503499437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1900662056507623337999249 1425496542380717503499437)
                ·
                  refine ⟨534561203392769063812289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1425496542380717503499437 534561203392769063812289)
                  ·
                    refine ⟨400920902544576797859217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 534561203392769063812289 400920902544576797859217)
                    ·
                      refine ⟨300690676908432598394413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 400920902544576797859217 300690676908432598394413)
                      ·
                        rfl

theorem cell23_585593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 2, 2].length) (baseStart_585593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585593 prefixEnd_585593 := by exact prefixLift 585593
  have htrace : WordTrace (prefixWord ++ tailWord_585593) baseStart_585593 baseEnd_585593 := by
    simpa [prefixWord, tailWord_585593, baseEnd_585593] using wordTrace_append hprefix tailTrace_585593
  have hstable : (prefixWord ++ tailWord_585593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585593).length < 2 ^ (prefixWord ++ tailWord_585593).sum := by decide
  have hdescent : baseEnd_585593 < baseStart_585593 := by decide
  rcases family_descends (prefixWord ++ tailWord_585593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585620 : List Nat := [2, 4, 2, 1, 1, 4, 1, 2, 2, 4]
def baseStart_585620 : Nat := 118140960795 + 585620 * 2 ^ 59
def prefixEnd_585620 : Nat := 4983230072969 + 3 ^ 40 * 585620 * 2
def baseEnd_585620 : Nat := 100234846962034664252263

theorem tailTrace_585620 : CollatzResearch.WordTrace tailWord_585620 prefixEnd_585620 100234846962034664252263 := by
  unfold tailWord_585620
  simp only [CollatzResearch.WordTrace]
  refine ⟨10679658069203115389217157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14239544092270820518956209 10679658069203115389217157)
  ·
    refine ⟨2002435887975584135478217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10679658069203115389217157 2002435887975584135478217)
    ·
      refine ⟨1501826915981688101608663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2002435887975584135478217 1501826915981688101608663)
      ·
        refine ⟨2252740373972532152412995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1501826915981688101608663 2252740373972532152412995)
        ·
          refine ⟨3379110560958798228619493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2252740373972532152412995 3379110560958798228619493)
          ·
            refine ⟨633583230179774667866155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3379110560958798228619493 633583230179774667866155)
            ·
              refine ⟨950374845269662001799233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 633583230179774667866155 950374845269662001799233)
              ·
                refine ⟨712781133952246501349425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 950374845269662001799233 712781133952246501349425)
                ·
                  refine ⟨534585850464184876012069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 712781133952246501349425 534585850464184876012069)
                  ·
                    refine ⟨100234846962034664252263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 534585850464184876012069 100234846962034664252263)
                    ·
                      rfl

theorem cell23_585620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_585620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585620 prefixEnd_585620 := by exact prefixLift 585620
  have htrace : WordTrace (prefixWord ++ tailWord_585620) baseStart_585620 baseEnd_585620 := by
    simpa [prefixWord, tailWord_585620, baseEnd_585620] using wordTrace_append hprefix tailTrace_585620
  have hstable : (prefixWord ++ tailWord_585620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585620).length < 2 ^ (prefixWord ++ tailWord_585620).sum := by decide
  have hdescent : baseEnd_585620 < baseStart_585620 := by decide
  rcases family_descends (prefixWord ++ tailWord_585620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585630 : List Nat := [4, 3, 1, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_585630 : Nat := 118140960795 + 585630 * 2 ^ 59
def prefixEnd_585630 : Nat := 4983230072969 + 3 ^ 40 * 585630 * 2
def baseEnd_585630 : Nat := 300709675692648953631743

theorem tailTrace_585630 : CollatzResearch.WordTrace tailWord_585630 prefixEnd_585630 300709675692648953631743 := by
  unfold tailWord_585630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2669960108546250310787293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14239787245580001657532229 2669960108546250310787293)
  ·
    refine ⟨1001235040704843866545235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2669960108546250310787293 1001235040704843866545235)
    ·
      refine ⟨1501852561057265799817853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1001235040704843866545235 1501852561057265799817853)
      ·
        refine ⟨563194710396474674931695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1501852561057265799817853 563194710396474674931695)
        ·
          refine ⟨844792065594712012397543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563194710396474674931695 844792065594712012397543)
          ·
            refine ⟨1267188098392068018596315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 844792065594712012397543 1267188098392068018596315)
            ·
              refine ⟨1900782147588102027894473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1267188098392068018596315 1900782147588102027894473)
              ·
                refine ⟨1425586610691076520920855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1900782147588102027894473 1425586610691076520920855)
                ·
                  refine ⟨2138379916036614781381283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1425586610691076520920855 2138379916036614781381283)
                  ·
                    refine ⟨3207569874054922172071925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2138379916036614781381283 3207569874054922172071925)
                    ·
                      refine ⟨300709675692648953631743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3207569874054922172071925 300709675692648953631743)
                      ·
                        rfl

theorem cell23_585630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_585630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585630 prefixEnd_585630 := by exact prefixLift 585630
  have htrace : WordTrace (prefixWord ++ tailWord_585630) baseStart_585630 baseEnd_585630 := by
    simpa [prefixWord, tailWord_585630, baseEnd_585630] using wordTrace_append hprefix tailTrace_585630
  have hstable : (prefixWord ++ tailWord_585630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585630).length < 2 ^ (prefixWord ++ tailWord_585630).sum := by decide
  have hdescent : baseEnd_585630 < baseStart_585630 := by decide
  rcases family_descends (prefixWord ++ tailWord_585630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585700 : List Nat := [2, 3, 1, 1, 1, 1, 5, 3, 2, 2, 2]
def baseStart_585700 : Nat := 118140960795 + 585700 * 2 ^ 59
def prefixEnd_585700 : Nat := 4983230072969 + 3 ^ 40 * 585700 * 2
def baseEnd_585700 : Nat := 300745619338463679756421

theorem tailTrace_585700 : CollatzResearch.WordTrace tailWord_585700 prefixEnd_585700 300745619338463679756421 := by
  unfold tailWord_585700
  simp only [CollatzResearch.WordTrace]
  refine ⟨10681116989058202220673277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14241489318744269627564369 10681116989058202220673277)
  ·
    refine ⟨4005418870896825832752479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10681116989058202220673277 4005418870896825832752479)
    ·
      refine ⟨6008128306345238749128719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4005418870896825832752479 6008128306345238749128719)
      ·
        refine ⟨9012192459517858123693079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6008128306345238749128719 9012192459517858123693079)
        ·
          refine ⟨13518288689276787185539619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9012192459517858123693079 13518288689276787185539619)
          ·
            refine ⟨20277433033915180778309429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13518288689276787185539619 20277433033915180778309429)
            ·
              refine ⟨1901009346929548197966509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20277433033915180778309429 1901009346929548197966509)
              ·
                refine ⟨712878505098580574237441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1901009346929548197966509 712878505098580574237441)
                ·
                  refine ⟨534658878823935430678081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 712878505098580574237441 534658878823935430678081)
                  ·
                    refine ⟨400994159117951573008561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 534658878823935430678081 400994159117951573008561)
                    ·
                      refine ⟨300745619338463679756421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 400994159117951573008561 300745619338463679756421)
                      ·
                        rfl

theorem cell23_585700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 2, 2, 2].length) (baseStart_585700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585700 prefixEnd_585700 := by exact prefixLift 585700
  have htrace : WordTrace (prefixWord ++ tailWord_585700) baseStart_585700 baseEnd_585700 := by
    simpa [prefixWord, tailWord_585700, baseEnd_585700] using wordTrace_append hprefix tailTrace_585700
  have hstable : (prefixWord ++ tailWord_585700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585700).length < 2 ^ (prefixWord ++ tailWord_585700).sum := by decide
  have hdescent : baseEnd_585700 < baseStart_585700 := by decide
  rcases family_descends (prefixWord ++ tailWord_585700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585736 : List Nat := [2, 1, 3, 2, 1, 2, 1, 4, 2, 5]
def baseStart_585736 : Nat := 118140960795 + 585736 * 2 ^ 59
def prefixEnd_585736 : Nat := 4983230072969 + 3 ^ 40 * 585736 * 2
def baseEnd_585736 : Nat := 100254701547341846302085

theorem tailTrace_585736 : CollatzResearch.WordTrace tailWord_585736 prefixEnd_585736 100254701547341846302085 := by
  unfold tailWord_585736
  simp only [CollatzResearch.WordTrace]
  refine ⟨10681773502992991294828531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14242364670657321726438041 10681773502992991294828531)
  ·
    refine ⟨16022660254489486942242797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10681773502992991294828531 16022660254489486942242797)
    ·
      refine ⟨6008497595433557603341049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16022660254489486942242797 6008497595433557603341049)
      ·
        refine ⟨4506373196575168202505787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6008497595433557603341049 4506373196575168202505787)
        ·
          refine ⟨6759559794862752303758681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4506373196575168202505787 6759559794862752303758681)
          ·
            refine ⟨5069669846147064227819011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6759559794862752303758681 5069669846147064227819011)
            ·
              refine ⟨7604504769220596341728517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5069669846147064227819011 7604504769220596341728517)
              ·
                refine ⟨1425844644228861814074097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7604504769220596341728517 1425844644228861814074097)
                ·
                  refine ⟨1069383483171646360555573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1425844644228861814074097 1069383483171646360555573)
                  ·
                    refine ⟨100254701547341846302085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1069383483171646360555573 100254701547341846302085)
                    ·
                      rfl

theorem cell23_585736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_585736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585736 prefixEnd_585736 := by exact prefixLift 585736
  have htrace : WordTrace (prefixWord ++ tailWord_585736) baseStart_585736 baseEnd_585736 := by
    simpa [prefixWord, tailWord_585736, baseEnd_585736] using wordTrace_append hprefix tailTrace_585736
  have hstable : (prefixWord ++ tailWord_585736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585736).length < 2 ^ (prefixWord ++ tailWord_585736).sum := by decide
  have hdescent : baseEnd_585736 < baseStart_585736 := by decide
  rcases family_descends (prefixWord ++ tailWord_585736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585770 : List Nat := [3, 1, 4, 1, 2, 3, 1, 1, 2, 5]
def baseStart_585770 : Nat := 118140960795 + 585770 * 2 ^ 59
def prefixEnd_585770 : Nat := 4983230072969 + 3 ^ 40 * 585770 * 2
def baseEnd_585770 : Nat := 100260520994759468627033

theorem tailTrace_585770 : CollatzResearch.WordTrace tailWord_585770 prefixEnd_585770 100260520994759468627033 := by
  unfold tailWord_585770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5341196771965701599098691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14243191391908537597596509 5341196771965701599098691)
  ·
    refine ⟨8011795157948552398648037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5341196771965701599098691 8011795157948552398648037)
    ·
      refine ⟨1502211592115353574746507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8011795157948552398648037 1502211592115353574746507)
      ·
        refine ⟨2253317388173030362119761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1502211592115353574746507 2253317388173030362119761)
        ·
          refine ⟨1689988041129772771589821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2253317388173030362119761 1689988041129772771589821)
          ·
            refine ⟨633745515423664789346183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1689988041129772771589821 633745515423664789346183)
            ·
              refine ⟨950618273135497184019275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 633745515423664789346183 950618273135497184019275)
              ·
                refine ⟨1425927409703245776028913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 950618273135497184019275 1425927409703245776028913)
                ·
                  refine ⟨1069445557277434332021685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1425927409703245776028913 1069445557277434332021685)
                  ·
                    refine ⟨100260520994759468627033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1069445557277434332021685 100260520994759468627033)
                    ·
                      rfl

theorem cell23_585770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_585770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585770 prefixEnd_585770 := by exact prefixLift 585770
  have htrace : WordTrace (prefixWord ++ tailWord_585770) baseStart_585770 baseEnd_585770 := by
    simpa [prefixWord, tailWord_585770, baseEnd_585770] using wordTrace_append hprefix tailTrace_585770
  have hstable : (prefixWord ++ tailWord_585770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585770).length < 2 ^ (prefixWord ++ tailWord_585770).sum := by decide
  have hdescent : baseEnd_585770 < baseStart_585770 := by decide
  rcases family_descends (prefixWord ++ tailWord_585770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585823 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 5, 1, 3]
def baseStart_585823 : Nat := 118140960795 + 585823 * 2 ^ 59
def prefixEnd_585823 : Nat := 4983230072969 + 3 ^ 40 * 585823 * 2
def baseEnd_585823 : Nat := 300808777458966698518355

theorem tailTrace_585823 : CollatzResearch.WordTrace tailWord_585823 prefixEnd_585823 300808777458966698518355 := by
  unfold tailWord_585823
  simp only [CollatzResearch.WordTrace]
  refine ⟨21366720156670796448074123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14244480104447197632049415 21366720156670796448074123)
  ·
    refine ⟨32050080235006194672111185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21366720156670796448074123 32050080235006194672111185)
    ·
      refine ⟨24037560176254646004083389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32050080235006194672111185 24037560176254646004083389)
      ·
        refine ⟨9014085066095492251531271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24037560176254646004083389 9014085066095492251531271)
        ·
          refine ⟨13521127599143238377296907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9014085066095492251531271 13521127599143238377296907)
          ·
            refine ⟨20281691398714857565945361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13521127599143238377296907 20281691398714857565945361)
            ·
              refine ⟨15211268549036143174459021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20281691398714857565945361 15211268549036143174459021)
              ·
                refine ⟨5704225705888553690422133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15211268549036143174459021 5704225705888553690422133)
                ·
                  refine ⟨534771159927051908477075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5704225705888553690422133 534771159927051908477075)
                  ·
                    refine ⟨802156739890577862715613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 534771159927051908477075 802156739890577862715613)
                    ·
                      refine ⟨300808777458966698518355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 802156739890577862715613 300808777458966698518355)
                      ·
                        rfl

theorem cell23_585823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_585823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585823 prefixEnd_585823 := by exact prefixLift 585823
  have htrace : WordTrace (prefixWord ++ tailWord_585823) baseStart_585823 baseEnd_585823 := by
    simpa [prefixWord, tailWord_585823, baseEnd_585823] using wordTrace_append hprefix tailTrace_585823
  have hstable : (prefixWord ++ tailWord_585823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585823).length < 2 ^ (prefixWord ++ tailWord_585823).sum := by decide
  have hdescent : baseEnd_585823 < baseStart_585823 := by decide
  rcases family_descends (prefixWord ++ tailWord_585823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585833 : List Nat := [1, 2, 1, 1, 1, 5, 1, 3, 1, 5, 2]
def baseStart_585833 : Nat := 118140960795 + 585833 * 2 ^ 59
def prefixEnd_585833 : Nat := 4983230072969 + 3 ^ 40 * 585833 * 2
def baseEnd_585833 : Nat := 300813912265511659393309

theorem tailTrace_585833 : CollatzResearch.WordTrace tailWord_585833 prefixEnd_585833 300813912265511659393309 := by
  unfold tailWord_585833
  simp only [CollatzResearch.WordTrace]
  refine ⟨21367084886634568155938153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14244723257756378770625435 21367084886634568155938153)
  ·
    refine ⟨16025313664975926116953615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21367084886634568155938153 16025313664975926116953615)
    ·
      refine ⟨24037970497463889175430423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16025313664975926116953615 24037970497463889175430423)
      ·
        refine ⟨36056955746195833763145635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24037970497463889175430423 36056955746195833763145635)
        ·
          refine ⟨54085433619293750644718453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36056955746195833763145635 54085433619293750644718453)
          ·
            refine ⟨5070509401808789122942355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54085433619293750644718453 5070509401808789122942355)
            ·
              refine ⟨7605764102713183684413533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5070509401808789122942355 7605764102713183684413533)
              ·
                refine ⟨2852161538517443881655075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7605764102713183684413533 2852161538517443881655075)
                ·
                  refine ⟨4278242307776165822482613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2852161538517443881655075 4278242307776165822482613)
                  ·
                    refine ⟨401085216354015545857745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4278242307776165822482613 401085216354015545857745)
                    ·
                      refine ⟨300813912265511659393309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 401085216354015545857745 300813912265511659393309)
                      ·
                        rfl

theorem cell23_585833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 5, 2].length) (baseStart_585833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585833 prefixEnd_585833 := by exact prefixLift 585833
  have htrace : WordTrace (prefixWord ++ tailWord_585833) baseStart_585833 baseEnd_585833 := by
    simpa [prefixWord, tailWord_585833, baseEnd_585833] using wordTrace_append hprefix tailTrace_585833
  have hstable : (prefixWord ++ tailWord_585833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585833).length < 2 ^ (prefixWord ++ tailWord_585833).sum := by decide
  have hdescent : baseEnd_585833 < baseStart_585833 := by decide
  rcases family_descends (prefixWord ++ tailWord_585833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585834 : List Nat := [3, 1, 3, 2, 3, 2, 1, 3, 1, 4]
def baseStart_585834 : Nat := 118140960795 + 585834 * 2 ^ 59
def prefixEnd_585834 : Nat := 4983230072969 + 3 ^ 40 * 585834 * 2
def baseEnd_585834 : Nat := 100271475248722051826935

theorem tailTrace_585834 : CollatzResearch.WordTrace tailWord_585834 prefixEnd_585834 100271475248722051826935 := by
  unfold tailWord_585834
  simp only [CollatzResearch.WordTrace]
  refine ⟨5341780339907736331681139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14244747573087296884483037 5341780339907736331681139)
  ·
    refine ⟨8012670509861604497521709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5341780339907736331681139 8012670509861604497521709)
    ·
      refine ⟨3004751441198101686570641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8012670509861604497521709 3004751441198101686570641)
      ·
        refine ⟨2253563580898576264927981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3004751441198101686570641 2253563580898576264927981)
        ·
          refine ⟨845086342836966099347993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2253563580898576264927981 845086342836966099347993)
          ·
            refine ⟨633814757127724574510995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 845086342836966099347993 633814757127724574510995)
            ·
              refine ⟨950722135691586861766493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 633814757127724574510995 950722135691586861766493)
              ·
                refine ⟨356520800884345073162435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 950722135691586861766493 356520800884345073162435)
                ·
                  refine ⟨534781201326517609743653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 356520800884345073162435 534781201326517609743653)
                  ·
                    refine ⟨100271475248722051826935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 534781201326517609743653 100271475248722051826935)
                    ·
                      rfl

theorem cell23_585834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_585834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585834 prefixEnd_585834 := by exact prefixLift 585834
  have htrace : WordTrace (prefixWord ++ tailWord_585834) baseStart_585834 baseEnd_585834 := by
    simpa [prefixWord, tailWord_585834, baseEnd_585834] using wordTrace_append hprefix tailTrace_585834
  have hstable : (prefixWord ++ tailWord_585834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585834).length < 2 ^ (prefixWord ++ tailWord_585834).sum := by decide
  have hdescent : baseEnd_585834 < baseStart_585834 := by decide
  rcases family_descends (prefixWord ++ tailWord_585834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585878 : List Nat := [5, 3, 2, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_585878 : Nat := 118140960795 + 585878 * 2 ^ 59
def prefixEnd_585878 : Nat := 4983230072969 + 3 ^ 40 * 585878 * 2
def baseEnd_585878 : Nat := 300837018894963983330603

theorem tailTrace_585878 : CollatzResearch.WordTrace tailWord_585878 prefixEnd_585878 300837018894963983330603 := by
  unfold tailWord_585878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1335545385716971302582893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14245817447647693894217525 1335545385716971302582893)
  ·
    refine ⟨500829519643864238468585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1335545385716971302582893 500829519643864238468585)
    ·
      refine ⟨375622139732898178851439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 500829519643864238468585 375622139732898178851439)
      ·
        refine ⟨563433209599347268277159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375622139732898178851439 563433209599347268277159)
        ·
          refine ⟨845149814399020902415739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563433209599347268277159 845149814399020902415739)
          ·
            refine ⟨1267724721598531353623609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845149814399020902415739 1267724721598531353623609)
            ·
              refine ⟨950793541198898515217707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1267724721598531353623609 950793541198898515217707)
              ·
                refine ⟨1426190311798347772826561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 950793541198898515217707 1426190311798347772826561)
                ·
                  refine ⟨1069642733848760829619921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1426190311798347772826561 1069642733848760829619921)
                  ·
                    refine ⟨802232050386570622214941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1069642733848760829619921 802232050386570622214941)
                    ·
                      refine ⟨300837018894963983330603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 802232050386570622214941 300837018894963983330603)
                      ·
                        rfl

theorem cell23_585878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_585878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585878 prefixEnd_585878 := by exact prefixLift 585878
  have htrace : WordTrace (prefixWord ++ tailWord_585878) baseStart_585878 baseEnd_585878 := by
    simpa [prefixWord, tailWord_585878, baseEnd_585878] using wordTrace_append hprefix tailTrace_585878
  have hstable : (prefixWord ++ tailWord_585878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585878).length < 2 ^ (prefixWord ++ tailWord_585878).sum := by decide
  have hdescent : baseEnd_585878 < baseStart_585878 := by decide
  rcases family_descends (prefixWord ++ tailWord_585878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585880 : List Nat := [2, 1, 2, 4, 3, 1, 1, 1, 3, 1, 4]
def baseStart_585880 : Nat := 118140960795 + 585880 * 2 ^ 59
def prefixEnd_585880 : Nat := 4983230072969 + 3 ^ 40 * 585880 * 2
def baseEnd_585880 : Nat := 300838045856272975505593

theorem tailTrace_585880 : CollatzResearch.WordTrace tailWord_585880 prefixEnd_585880 300838045856272975505593 := by
  unfold tailWord_585880
  simp only [CollatzResearch.WordTrace]
  refine ⟨10684399558732147591449547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14245866078309530121932729 10684399558732147591449547)
  ·
    refine ⟨16026599338098221387174321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10684399558732147591449547 16026599338098221387174321)
    ·
      refine ⟨12019949503573666040380741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16026599338098221387174321 12019949503573666040380741)
      ·
        refine ⟨2253740531920062382571389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12019949503573666040380741 2253740531920062382571389)
        ·
          refine ⟨845152699470023393464271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2253740531920062382571389 845152699470023393464271)
          ·
            refine ⟨1267729049205035090196407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845152699470023393464271 1267729049205035090196407)
            ·
              refine ⟨1901593573807552635294611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1267729049205035090196407 1901593573807552635294611)
              ·
                refine ⟨2852390360711328952941917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1901593573807552635294611 2852390360711328952941917)
                ·
                  refine ⟨1069646385266748357353219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2852390360711328952941917 1069646385266748357353219)
                  ·
                    refine ⟨1604469577900122536029829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1069646385266748357353219 1604469577900122536029829)
                    ·
                      refine ⟨300838045856272975505593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1604469577900122536029829 300838045856272975505593)
                      ·
                        rfl

theorem cell23_585880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_585880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585880 prefixEnd_585880 := by exact prefixLift 585880
  have htrace : WordTrace (prefixWord ++ tailWord_585880) baseStart_585880 baseEnd_585880 := by
    simpa [prefixWord, tailWord_585880, baseEnd_585880] using wordTrace_append hprefix tailTrace_585880
  have hstable : (prefixWord ++ tailWord_585880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585880).length < 2 ^ (prefixWord ++ tailWord_585880).sum := by decide
  have hdescent : baseEnd_585880 < baseStart_585880 := by decide
  rcases family_descends (prefixWord ++ tailWord_585880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585890 : List Nat := [3, 3, 1, 3, 1, 2, 1, 2, 1, 6]
def baseStart_585890 : Nat := 118140960795 + 585890 * 2 ^ 59
def prefixEnd_585890 : Nat := 4983230072969 + 3 ^ 40 * 585890 * 2
def baseEnd_585890 : Nat := 100281060220939312126849

theorem tailTrace_585890 : CollatzResearch.WordTrace tailWord_585890 prefixEnd_585890 100281060220939312126849 := by
  unfold tailWord_585890
  simp only [CollatzResearch.WordTrace]
  refine ⟨5342290961857016722690781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14246109231618711260508749 5342290961857016722690781)
  ·
    refine ⟨2003359110696381271009043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5342290961857016722690781 2003359110696381271009043)
    ·
      refine ⟨3005038666044571906513565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2003359110696381271009043 3005038666044571906513565)
      ·
        refine ⟨1126889499766714464942587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3005038666044571906513565 1126889499766714464942587)
        ·
          refine ⟨1690334249650071697413881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1126889499766714464942587 1690334249650071697413881)
          ·
            refine ⟨1267750687237553773060411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1690334249650071697413881 1267750687237553773060411)
            ·
              refine ⟨1901626030856330659590617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1267750687237553773060411 1901626030856330659590617)
              ·
                refine ⟨1426219523142247994692963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1901626030856330659590617 1426219523142247994692963)
                ·
                  refine ⟨2139329284713371992039445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1426219523142247994692963 2139329284713371992039445)
                  ·
                    refine ⟨100281060220939312126849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2139329284713371992039445 100281060220939312126849)
                    ·
                      rfl

theorem cell23_585890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_585890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585890 prefixEnd_585890 := by exact prefixLift 585890
  have htrace : WordTrace (prefixWord ++ tailWord_585890) baseStart_585890 baseEnd_585890 := by
    simpa [prefixWord, tailWord_585890, baseEnd_585890] using wordTrace_append hprefix tailTrace_585890
  have hstable : (prefixWord ++ tailWord_585890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585890).length < 2 ^ (prefixWord ++ tailWord_585890).sum := by decide
  have hdescent : baseEnd_585890 < baseStart_585890 := by decide
  rcases family_descends (prefixWord ++ tailWord_585890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585893 : List Nat := [1, 3, 1, 2, 1, 3, 3, 2, 1, 2, 4]
def baseStart_585893 : Nat := 118140960795 + 585893 * 2 ^ 59
def prefixEnd_585893 : Nat := 4983230072969 + 3 ^ 40 * 585893 * 2
def baseEnd_585893 : Nat := 300844721104781424643033

theorem tailTrace_585893 : CollatzResearch.WordTrace tailWord_585893 prefixEnd_585893 300844721104781424643033 := by
  unfold tailWord_585893
  simp only [CollatzResearch.WordTrace]
  refine ⟨21369273266417198403122333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14246182177611465602081555 21369273266417198403122333)
  ·
    refine ⟨8013477474906449401170875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21369273266417198403122333 8013477474906449401170875)
    ·
      refine ⟨12020216212359674101756313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8013477474906449401170875 12020216212359674101756313)
      ·
        refine ⟨9015162159269755576317235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12020216212359674101756313 9015162159269755576317235)
        ·
          refine ⟨13522743238904633364475853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9015162159269755576317235 13522743238904633364475853)
          ·
            refine ⟨5071028714589237511678445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13522743238904633364475853 5071028714589237511678445)
            ·
              refine ⟨1901635767970964066879417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5071028714589237511678445 1901635767970964066879417)
              ·
                refine ⟨1426226825978223050159563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1901635767970964066879417 1426226825978223050159563)
                ·
                  refine ⟨2139340238967334575239345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1426226825978223050159563 2139340238967334575239345)
                  ·
                    refine ⟨1604505179225500931429509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2139340238967334575239345 1604505179225500931429509)
                    ·
                      refine ⟨300844721104781424643033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1604505179225500931429509 300844721104781424643033)
                      ·
                        rfl

theorem cell23_585893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_585893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585893 prefixEnd_585893 := by exact prefixLift 585893
  have htrace : WordTrace (prefixWord ++ tailWord_585893) baseStart_585893 baseEnd_585893 := by
    simpa [prefixWord, tailWord_585893, baseEnd_585893] using wordTrace_append hprefix tailTrace_585893
  have hstable : (prefixWord ++ tailWord_585893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585893).length < 2 ^ (prefixWord ++ tailWord_585893).sum := by decide
  have hdescent : baseEnd_585893 < baseStart_585893 := by decide
  rcases family_descends (prefixWord ++ tailWord_585893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585913 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 3, 3, 3]
def baseStart_585913 : Nat := 118140960795 + 585913 * 2 ^ 59
def prefixEnd_585913 : Nat := 4983230072969 + 3 ^ 40 * 585913 * 2
def baseEnd_585913 : Nat := 300854990717871346392941

theorem tailTrace_585913 : CollatzResearch.WordTrace tailWord_585913 prefixEnd_585913 300854990717871346392941 := by
  unfold tailWord_585913
  simp only [CollatzResearch.WordTrace]
  refine ⟨21370002726344741818850393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14246668484229827879233595 21370002726344741818850393)
  ·
    refine ⟨16027502044758556364137795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21370002726344741818850393 16027502044758556364137795)
    ·
      refine ⟨24041253067137834546206693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16027502044758556364137795 24041253067137834546206693)
      ·
        refine ⟨4507734950088343977413755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24041253067137834546206693 4507734950088343977413755)
        ·
          refine ⟨6761602425132515966120633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4507734950088343977413755 6761602425132515966120633)
          ·
            refine ⟨5071201818849386974590475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6761602425132515966120633 5071201818849386974590475)
            ·
              refine ⟨7606802728274080461885713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5071201818849386974590475 7606802728274080461885713)
              ·
                refine ⟨5705102046205560346414285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7606802728274080461885713 5705102046205560346414285)
                ·
                  refine ⟨2139413267327085129905357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5705102046205560346414285 2139413267327085129905357)
                  ·
                    refine ⟨802279975247656923714509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2139413267327085129905357 802279975247656923714509)
                    ·
                      refine ⟨300854990717871346392941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 802279975247656923714509 300854990717871346392941)
                      ·
                        rfl

theorem cell23_585913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_585913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585913 prefixEnd_585913 := by exact prefixLift 585913
  have htrace : WordTrace (prefixWord ++ tailWord_585913) baseStart_585913 baseEnd_585913 := by
    simpa [prefixWord, tailWord_585913, baseEnd_585913] using wordTrace_append hprefix tailTrace_585913
  have hstable : (prefixWord ++ tailWord_585913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585913).length < 2 ^ (prefixWord ++ tailWord_585913).sum := by decide
  have hdescent : baseEnd_585913 < baseStart_585913 := by decide
  rcases family_descends (prefixWord ++ tailWord_585913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585930 : List Nat := [3, 1, 2, 1, 3, 1, 4, 1, 1, 3, 3]
def baseStart_585930 : Nat := 118140960795 + 585930 * 2 ^ 59
def prefixEnd_585930 : Nat := 4983230072969 + 3 ^ 40 * 585930 * 2
def baseEnd_585930 : Nat := 300863719888997779880363

theorem tailTrace_585930 : CollatzResearch.WordTrace tailWord_585930 prefixEnd_585930 300863719888997779880363 := by
  unfold tailWord_585930
  simp only [CollatzResearch.WordTrace]
  refine ⟨5342655691820788430554811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14247081844855435814812829 5342655691820788430554811)
  ·
    refine ⟨8013983537731182645832217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5342655691820788430554811 8013983537731182645832217)
    ·
      refine ⟨6010487653298386984374163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8013983537731182645832217 6010487653298386984374163)
      ·
        refine ⟨9015731479947580476561245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6010487653298386984374163 9015731479947580476561245)
        ·
          refine ⟨3380899304980342678710467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9015731479947580476561245 3380899304980342678710467)
          ·
            refine ⟨5071348957470514018065701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3380899304980342678710467 5071348957470514018065701)
            ·
              refine ⟨950877929525721378387319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5071348957470514018065701 950877929525721378387319)
              ·
                refine ⟨1426316894288582067580979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 950877929525721378387319 1426316894288582067580979)
                ·
                  refine ⟨2139475341432873101371469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1426316894288582067580979 2139475341432873101371469)
                  ·
                    refine ⟨802303253037327413014301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2139475341432873101371469 802303253037327413014301)
                    ·
                      refine ⟨300863719888997779880363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 802303253037327413014301 300863719888997779880363)
                      ·
                        rfl

theorem cell23_585930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_585930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585930 prefixEnd_585930 := by exact prefixLift 585930
  have htrace : WordTrace (prefixWord ++ tailWord_585930) baseStart_585930 baseEnd_585930 := by
    simpa [prefixWord, tailWord_585930, baseEnd_585930] using wordTrace_append hprefix tailTrace_585930
  have hstable : (prefixWord ++ tailWord_585930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585930).length < 2 ^ (prefixWord ++ tailWord_585930).sum := by decide
  have hdescent : baseEnd_585930 < baseStart_585930 := by decide
  rcases family_descends (prefixWord ++ tailWord_585930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585948 : List Nat := [2, 2, 5, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_585948 : Nat := 118140960795 + 585948 * 2 ^ 59
def prefixEnd_585948 : Nat := 4983230072969 + 3 ^ 40 * 585948 * 2
def baseEnd_585948 : Nat := 300872962540778709455281

theorem tailTrace_585948 : CollatzResearch.WordTrace tailWord_585948 prefixEnd_585948 300872962540778709455281 := by
  unfold tailWord_585948
  simp only [CollatzResearch.WordTrace]
  refine ⟨10685639640608971398187249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14247519520811961864249665 10685639640608971398187249)
  ·
    refine ⟨8014229730456728548640437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10685639640608971398187249 8014229730456728548640437)
    ·
      refine ⟨751334037230318301435041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8014229730456728548640437 751334037230318301435041)
      ·
        refine ⟨563500527922738726076281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 751334037230318301435041 563500527922738726076281)
        ·
          refine ⟨422625395942054044557211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 563500527922738726076281 422625395942054044557211)
          ·
            refine ⟨633938093913081066835817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422625395942054044557211 633938093913081066835817)
            ·
              refine ⟨475453570434810800126863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 633938093913081066835817 475453570434810800126863)
              ·
                refine ⟨713180355652216200190295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 475453570434810800126863 713180355652216200190295)
                ·
                  refine ⟨1069770533478324300285443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 713180355652216200190295 1069770533478324300285443)
                  ·
                    refine ⟨1604655800217486450428165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1069770533478324300285443 1604655800217486450428165)
                    ·
                      refine ⟨300872962540778709455281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1604655800217486450428165 300872962540778709455281)
                      ·
                        rfl

theorem cell23_585948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_585948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585948 prefixEnd_585948 := by exact prefixLift 585948
  have htrace : WordTrace (prefixWord ++ tailWord_585948) baseStart_585948 baseEnd_585948 := by
    simpa [prefixWord, tailWord_585948, baseEnd_585948] using wordTrace_append hprefix tailTrace_585948
  have hstable : (prefixWord ++ tailWord_585948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585948).length < 2 ^ (prefixWord ++ tailWord_585948).sum := by decide
  have hdescent : baseEnd_585948 < baseStart_585948 := by decide
  rcases family_descends (prefixWord ++ tailWord_585948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585983 : List Nat := [1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 4]
def baseStart_585983 : Nat := 118140960795 + 585983 * 2 ^ 59
def prefixEnd_585983 : Nat := 4983230072969 + 3 ^ 40 * 585983 * 2
def baseEnd_585983 : Nat := 300890934363686072517619

theorem tailTrace_585983 : CollatzResearch.WordTrace tailWord_585983 prefixEnd_585983 300890934363686072517619 := by
  unfold tailWord_585983
  simp only [CollatzResearch.WordTrace]
  refine ⟨21372555836091143773898603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14248370557394095849265735 21372555836091143773898603)
  ·
    refine ⟨32058833754136715660847905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21372555836091143773898603 32058833754136715660847905)
    ·
      refine ⟨24044125315602536745635929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32058833754136715660847905 24044125315602536745635929)
      ·
        refine ⟨18033093986701902559226947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24044125315602536745635929 18033093986701902559226947)
        ·
          refine ⟨27049640980052853838840421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18033093986701902559226947 27049640980052853838840421)
          ·
            refine ⟨5071807683759910094782579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27049640980052853838840421 5071807683759910094782579)
            ·
              refine ⟨7607711525639865142173869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5071807683759910094782579 7607711525639865142173869)
              ·
                refine ⟨2852891822114949428315201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7607711525639865142173869 2852891822114949428315201)
                ·
                  refine ⟨2139668866586212071236401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2852891822114949428315201 2139668866586212071236401)
                  ·
                    refine ⟨1604751649939659053427301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2139668866586212071236401 1604751649939659053427301)
                    ·
                      refine ⟨300890934363686072517619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1604751649939659053427301 300890934363686072517619)
                      ·
                        rfl

theorem cell23_585983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_585983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585983 prefixEnd_585983 := by exact prefixLift 585983
  have htrace : WordTrace (prefixWord ++ tailWord_585983) baseStart_585983 baseEnd_585983 := by
    simpa [prefixWord, tailWord_585983, baseEnd_585983] using wordTrace_append hprefix tailTrace_585983
  have hstable : (prefixWord ++ tailWord_585983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585983).length < 2 ^ (prefixWord ++ tailWord_585983).sum := by decide
  have hdescent : baseEnd_585983 < baseStart_585983 := by decide
  rcases family_descends (prefixWord ++ tailWord_585983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585991 : List Nat := [1, 1, 4, 5, 1, 1, 2, 2, 1, 3, 2]
def baseStart_585991 : Nat := 118140960795 + 585991 * 2 ^ 59
def prefixEnd_585991 : Nat := 4983230072969 + 3 ^ 40 * 585991 * 2
def baseEnd_585991 : Nat := 300895042208922041217583

theorem tailTrace_585991 : CollatzResearch.WordTrace tailWord_585991 prefixEnd_585991 300895042208922041217583 := by
  unfold tailWord_585991
  simp only [CollatzResearch.WordTrace]
  refine ⟨21372847620062161140189827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14248565080041440760126551 21372847620062161140189827)
  ·
    refine ⟨32059271430093241710284741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21372847620062161140189827 32059271430093241710284741)
    ·
      refine ⟨6011113393142482820678389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32059271430093241710284741 6011113393142482820678389)
      ·
        refine ⟨563541880607107764438599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6011113393142482820678389 563541880607107764438599)
        ·
          refine ⟨845312820910661646657899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563541880607107764438599 845312820910661646657899)
          ·
            refine ⟨1267969231365992469986849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845312820910661646657899 1267969231365992469986849)
            ·
              refine ⟨950976923524494352490137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1267969231365992469986849 950976923524494352490137)
              ·
                refine ⟨713232692643370764367603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 950976923524494352490137 713232692643370764367603)
                ·
                  refine ⟨1069849038965056146551405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 713232692643370764367603 1069849038965056146551405)
                  ·
                    refine ⟨401193389611896054956777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1069849038965056146551405 401193389611896054956777)
                    ·
                      refine ⟨300895042208922041217583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 401193389611896054956777 300895042208922041217583)
                      ·
                        rfl

theorem cell23_585991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_585991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585991 prefixEnd_585991 := by exact prefixLift 585991
  have htrace : WordTrace (prefixWord ++ tailWord_585991) baseStart_585991 baseEnd_585991 := by
    simpa [prefixWord, tailWord_585991, baseEnd_585991] using wordTrace_append hprefix tailTrace_585991
  have hstable : (prefixWord ++ tailWord_585991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585991).length < 2 ^ (prefixWord ++ tailWord_585991).sum := by decide
  have hdescent : baseEnd_585991 < baseStart_585991 := by decide
  rcases family_descends (prefixWord ++ tailWord_585991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585993 : List Nat := [1, 2, 1, 1, 3, 4, 2, 2, 7]
def baseStart_585993 : Nat := 118140960795 + 585993 * 2 ^ 59
def prefixEnd_585993 : Nat := 4983230072969 + 3 ^ 40 * 585993 * 2
def baseEnd_585993 : Nat := 33432896574470114821397

theorem tailTrace_585993 : CollatzResearch.WordTrace tailWord_585993 prefixEnd_585993 33432896574470114821397 := by
  unfold tailWord_585993
  simp only [CollatzResearch.WordTrace]
  refine ⟨21372920566054915481762633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14248613710703276987841755 21372920566054915481762633)
  ·
    refine ⟨16029690424541186611321975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21372920566054915481762633 16029690424541186611321975)
    ·
      refine ⟨24044535636811779916982963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16029690424541186611321975 24044535636811779916982963)
      ·
        refine ⟨36066803455217669875474445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24044535636811779916982963 36066803455217669875474445)
        ·
          refine ⟨13525051295706626203302917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36066803455217669875474445 13525051295706626203302917)
          ·
            refine ⟨2535947117944992413119297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13525051295706626203302917 2535947117944992413119297)
            ·
              refine ⟨1901960338458744309839473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2535947117944992413119297 1901960338458744309839473)
              ·
                refine ⟨1426470253844058232379605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1901960338458744309839473 1426470253844058232379605)
                ·
                  refine ⟨33432896574470114821397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1426470253844058232379605 33432896574470114821397)
                  ·
                    rfl

theorem cell23_585993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 7].length) (baseStart_585993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_585993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_585993 prefixEnd_585993 := by exact prefixLift 585993
  have htrace : WordTrace (prefixWord ++ tailWord_585993) baseStart_585993 baseEnd_585993 := by
    simpa [prefixWord, tailWord_585993, baseEnd_585993] using wordTrace_append hprefix tailTrace_585993
  have hstable : (prefixWord ++ tailWord_585993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585993).length < 2 ^ (prefixWord ++ tailWord_585993).sum := by decide
  have hdescent : baseEnd_585993 < baseStart_585993 := by decide
  rcases family_descends (prefixWord ++ tailWord_585993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586003 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 3]
def baseStart_586003 : Nat := 118140960795 + 586003 * 2 ^ 59
def prefixEnd_586003 : Nat := 4983230072969 + 3 ^ 40 * 586003 * 2
def baseEnd_586003 : Nat := 300901203976775994267527

theorem tailTrace_586003 : CollatzResearch.WordTrace tailWord_586003 prefixEnd_586003 300901203976775994267527 := by
  unfold tailWord_586003
  simp only [CollatzResearch.WordTrace]
  refine ⟨21373285296018687189626663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14248856864012458126417775 21373285296018687189626663)
  ·
    refine ⟨32059927944028030784439995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21373285296018687189626663 32059927944028030784439995)
    ·
      refine ⟨48089891916042046176659993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32059927944028030784439995 48089891916042046176659993)
      ·
        refine ⟨36067418937031534632494995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48089891916042046176659993 36067418937031534632494995)
        ·
          refine ⟨54101128405547301948742493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36067418937031534632494995 54101128405547301948742493)
          ·
            refine ⟨20287923152080238230778435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54101128405547301948742493 20287923152080238230778435)
            ·
              refine ⟨30431884728120357346167653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20287923152080238230778435 30431884728120357346167653)
              ·
                refine ⟨5705978386522567002406435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30431884728120357346167653 5705978386522567002406435)
                ·
                  refine ⟨8558967579783850503609653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5705978386522567002406435 8558967579783850503609653)
                  ·
                    refine ⟨802403210604735984713405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8558967579783850503609653 802403210604735984713405)
                    ·
                      refine ⟨300901203976775994267527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 802403210604735984713405 300901203976775994267527)
                      ·
                        rfl

theorem cell23_586003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 3].length) (baseStart_586003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586003 prefixEnd_586003 := by exact prefixLift 586003
  have htrace : WordTrace (prefixWord ++ tailWord_586003) baseStart_586003 baseEnd_586003 := by
    simpa [prefixWord, tailWord_586003, baseEnd_586003] using wordTrace_append hprefix tailTrace_586003
  have hstable : (prefixWord ++ tailWord_586003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586003).length < 2 ^ (prefixWord ++ tailWord_586003).sum := by decide
  have hdescent : baseEnd_586003 < baseStart_586003 := by decide
  rcases family_descends (prefixWord ++ tailWord_586003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586073 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 2, 1, 6]
def baseStart_586073 : Nat := 118140960795 + 586073 * 2 ^ 59
def prefixEnd_586073 : Nat := 4983230072969 + 3 ^ 40 * 586073 * 2
def baseEnd_586073 : Nat := 300937147622590720392205

theorem tailTrace_586073 : CollatzResearch.WordTrace tailWord_586073 prefixEnd_586073 300937147622590720392205 := by
  unfold tailWord_586073
  simp only [CollatzResearch.WordTrace]
  refine ⟨21375838405765089144674873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14250558937176726096449915 21375838405765089144674873)
  ·
    refine ⟨16031878804323816858506155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21375838405765089144674873 16031878804323816858506155)
    ·
      refine ⟨24047818206485725287759233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16031878804323816858506155 24047818206485725287759233)
      ·
        refine ⟨18035863654864293965819425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24047818206485725287759233 18035863654864293965819425)
        ·
          refine ⟨13526897741148220474364569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18035863654864293965819425 13526897741148220474364569)
          ·
            refine ⟨10145173305861165355773427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13526897741148220474364569 10145173305861165355773427)
            ·
              refine ⟨15217759958791748033660141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10145173305861165355773427 15217759958791748033660141)
              ·
                refine ⟨5706659984546905512622553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15217759958791748033660141 5706659984546905512622553)
                ·
                  refine ⟨4279994988410179134466915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5706659984546905512622553 4279994988410179134466915)
                  ·
                    refine ⟨6419992482615268701700373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4279994988410179134466915 6419992482615268701700373)
                    ·
                      refine ⟨300937147622590720392205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6419992482615268701700373 300937147622590720392205)
                      ·
                        rfl

theorem cell23_586073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_586073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586073 prefixEnd_586073 := by exact prefixLift 586073
  have htrace : WordTrace (prefixWord ++ tailWord_586073) baseStart_586073 baseEnd_586073 := by
    simpa [prefixWord, tailWord_586073, baseEnd_586073] using wordTrace_append hprefix tailTrace_586073
  have hstable : (prefixWord ++ tailWord_586073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586073).length < 2 ^ (prefixWord ++ tailWord_586073).sum := by decide
  have hdescent : baseEnd_586073 < baseStart_586073 := by decide
  rcases family_descends (prefixWord ++ tailWord_586073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586103 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 6]
def baseStart_586103 : Nat := 118140960795 + 586103 * 2 ^ 59
def prefixEnd_586103 : Nat := 4983230072969 + 3 ^ 40 * 586103 * 2
def baseEnd_586103 : Nat := 300952552042225603017067

theorem tailTrace_586103 : CollatzResearch.WordTrace tailWord_586103 prefixEnd_586103 300952552042225603017067 := by
  unfold tailWord_586103
  simp only [CollatzResearch.WordTrace]
  refine ⟨21376932595656404268266963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14251288397104269512177975 21376932595656404268266963)
  ·
    refine ⟨32065398893484606402400445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21376932595656404268266963 32065398893484606402400445)
    ·
      refine ⟨12024524585056727400900167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32065398893484606402400445 12024524585056727400900167)
      ·
        refine ⟨18036786877585091101350251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12024524585056727400900167 18036786877585091101350251)
        ·
          refine ⟨27055180316377636652025377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18036786877585091101350251 27055180316377636652025377)
          ·
            refine ⟨20291385237283227489019033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27055180316377636652025377 20291385237283227489019033)
            ·
              refine ⟨15218538927962420616764275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20291385237283227489019033 15218538927962420616764275)
              ·
                refine ⟨22827808391943630925146413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15218538927962420616764275 22827808391943630925146413)
                ·
                  refine ⟨8560428146978861596929905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22827808391943630925146413 8560428146978861596929905)
                  ·
                    refine ⟨6420321110234146197697429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8560428146978861596929905 6420321110234146197697429)
                    ·
                      refine ⟨300952552042225603017067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6420321110234146197697429 300952552042225603017067)
                      ·
                        rfl

theorem cell23_586103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_586103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586103 prefixEnd_586103 := by exact prefixLift 586103
  have htrace : WordTrace (prefixWord ++ tailWord_586103) baseStart_586103 baseEnd_586103 := by
    simpa [prefixWord, tailWord_586103, baseEnd_586103] using wordTrace_append hprefix tailTrace_586103
  have hstable : (prefixWord ++ tailWord_586103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586103).length < 2 ^ (prefixWord ++ tailWord_586103).sum := by decide
  have hdescent : baseEnd_586103 < baseStart_586103 := by decide
  rcases family_descends (prefixWord ++ tailWord_586103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586137 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 4, 3, 2]
def baseStart_586137 : Nat := 118140960795 + 586137 * 2 ^ 59
def prefixEnd_586137 : Nat := 4983230072969 + 3 ^ 40 * 586137 * 2
def baseEnd_586137 : Nat := 300970010384478469991911

theorem tailTrace_586137 : CollatzResearch.WordTrace tailWord_586137 prefixEnd_586137 300970010384478469991911 := by
  unfold tailWord_586137
  simp only [CollatzResearch.WordTrace]
  refine ⟨21378172677533228075004665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14252115118355485383336443 21378172677533228075004665)
  ·
    refine ⟨16033629508149921056253499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21378172677533228075004665 16033629508149921056253499)
    ·
      refine ⟨24050444262224881584380249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16033629508149921056253499 24050444262224881584380249)
      ·
        refine ⟨18037833196668661188285187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24050444262224881584380249 18037833196668661188285187)
        ·
          refine ⟨27056749795002991782427781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18037833196668661188285187 27056749795002991782427781)
          ·
            refine ⟨5073140586563060959205209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27056749795002991782427781 5073140586563060959205209)
            ·
              refine ⟨3804855439922295719403907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5073140586563060959205209 3804855439922295719403907)
              ·
                refine ⟨5707283159883443579105861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3804855439922295719403907 5707283159883443579105861)
                ·
                  refine ⟨1070115592478145671082349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5707283159883443579105861 1070115592478145671082349)
                  ·
                    refine ⟨401293347179304626655881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1070115592478145671082349 401293347179304626655881)
                    ·
                      refine ⟨300970010384478469991911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 401293347179304626655881 300970010384478469991911)
                      ·
                        rfl

theorem cell23_586137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 3, 2].length) (baseStart_586137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586137 prefixEnd_586137 := by exact prefixLift 586137
  have htrace : WordTrace (prefixWord ++ tailWord_586137) baseStart_586137 baseEnd_586137 := by
    simpa [prefixWord, tailWord_586137, baseEnd_586137] using wordTrace_append hprefix tailTrace_586137
  have hstable : (prefixWord ++ tailWord_586137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586137).length < 2 ^ (prefixWord ++ tailWord_586137).sum := by decide
  have hdescent : baseEnd_586137 < baseStart_586137 := by decide
  rcases family_descends (prefixWord ++ tailWord_586137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586144 : List Nat := [2, 1, 1, 4, 1, 4, 2, 1, 3, 1, 3]
def baseStart_586144 : Nat := 118140960795 + 586144 * 2 ^ 59
def prefixEnd_586144 : Nat := 4983230072969 + 3 ^ 40 * 586144 * 2
def baseEnd_586144 : Nat := 300973604749059942604379

theorem tailTrace_586144 : CollatzResearch.WordTrace tailWord_586144 prefixEnd_586144 300973604749059942604379 := by
  unfold tailWord_586144
  simp only [CollatzResearch.WordTrace]
  refine ⟨10689213994253934135254743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14252285325671912180339657 10689213994253934135254743)
  ·
    refine ⟨16033820991380901202882115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10689213994253934135254743 16033820991380901202882115)
    ·
      refine ⟨24050731487071351804323173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16033820991380901202882115 24050731487071351804323173)
      ·
        refine ⟨4509512153825878463310595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24050731487071351804323173 4509512153825878463310595)
        ·
          refine ⟨6764268230738817694965893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4509512153825878463310595 6764268230738817694965893)
          ·
            refine ⟨1268300293263528317806105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6764268230738817694965893 1268300293263528317806105)
            ·
              refine ⟨951225219947646238354579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1268300293263528317806105 951225219947646238354579)
              ·
                refine ⟨1426837829921469357531869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 951225219947646238354579 1426837829921469357531869)
                ·
                  refine ⟨535064186220551009074451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1426837829921469357531869 535064186220551009074451)
                  ·
                    refine ⟨802596279330826513611677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 535064186220551009074451 802596279330826513611677)
                    ·
                      refine ⟨300973604749059942604379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 802596279330826513611677 300973604749059942604379)
                      ·
                        rfl

theorem cell23_586144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_586144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586144 prefixEnd_586144 := by exact prefixLift 586144
  have htrace : WordTrace (prefixWord ++ tailWord_586144) baseStart_586144 baseEnd_586144 := by
    simpa [prefixWord, tailWord_586144, baseEnd_586144] using wordTrace_append hprefix tailTrace_586144
  have hstable : (prefixWord ++ tailWord_586144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586144).length < 2 ^ (prefixWord ++ tailWord_586144).sum := by decide
  have hdescent : baseEnd_586144 < baseStart_586144 := by decide
  rcases family_descends (prefixWord ++ tailWord_586144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586167 : List Nat := [1, 1, 3, 1, 3, 3, 1, 4, 1, 1, 4]
def baseStart_586167 : Nat := 118140960795 + 586167 * 2 ^ 59
def prefixEnd_586167 : Nat := 4983230072969 + 3 ^ 40 * 586167 * 2
def baseEnd_586167 : Nat := 300985414804113352616773

theorem tailTrace_586167 : CollatzResearch.WordTrace tailWord_586167 prefixEnd_586167 300985414804113352616773 := by
  unfold tailWord_586167
  simp only [CollatzResearch.WordTrace]
  refine ⟨21379266867424543198596755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14252844578283028799064503 21379266867424543198596755)
  ·
    refine ⟨32068900301136814797895133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21379266867424543198596755 32068900301136814797895133)
    ·
      refine ⟨12025837612926305549210675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32068900301136814797895133 12025837612926305549210675)
      ·
        refine ⟨18038756419389458323816013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12025837612926305549210675 18038756419389458323816013)
        ·
          refine ⟨6764533657271046871431005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18038756419389458323816013 6764533657271046871431005)
          ·
            refine ⟨2536700121476642576786627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6764533657271046871431005 2536700121476642576786627)
            ·
              refine ⟨3805050182214963865179941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2536700121476642576786627 3805050182214963865179941)
              ·
                refine ⟨713446909165305724721239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3805050182214963865179941 713446909165305724721239)
                ·
                  refine ⟨1070170363747958587081859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 713446909165305724721239 1070170363747958587081859)
                  ·
                    refine ⟨1605255545621937880622789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1070170363747958587081859 1605255545621937880622789)
                    ·
                      refine ⟨300985414804113352616773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1605255545621937880622789 300985414804113352616773)
                      ·
                        rfl

theorem cell23_586167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 1, 4].length) (baseStart_586167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586167 prefixEnd_586167 := by exact prefixLift 586167
  have htrace : WordTrace (prefixWord ++ tailWord_586167) baseStart_586167 baseEnd_586167 := by
    simpa [prefixWord, tailWord_586167, baseEnd_586167] using wordTrace_append hprefix tailTrace_586167
  have hstable : (prefixWord ++ tailWord_586167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586167).length < 2 ^ (prefixWord ++ tailWord_586167).sum := by decide
  have hdescent : baseEnd_586167 < baseStart_586167 := by decide
  rcases family_descends (prefixWord ++ tailWord_586167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586170 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3]
def baseStart_586170 : Nat := 118140960795 + 586170 * 2 ^ 59
def prefixEnd_586170 : Nat := 4983230072969 + 3 ^ 40 * 586170 * 2
def baseEnd_586170 : Nat := 300986955246076840879259

theorem tailTrace_586170 : CollatzResearch.WordTrace tailWord_586170 prefixEnd_586170 300986955246076840879259 := by
  unfold tailWord_586170
  simp only [CollatzResearch.WordTrace]
  refine ⟨5344844071603418677738991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14252917524275783140637309 5344844071603418677738991)
  ·
    refine ⟨8017266107405128016608487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5344844071603418677738991 8017266107405128016608487)
    ·
      refine ⟨12025899161107692024912731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8017266107405128016608487 12025899161107692024912731)
      ·
        refine ⟨18038848741661538037369097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12025899161107692024912731 18038848741661538037369097)
        ·
          refine ⟨13529136556246153528026823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18038848741661538037369097 13529136556246153528026823)
          ·
            refine ⟨20293704834369230292040235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13529136556246153528026823 20293704834369230292040235)
            ·
              refine ⟨30440557251553845438060353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20293704834369230292040235 30440557251553845438060353)
              ·
                refine ⟨22830417938665384078545265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30440557251553845438060353 22830417938665384078545265)
                ·
                  refine ⟨17122813453999038058908949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22830417938665384078545265 17122813453999038058908949)
                  ·
                    refine ⟨802631880656204909011357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17122813453999038058908949 802631880656204909011357)
                    ·
                      refine ⟨300986955246076840879259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 802631880656204909011357 300986955246076840879259)
                      ·
                        rfl

theorem cell23_586170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3].length) (baseStart_586170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586170 prefixEnd_586170 := by exact prefixLift 586170
  have htrace : WordTrace (prefixWord ++ tailWord_586170) baseStart_586170 baseEnd_586170 := by
    simpa [prefixWord, tailWord_586170, baseEnd_586170] using wordTrace_append hprefix tailTrace_586170
  have hstable : (prefixWord ++ tailWord_586170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586170).length < 2 ^ (prefixWord ++ tailWord_586170).sum := by decide
  have hdescent : baseEnd_586170 < baseStart_586170 := by decide
  rcases family_descends (prefixWord ++ tailWord_586170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586217 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 6, 1, 3]
def baseStart_586217 : Nat := 118140960795 + 586217 * 2 ^ 59
def prefixEnd_586217 : Nat := 4983230072969 + 3 ^ 40 * 586217 * 2
def baseEnd_586217 : Nat := 301011088836838156991543

theorem tailTrace_586217 : CollatzResearch.WordTrace tailWord_586217 prefixEnd_586217 301011088836838156991543 := by
  unfold tailWord_586217
  simp only [CollatzResearch.WordTrace]
  refine ⟨21381090517243401737916905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14254060344828934491944603 21381090517243401737916905)
  ·
    refine ⟨16035817887932551303437679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21381090517243401737916905 16035817887932551303437679)
    ·
      refine ⟨24053726831898826955156519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16035817887932551303437679 24053726831898826955156519)
      ·
        refine ⟨36080590247848240432734779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24053726831898826955156519 36080590247848240432734779)
        ·
          refine ⟨54120885371772360649102169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36080590247848240432734779 54120885371772360649102169)
          ·
            refine ⟨40590664028829270486826627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54120885371772360649102169 40590664028829270486826627)
            ·
              refine ⟨60885996043243905730239941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40590664028829270486826627 60885996043243905730239941)
              ·
                refine ⟨11416124258108232324419989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60885996043243905730239941 11416124258108232324419989)
                ·
                  refine ⟨535130824598823390207187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11416124258108232324419989 535130824598823390207187)
                  ·
                    refine ⟨802696236898235085310781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 535130824598823390207187 802696236898235085310781)
                    ·
                      refine ⟨301011088836838156991543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 802696236898235085310781 301011088836838156991543)
                      ·
                        rfl

theorem cell23_586217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 1, 3].length) (baseStart_586217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586217 prefixEnd_586217 := by exact prefixLift 586217
  have htrace : WordTrace (prefixWord ++ tailWord_586217) baseStart_586217 baseEnd_586217 := by
    simpa [prefixWord, tailWord_586217, baseEnd_586217] using wordTrace_append hprefix tailTrace_586217
  have hstable : (prefixWord ++ tailWord_586217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586217).length < 2 ^ (prefixWord ++ tailWord_586217).sum := by decide
  have hdescent : baseEnd_586217 < baseStart_586217 := by decide
  rcases family_descends (prefixWord ++ tailWord_586217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586221 : List Nat := [1, 5, 1, 3, 1, 1, 3, 2, 1, 2, 3]
def baseStart_586221 : Nat := 118140960795 + 586221 * 2 ^ 59
def prefixEnd_586221 : Nat := 4983230072969 + 3 ^ 40 * 586221 * 2
def baseEnd_586221 : Nat := 301013142759456141341525

theorem tailTrace_586221 : CollatzResearch.WordTrace tailWord_586221 prefixEnd_586221 301013142759456141341525 := by
  unfold tailWord_586221
  simp only [CollatzResearch.WordTrace]
  refine ⟨21381236409228910421062517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14254157606152606947375011 21381236409228910421062517)
  ·
    refine ⟨2004490913365210351974611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21381236409228910421062517 2004490913365210351974611)
    ·
      refine ⟨3006736370047815527961917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2004490913365210351974611 3006736370047815527961917)
      ·
        refine ⟨1127526138767930822985719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3006736370047815527961917 1127526138767930822985719)
        ·
          refine ⟨1691289208151896234478579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1127526138767930822985719 1691289208151896234478579)
          ·
            refine ⟨2536933812227844351717869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1691289208151896234478579 2536933812227844351717869)
            ·
              refine ⟨951350179585441631894201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2536933812227844351717869 951350179585441631894201)
              ·
                refine ⟨713512634689081223920651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 951350179585441631894201 713512634689081223920651)
                ·
                  refine ⟨1070268952033621835880977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 713512634689081223920651 1070268952033621835880977)
                  ·
                    refine ⟨802701714025216376910733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1070268952033621835880977 802701714025216376910733)
                    ·
                      refine ⟨301013142759456141341525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 802701714025216376910733 301013142759456141341525)
                      ·
                        rfl

theorem cell23_586221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_586221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586221 prefixEnd_586221 := by exact prefixLift 586221
  have htrace : WordTrace (prefixWord ++ tailWord_586221) baseStart_586221 baseEnd_586221 := by
    simpa [prefixWord, tailWord_586221, baseEnd_586221] using wordTrace_append hprefix tailTrace_586221
  have hstable : (prefixWord ++ tailWord_586221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586221).length < 2 ^ (prefixWord ++ tailWord_586221).sum := by decide
  have hdescent : baseEnd_586221 < baseStart_586221 := by decide
  rcases family_descends (prefixWord ++ tailWord_586221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586240 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 4]
def baseStart_586240 : Nat := 118140960795 + 586240 * 2 ^ 59
def prefixEnd_586240 : Nat := 4983230072969 + 3 ^ 40 * 586240 * 2
def baseEnd_586240 : Nat := 301022898891891567003937

theorem tailTrace_586240 : CollatzResearch.WordTrace tailWord_586240 prefixEnd_586240 301022898891891567003937 := by
  unfold tailWord_586240
  simp only [CollatzResearch.WordTrace]
  refine ⟨10690964698080038333002087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14254619597440051110669449 10690964698080038333002087)
  ·
    refine ⟨16036447047120057499503131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10690964698080038333002087 16036447047120057499503131)
    ·
      refine ⟨24054670570680086249254697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16036447047120057499503131 24054670570680086249254697)
      ·
        refine ⟨18041002928010064686941023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24054670570680086249254697 18041002928010064686941023)
        ·
          refine ⟨27061504392015097030411535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18041002928010064686941023 27061504392015097030411535)
          ·
            refine ⟨40592256588022645545617303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27061504392015097030411535 40592256588022645545617303)
            ·
              refine ⟨60888384882033968318425955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40592256588022645545617303 60888384882033968318425955)
              ·
                refine ⟨91332577323050952477638933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60888384882033968318425955 91332577323050952477638933)
                ·
                  refine ⟨4281214562018013397389325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91332577323050952477638933 4281214562018013397389325)
                  ·
                    refine ⟨1605455460756755024020997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4281214562018013397389325 1605455460756755024020997)
                    ·
                      refine ⟨301022898891891567003937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1605455460756755024020997 301022898891891567003937)
                      ·
                        rfl

theorem cell23_586240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_586240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586240 prefixEnd_586240 := by exact prefixLift 586240
  have htrace : WordTrace (prefixWord ++ tailWord_586240) baseStart_586240 baseEnd_586240 := by
    simpa [prefixWord, tailWord_586240, baseEnd_586240] using wordTrace_append hprefix tailTrace_586240
  have hstable : (prefixWord ++ tailWord_586240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586240).length < 2 ^ (prefixWord ++ tailWord_586240).sum := by decide
  have hdescent : baseEnd_586240 < baseStart_586240 := by decide
  rcases family_descends (prefixWord ++ tailWord_586240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586251 : List Nat := [1, 1, 1, 1, 7, 2, 2, 2, 2, 1, 3]
def baseStart_586251 : Nat := 118140960795 + 586251 * 2 ^ 59
def prefixEnd_586251 : Nat := 4983230072969 + 3 ^ 40 * 586251 * 2
def baseEnd_586251 : Nat := 301028547179091023966387

theorem tailTrace_586251 : CollatzResearch.WordTrace tailWord_586251 prefixEnd_586251 301028547179091023966387 := by
  unfold tailWord_586251
  simp only [CollatzResearch.WordTrace]
  refine ⟨21382330599120225544654607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14254887066080150363103071 21382330599120225544654607)
  ·
    refine ⟨32073495898680338316981911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21382330599120225544654607 32073495898680338316981911)
    ·
      refine ⟨48110243848020507475472867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32073495898680338316981911 48110243848020507475472867)
      ·
        refine ⟨72165365772030761213209301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48110243848020507475472867 72165365772030761213209301)
        ·
          refine ⟨1691375760281970965934593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 72165365772030761213209301 1691375760281970965934593)
          ·
            refine ⟨1268531820211478224450945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1691375760281970965934593 1268531820211478224450945)
            ·
              refine ⟨951398865158608668338209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1268531820211478224450945 951398865158608668338209)
              ·
                refine ⟨713549148868956501253657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 951398865158608668338209 713549148868956501253657)
                ·
                  refine ⟨535161861651717375940243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 713549148868956501253657 535161861651717375940243)
                  ·
                    refine ⟨802742792477576063910365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 535161861651717375940243 802742792477576063910365)
                    ·
                      refine ⟨301028547179091023966387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 802742792477576063910365 301028547179091023966387)
                      ·
                        rfl

theorem cell23_586251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 1, 3].length) (baseStart_586251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586251 prefixEnd_586251 := by exact prefixLift 586251
  have htrace : WordTrace (prefixWord ++ tailWord_586251) baseStart_586251 baseEnd_586251 := by
    simpa [prefixWord, tailWord_586251, baseEnd_586251] using wordTrace_append hprefix tailTrace_586251
  have hstable : (prefixWord ++ tailWord_586251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586251).length < 2 ^ (prefixWord ++ tailWord_586251).sum := by decide
  have hdescent : baseEnd_586251 < baseStart_586251 := by decide
  rcases family_descends (prefixWord ++ tailWord_586251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586302 : List Nat := [4, 2, 1, 4, 2, 1, 1, 2, 2, 1, 3]
def baseStart_586302 : Nat := 118140960795 + 586302 * 2 ^ 59
def prefixEnd_586302 : Nat := 4983230072969 + 3 ^ 40 * 586302 * 2
def baseEnd_586302 : Nat := 301054734692470324428653

theorem tailTrace_586302 : CollatzResearch.WordTrace tailWord_586302 prefixEnd_586302 301054734692470324428653 := by
  unfold tailWord_586302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2673023840241932656845145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14256127147956974169840773 2673023840241932656845145)
  ·
    refine ⟨2004767880181449492633859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2673023840241932656845145 2004767880181449492633859)
    ·
      refine ⟨3007151820272174238950789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2004767880181449492633859 3007151820272174238950789)
      ·
        refine ⟨563840966301032669803273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3007151820272174238950789 563840966301032669803273)
        ·
          refine ⟨422880724725774502352455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 563840966301032669803273 422880724725774502352455)
          ·
            refine ⟨634321087088661753528683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422880724725774502352455 634321087088661753528683)
            ·
              refine ⟨951481630632992630293025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634321087088661753528683 951481630632992630293025)
              ·
                refine ⟨713611222974744472719769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 951481630632992630293025 713611222974744472719769)
                ·
                  refine ⟨535208417231058354539827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 713611222974744472719769 535208417231058354539827)
                  ·
                    refine ⟨802812625846587531809741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 535208417231058354539827 802812625846587531809741)
                    ·
                      refine ⟨301054734692470324428653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 802812625846587531809741 301054734692470324428653)
                      ·
                        rfl

theorem cell23_586302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_586302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586302 prefixEnd_586302 := by exact prefixLift 586302
  have htrace : WordTrace (prefixWord ++ tailWord_586302) baseStart_586302 baseEnd_586302 := by
    simpa [prefixWord, tailWord_586302, baseEnd_586302] using wordTrace_append hprefix tailTrace_586302
  have hstable : (prefixWord ++ tailWord_586302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586302).length < 2 ^ (prefixWord ++ tailWord_586302).sum := by decide
  have hdescent : baseEnd_586302 < baseStart_586302 := by decide
  rcases family_descends (prefixWord ++ tailWord_586302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586314 : List Nat := [3, 1, 2, 1, 1, 4, 2, 4, 5]
def baseStart_586314 : Nat := 118140960795 + 586314 * 2 ^ 59
def prefixEnd_586314 : Nat := 4983230072969 + 3 ^ 40 * 586314 * 2
def baseEnd_586314 : Nat := 33451210717813808608733

theorem tailTrace_586314 : CollatzResearch.WordTrace tailWord_586314 prefixEnd_586314 33451210717813808608733 := by
  unfold tailWord_586314
  simp only [CollatzResearch.WordTrace]
  refine ⟨5346157099472996826049499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14256418931927991536131997 5346157099472996826049499)
  ·
    refine ⟨8019235649209495239074249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5346157099472996826049499 8019235649209495239074249)
    ·
      refine ⟨6014426736907121429305687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8019235649209495239074249 6014426736907121429305687)
      ·
        refine ⟨9021640105360682143958531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6014426736907121429305687 9021640105360682143958531)
        ·
          refine ⟨13532460158041023215937797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9021640105360682143958531 13532460158041023215937797)
          ·
            refine ⟨2537336279632691852988337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13532460158041023215937797 2537336279632691852988337)
            ·
              refine ⟨1903002209724518889741253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2537336279632691852988337 1903002209724518889741253)
              ·
                refine ⟨356812914323347291826485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1903002209724518889741253 356812914323347291826485)
                ·
                  refine ⟨33451210717813808608733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 356812914323347291826485 33451210717813808608733)
                  ·
                    rfl

theorem cell23_586314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 5].length) (baseStart_586314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586314 prefixEnd_586314 := by exact prefixLift 586314
  have htrace : WordTrace (prefixWord ++ tailWord_586314) baseStart_586314 baseEnd_586314 := by
    simpa [prefixWord, tailWord_586314, baseEnd_586314] using wordTrace_append hprefix tailTrace_586314
  have hstable : (prefixWord ++ tailWord_586314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586314).length < 2 ^ (prefixWord ++ tailWord_586314).sum := by decide
  have hdescent : baseEnd_586314 < baseStart_586314 := by decide
  rcases family_descends (prefixWord ++ tailWord_586314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586324 : List Nat := [2, 4, 1, 1, 1, 3, 2, 1, 2, 3, 3]
def baseStart_586324 : Nat := 118140960795 + 586324 * 2 ^ 59
def prefixEnd_586324 : Nat := 4983230072969 + 3 ^ 40 * 586324 * 2
def baseEnd_586324 : Nat := 301066031266869238353551

theorem tailTrace_586324 : CollatzResearch.WordTrace tailWord_586324 prefixEnd_586324 301066031266869238353551 := by
  unfold tailWord_586324
  simp only [CollatzResearch.WordTrace]
  refine ⟨10692496563927879506031013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14256662085237172674708017 10692496563927879506031013)
  ·
    refine ⟨2004843105736477407380815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10692496563927879506031013 2004843105736477407380815)
    ·
      refine ⟨3007264658604716111071223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2004843105736477407380815 3007264658604716111071223)
      ·
        refine ⟨4510896987907074166606835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3007264658604716111071223 4510896987907074166606835)
        ·
          refine ⟨6766345481860611249910253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4510896987907074166606835 6766345481860611249910253)
          ·
            refine ⟨2537379555697729218716345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6766345481860611249910253 2537379555697729218716345)
            ·
              refine ⟨1903034666773296914037259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2537379555697729218716345 1903034666773296914037259)
              ·
                refine ⟨2854552000159945371055889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1903034666773296914037259 2854552000159945371055889)
                ·
                  refine ⟨2140914000119959028291917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2854552000159945371055889 2140914000119959028291917)
                  ·
                    refine ⟨802842750044984635609469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2140914000119959028291917 802842750044984635609469)
                    ·
                      refine ⟨301066031266869238353551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 802842750044984635609469 301066031266869238353551)
                      ·
                        rfl

theorem cell23_586324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_586324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586324 prefixEnd_586324 := by exact prefixLift 586324
  have htrace : WordTrace (prefixWord ++ tailWord_586324) baseStart_586324 baseEnd_586324 := by
    simpa [prefixWord, tailWord_586324, baseEnd_586324] using wordTrace_append hprefix tailTrace_586324
  have hstable : (prefixWord ++ tailWord_586324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586324).length < 2 ^ (prefixWord ++ tailWord_586324).sum := by decide
  have hdescent : baseEnd_586324 < baseStart_586324 := by decide
  rcases family_descends (prefixWord ++ tailWord_586324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586364 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 4, 4, 2]
def baseStart_586364 : Nat := 118140960795 + 586364 * 2 ^ 59
def prefixEnd_586364 : Nat := 4983230072969 + 3 ^ 40 * 586364 * 2
def baseEnd_586364 : Nat := 301086570493049081853367

theorem tailTrace_586364 : CollatzResearch.WordTrace tailWord_586364 prefixEnd_586364 301086570493049081853367 := by
  unfold tailWord_586364
  simp only [CollatzResearch.WordTrace]
  refine ⟨10693226023855422921759073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14257634698473897229012097 10693226023855422921759073)
  ·
    refine ⟨8019919517891567191319305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10693226023855422921759073 8019919517891567191319305)
    ·
      refine ⟨6014939638418675393489479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8019919517891567191319305 6014939638418675393489479)
      ·
        refine ⟨9022409457628013090234219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6014939638418675393489479 9022409457628013090234219)
        ·
          refine ⟨13533614186442019635351329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9022409457628013090234219 13533614186442019635351329)
          ·
            refine ⟨10150210639831514726513497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13533614186442019635351329 10150210639831514726513497)
            ·
              refine ⟨7612657979873636044885123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10150210639831514726513497 7612657979873636044885123)
              ·
                refine ⟨11418986969810454067327685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7612657979873636044885123 11418986969810454067327685)
                ·
                  refine ⟨2141060056839460137623941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11418986969810454067327685 2141060056839460137623941)
                  ·
                    refine ⟨401448760657398775804489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2141060056839460137623941 401448760657398775804489)
                    ·
                      refine ⟨301086570493049081853367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 401448760657398775804489 301086570493049081853367)
                      ·
                        rfl

theorem cell23_586364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 4, 4, 2].length) (baseStart_586364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586364 prefixEnd_586364 := by exact prefixLift 586364
  have htrace : WordTrace (prefixWord ++ tailWord_586364) baseStart_586364 baseEnd_586364 := by
    simpa [prefixWord, tailWord_586364, baseEnd_586364] using wordTrace_append hprefix tailTrace_586364
  have hstable : (prefixWord ++ tailWord_586364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586364).length < 2 ^ (prefixWord ++ tailWord_586364).sum := by decide
  have hdescent : baseEnd_586364 < baseStart_586364 := by decide
  rcases family_descends (prefixWord ++ tailWord_586364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586367 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 3]
def baseStart_586367 : Nat := 118140960795 + 586367 * 2 ^ 59
def prefixEnd_586367 : Nat := 4983230072969 + 3 ^ 40 * 586367 * 2
def baseEnd_586367 : Nat := 301088110935012570115853

theorem tailTrace_586367 : CollatzResearch.WordTrace tailWord_586367 prefixEnd_586367 301088110935012570115853 := by
  unfold tailWord_586367
  simp only [CollatzResearch.WordTrace]
  refine ⟨21386561466699977355877355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14257707644466651570584903 21386561466699977355877355)
  ·
    refine ⟨32079842200049966033816033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21386561466699977355877355 32079842200049966033816033)
    ·
      refine ⟨24059881650037474525362025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32079842200049966033816033 24059881650037474525362025)
      ·
        refine ⟨18044911237528105894021519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24059881650037474525362025 18044911237528105894021519)
        ·
          refine ⟨27067366856292158841032279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18044911237528105894021519 27067366856292158841032279)
          ·
            refine ⟨40601050284438238261548419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27067366856292158841032279 40601050284438238261548419)
            ·
              refine ⟨60901575426657357392322629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40601050284438238261548419 60901575426657357392322629)
              ·
                refine ⟨11419045392498254511060493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60901575426657357392322629 11419045392498254511060493)
                ·
                  refine ⟨4282142022186845441647685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11419045392498254511060493 4282142022186845441647685)
                  ·
                    refine ⟨802901629160033520308941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4282142022186845441647685 802901629160033520308941)
                    ·
                      refine ⟨301088110935012570115853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 802901629160033520308941 301088110935012570115853)
                      ·
                        rfl

theorem cell23_586367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 3].length) (baseStart_586367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586367 prefixEnd_586367 := by exact prefixLift 586367
  have htrace : WordTrace (prefixWord ++ tailWord_586367) baseStart_586367 baseEnd_586367 := by
    simpa [prefixWord, tailWord_586367, baseEnd_586367] using wordTrace_append hprefix tailTrace_586367
  have hstable : (prefixWord ++ tailWord_586367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586367).length < 2 ^ (prefixWord ++ tailWord_586367).sum := by decide
  have hdescent : baseEnd_586367 < baseStart_586367 := by decide
  rcases family_descends (prefixWord ++ tailWord_586367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586387 : List Nat := [1, 1, 1, 2, 1, 2, 2, 7, 6]
def baseStart_586387 : Nat := 118140960795 + 586387 * 2 ^ 59
def prefixEnd_586387 : Nat := 4983230072969 + 3 ^ 40 * 586387 * 2
def baseEnd_586387 : Nat := 33455375616455832429529

theorem tailTrace_586387 : CollatzResearch.WordTrace tailWord_586387 prefixEnd_586387 33455375616455832429529 := by
  unfold tailWord_586387
  simp only [CollatzResearch.WordTrace]
  refine ⟨21387290926627520771605415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14258193951085013847736943 21387290926627520771605415)
  ·
    refine ⟨32080936389941281157408123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21387290926627520771605415 32080936389941281157408123)
    ·
      refine ⟨48121404584911921736112185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32080936389941281157408123 48121404584911921736112185)
      ·
        refine ⟨36091053438683941302084139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48121404584911921736112185 36091053438683941302084139)
        ·
          refine ⟨54136580158025911953126209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36091053438683941302084139 54136580158025911953126209)
          ·
            refine ⟨40602435118519433964844657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54136580158025911953126209 40602435118519433964844657)
            ·
              refine ⟨30451826338889575473633493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40602435118519433964844657 30451826338889575473633493)
              ·
                refine ⟨713714679817724425163285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 30451826338889575473633493 713714679817724425163285)
                ·
                  refine ⟨33455375616455832429529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 713714679817724425163285 33455375616455832429529)
                  ·
                    rfl

theorem cell23_586387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 6].length) (baseStart_586387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586387 prefixEnd_586387 := by exact prefixLift 586387
  have htrace : WordTrace (prefixWord ++ tailWord_586387) baseStart_586387 baseEnd_586387 := by
    simpa [prefixWord, tailWord_586387, baseEnd_586387] using wordTrace_append hprefix tailTrace_586387
  have hstable : (prefixWord ++ tailWord_586387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586387).length < 2 ^ (prefixWord ++ tailWord_586387).sum := by decide
  have hdescent : baseEnd_586387 < baseStart_586387 := by decide
  rcases family_descends (prefixWord ++ tailWord_586387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586421 : List Nat := [1, 3, 3, 3, 1, 2, 2, 2, 6]
def baseStart_586421 : Nat := 118140960795 + 586421 * 2 ^ 59
def prefixEnd_586421 : Nat := 4983230072969 + 3 ^ 40 * 586421 * 2
def baseEnd_586421 : Nat := 33457315432261706537845

theorem tailTrace_586421 : CollatzResearch.WordTrace tailWord_586421 prefixEnd_586421 33457315432261706537845 := by
  unfold tailWord_586421
  simp only [CollatzResearch.WordTrace]
  refine ⟨21388531008504344578343117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14259020672336229718895411 21388531008504344578343117)
  ·
    refine ⟨8020699128189129216878669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21388531008504344578343117 8020699128189129216878669)
    ·
      refine ⟨3007762173070923456329501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8020699128189129216878669 3007762173070923456329501)
      ·
        refine ⟨1127910814901596296123563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3007762173070923456329501 1127910814901596296123563)
        ·
          refine ⟨1691866222352394444185345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1127910814901596296123563 1691866222352394444185345)
          ·
            refine ⟨1268899666764295833139009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1691866222352394444185345 1268899666764295833139009)
            ·
              refine ⟨951674750073221874854257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1268899666764295833139009 951674750073221874854257)
              ·
                refine ⟨713756062554916406140693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 951674750073221874854257 713756062554916406140693)
                ·
                  refine ⟨33457315432261706537845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 713756062554916406140693 33457315432261706537845)
                  ·
                    rfl

theorem cell23_586421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 6].length) (baseStart_586421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586421 prefixEnd_586421 := by exact prefixLift 586421
  have htrace : WordTrace (prefixWord ++ tailWord_586421) baseStart_586421 baseEnd_586421 := by
    simpa [prefixWord, tailWord_586421, baseEnd_586421] using wordTrace_append hprefix tailTrace_586421
  have hstable : (prefixWord ++ tailWord_586421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586421).length < 2 ^ (prefixWord ++ tailWord_586421).sum := by decide
  have hdescent : baseEnd_586421 < baseStart_586421 := by decide
  rcases family_descends (prefixWord ++ tailWord_586421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586424 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 5, 5, 2]
def baseStart_586424 : Nat := 118140960795 + 586424 * 2 ^ 59
def prefixEnd_586424 : Nat := 4983230072969 + 3 ^ 40 * 586424 * 2
def baseEnd_586424 : Nat := 301117379332318847103091

theorem tailTrace_586424 : CollatzResearch.WordTrace tailWord_586424 prefixEnd_586424 301117379332318847103091 := by
  unfold tailWord_586424
  simp only [CollatzResearch.WordTrace]
  refine ⟨10694320213746738045351163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14259093618328984060468217 10694320213746738045351163)
  ·
    refine ⟨16041480320620107068026745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10694320213746738045351163 16041480320620107068026745)
    ·
      refine ⟨12031110240465080301020059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16041480320620107068026745 12031110240465080301020059)
      ·
        refine ⟨18046665360697620451530089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12031110240465080301020059 18046665360697620451530089)
        ·
          refine ⟨13534999020523215338647567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18046665360697620451530089 13534999020523215338647567)
          ·
            refine ⟨20302498530784823007971351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13534999020523215338647567 20302498530784823007971351)
            ·
              refine ⟨30453747796177234511957027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20302498530784823007971351 30453747796177234511957027)
              ·
                refine ⟨45680621694265851767935541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30453747796177234511957027 45680621694265851767935541)
                ·
                  refine ⟨4282558283837423603243957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45680621694265851767935541 4282558283837423603243957)
                  ·
                    refine ⟨401489839109758462804121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4282558283837423603243957 401489839109758462804121)
                    ·
                      refine ⟨301117379332318847103091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 401489839109758462804121 301117379332318847103091)
                      ·
                        rfl

theorem cell23_586424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 5, 5, 2].length) (baseStart_586424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586424 prefixEnd_586424 := by exact prefixLift 586424
  have htrace : WordTrace (prefixWord ++ tailWord_586424) baseStart_586424 baseEnd_586424 := by
    simpa [prefixWord, tailWord_586424, baseEnd_586424] using wordTrace_append hprefix tailTrace_586424
  have hstable : (prefixWord ++ tailWord_586424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586424).length < 2 ^ (prefixWord ++ tailWord_586424).sum := by decide
  have hdescent : baseEnd_586424 < baseStart_586424 := by decide
  rcases family_descends (prefixWord ++ tailWord_586424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586437 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 1, 7, 4]
def baseStart_586437 : Nat := 118140960795 + 586437 * 2 ^ 59
def prefixEnd_586437 : Nat := 4983230072969 + 3 ^ 40 * 586437 * 2
def baseEnd_586437 : Nat := 301124054580827296240531

theorem tailTrace_586437 : CollatzResearch.WordTrace tailWord_586437 prefixEnd_586437 301124054580827296240531 := by
  unfold tailWord_586437
  simp only [CollatzResearch.WordTrace]
  refine ⟨21389114576446379310925565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14259409717630919540617043 21389114576446379310925565)
  ·
    refine ⟨8020917966167392241597087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21389114576446379310925565 8020917966167392241597087)
    ·
      refine ⟨12031376949251088362395631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8020917966167392241597087 12031376949251088362395631)
      ·
        refine ⟨18047065423876632543593447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12031376949251088362395631 18047065423876632543593447)
        ·
          refine ⟨27070598135814948815390171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18047065423876632543593447 27070598135814948815390171)
          ·
            refine ⟨40605897203722423223085257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27070598135814948815390171 40605897203722423223085257)
            ·
              refine ⟨30454422902791817417313943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40605897203722423223085257 30454422902791817417313943)
              ·
                refine ⟨45681634354187726125970915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30454422902791817417313943 45681634354187726125970915)
                ·
                  refine ⟨68522451531281589188956373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45681634354187726125970915 68522451531281589188956373)
                  ·
                    refine ⟨1605994957764412246616165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 68522451531281589188956373 1605994957764412246616165)
                    ·
                      refine ⟨301124054580827296240531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1605994957764412246616165 301124054580827296240531)
                      ·
                        rfl

theorem cell23_586437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_586437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586437 prefixEnd_586437 := by exact prefixLift 586437
  have htrace : WordTrace (prefixWord ++ tailWord_586437) baseStart_586437 baseEnd_586437 := by
    simpa [prefixWord, tailWord_586437, baseEnd_586437] using wordTrace_append hprefix tailTrace_586437
  have hstable : (prefixWord ++ tailWord_586437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586437).length < 2 ^ (prefixWord ++ tailWord_586437).sum := by decide
  have hdescent : baseEnd_586437 < baseStart_586437 := by decide
  rcases family_descends (prefixWord ++ tailWord_586437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586464 : List Nat := [2, 1, 1, 3, 1, 2, 1, 4, 4, 4]
def baseStart_586464 : Nat := 118140960795 + 586464 * 2 ^ 59
def prefixEnd_586464 : Nat := 4983230072969 + 3 ^ 40 * 586464 * 2
def baseEnd_586464 : Nat := 100379306186166230200969

theorem tailTrace_586464 : CollatzResearch.WordTrace tailWord_586464 prefixEnd_586464 100379306186166230200969 := by
  unfold tailWord_586464
  simp only [CollatzResearch.WordTrace]
  refine ⟨10695049673674281461079223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14260066231565708614772297 10695049673674281461079223)
  ·
    refine ⟨16042574510511422191618835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10695049673674281461079223 16042574510511422191618835)
    ·
      refine ⟨24063861765767133287428253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16042574510511422191618835 24063861765767133287428253)
      ·
        refine ⟨9023948162162674982785595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24063861765767133287428253 9023948162162674982785595)
        ·
          refine ⟨13535922243244012474178393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9023948162162674982785595 13535922243244012474178393)
          ·
            refine ⟨10151941682433009355633795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13535922243244012474178393 10151941682433009355633795)
            ·
              refine ⟨15227912523649514033450693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10151941682433009355633795 15227912523649514033450693)
              ·
                refine ⟨2855233598184283881272005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15227912523649514033450693 2855233598184283881272005)
                ·
                  refine ⟨535356299659553227738501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2855233598184283881272005 535356299659553227738501)
                  ·
                    refine ⟨100379306186166230200969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 535356299659553227738501 100379306186166230200969)
                    ·
                      rfl

theorem cell23_586464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 4, 4].length) (baseStart_586464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586464 prefixEnd_586464 := by exact prefixLift 586464
  have htrace : WordTrace (prefixWord ++ tailWord_586464) baseStart_586464 baseEnd_586464 := by
    simpa [prefixWord, tailWord_586464, baseEnd_586464] using wordTrace_append hprefix tailTrace_586464
  have hstable : (prefixWord ++ tailWord_586464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586464).length < 2 ^ (prefixWord ++ tailWord_586464).sum := by decide
  have hdescent : baseEnd_586464 < baseStart_586464 := by decide
  rcases family_descends (prefixWord ++ tailWord_586464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586465 : List Nat := [1, 2, 3, 1, 4, 2, 2, 3, 1, 1, 3]
def baseStart_586465 : Nat := 118140960795 + 586465 * 2 ^ 59
def prefixEnd_586465 : Nat := 4983230072969 + 3 ^ 40 * 586465 * 2
def baseEnd_586465 : Nat := 301138432039153186690403

theorem tailTrace_586465 : CollatzResearch.WordTrace tailWord_586465 prefixEnd_586465 301138432039153186690403 := by
  unfold tailWord_586465
  simp only [CollatzResearch.WordTrace]
  refine ⟨21390135820344940092944849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14260090546896626728629899 21390135820344940092944849)
  ·
    refine ⟨16042601865258705069708637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21390135820344940092944849 16042601865258705069708637)
    ·
      refine ⟨6015975699472014401140739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16042601865258705069708637 6015975699472014401140739)
      ·
        refine ⟨9023963549208021601711109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6015975699472014401140739 9023963549208021601711109)
        ·
          refine ⟨1691993165476504050320833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9023963549208021601711109 1691993165476504050320833)
          ·
            refine ⟨1268994874107378037740625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1691993165476504050320833 1268994874107378037740625)
            ·
              refine ⟨951746155580533528305469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1268994874107378037740625 951746155580533528305469)
              ·
                refine ⟨356904808342700073114551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 951746155580533528305469 356904808342700073114551)
                ·
                  refine ⟨535357212514050109671827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 356904808342700073114551 535357212514050109671827)
                  ·
                    refine ⟨803035818771075164507741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 535357212514050109671827 803035818771075164507741)
                    ·
                      refine ⟨301138432039153186690403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 803035818771075164507741 301138432039153186690403)
                      ·
                        rfl

theorem cell23_586465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 1, 1, 3].length) (baseStart_586465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586465 prefixEnd_586465 := by exact prefixLift 586465
  have htrace : WordTrace (prefixWord ++ tailWord_586465) baseStart_586465 baseEnd_586465 := by
    simpa [prefixWord, tailWord_586465, baseEnd_586465] using wordTrace_append hprefix tailTrace_586465
  have hstable : (prefixWord ++ tailWord_586465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586465).length < 2 ^ (prefixWord ++ tailWord_586465).sum := by decide
  have hdescent : baseEnd_586465 < baseStart_586465 := by decide
  rcases family_descends (prefixWord ++ tailWord_586465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586468 : List Nat := [2, 3, 1, 1, 1, 6, 2, 1, 1, 5]
def baseStart_586468 : Nat := 118140960795 + 586468 * 2 ^ 59
def prefixEnd_586468 : Nat := 4983230072969 + 3 ^ 40 * 586468 * 2
def baseEnd_586468 : Nat := 100379990827038891650963

theorem tailTrace_586468 : CollatzResearch.WordTrace tailWord_586468 prefixEnd_586468 100379990827038891650963 := by
  unfold tailWord_586468
  simp only [CollatzResearch.WordTrace]
  refine ⟨10695122619667035802652029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14260163492889381070202705 10695122619667035802652029)
  ·
    refine ⟨4010670982375138425994511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10695122619667035802652029 4010670982375138425994511)
    ·
      refine ⟨6016006473562707638991767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4010670982375138425994511 6016006473562707638991767)
      ·
        refine ⟨9024009710344061458487651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6016006473562707638991767 9024009710344061458487651)
        ·
          refine ⟨13536014565516092187731477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9024009710344061458487651 13536014565516092187731477)
          ·
            refine ⟨634500682758566821299913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13536014565516092187731477 634500682758566821299913)
            ·
              refine ⟨475875512068925115974935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 634500682758566821299913 475875512068925115974935)
              ·
                refine ⟨713813268103387673962403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 475875512068925115974935 713813268103387673962403)
                ·
                  refine ⟨1070719902155081510943605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 713813268103387673962403 1070719902155081510943605)
                  ·
                    refine ⟨100379990827038891650963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1070719902155081510943605 100379990827038891650963)
                    ·
                      rfl

theorem cell23_586468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_586468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586468 prefixEnd_586468 := by exact prefixLift 586468
  have htrace : WordTrace (prefixWord ++ tailWord_586468) baseStart_586468 baseEnd_586468 := by
    simpa [prefixWord, tailWord_586468, baseEnd_586468] using wordTrace_append hprefix tailTrace_586468
  have hstable : (prefixWord ++ tailWord_586468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586468).length < 2 ^ (prefixWord ++ tailWord_586468).sum := by decide
  have hdescent : baseEnd_586468 < baseStart_586468 := by decide
  rcases family_descends (prefixWord ++ tailWord_586468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586474 : List Nat := [3, 1, 3, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_586474 : Nat := 118140960795 + 586474 * 2 ^ 59
def prefixEnd_586474 : Nat := 4983230072969 + 3 ^ 40 * 586474 * 2
def baseEnd_586474 : Nat := 301143053365043651477861

theorem tailTrace_586474 : CollatzResearch.WordTrace tailWord_586474 prefixEnd_586474 301143053365043651477861 := by
  unfold tailWord_586474
  simp only [CollatzResearch.WordTrace]
  refine ⟨5347616019328083657505619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14260309384874889753348317 5347616019328083657505619)
  ·
    refine ⟨8021424028992125486258429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5347616019328083657505619 8021424028992125486258429)
    ·
      refine ⟨3008034010872047057346911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8021424028992125486258429 3008034010872047057346911)
      ·
        refine ⟨4512051016308070586020367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3008034010872047057346911 4512051016308070586020367)
        ·
          refine ⟨6768076524462105879030551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4512051016308070586020367 6768076524462105879030551)
          ·
            refine ⟨10152114786693158818545827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6768076524462105879030551 10152114786693158818545827)
            ·
              refine ⟨15228172180039738227818741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10152114786693158818545827 15228172180039738227818741)
              ·
                refine ⟨1427641141878725458858007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15228172180039738227818741 1427641141878725458858007)
                ·
                  refine ⟨2141461712818088188287011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1427641141878725458858007 2141461712818088188287011)
                  ·
                    refine ⟨3212192569227132282430517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2141461712818088188287011 3212192569227132282430517)
                    ·
                      refine ⟨301143053365043651477861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3212192569227132282430517 301143053365043651477861)
                      ·
                        rfl

theorem cell23_586474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_586474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586474 prefixEnd_586474 := by exact prefixLift 586474
  have htrace : WordTrace (prefixWord ++ tailWord_586474) baseStart_586474 baseEnd_586474 := by
    simpa [prefixWord, tailWord_586474, baseEnd_586474] using wordTrace_append hprefix tailTrace_586474
  have hstable : (prefixWord ++ tailWord_586474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586474).length < 2 ^ (prefixWord ++ tailWord_586474).sum := by decide
  have hdescent : baseEnd_586474 < baseStart_586474 := by decide
  rcases family_descends (prefixWord ++ tailWord_586474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586487 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 7]
def baseStart_586487 : Nat := 118140960795 + 586487 * 2 ^ 59
def prefixEnd_586487 : Nat := 4983230072969 + 3 ^ 40 * 586487 * 2
def baseEnd_586487 : Nat := 301149728613552100615301

theorem tailTrace_586487 : CollatzResearch.WordTrace tailWord_586487 prefixEnd_586487 301149728613552100615301 := by
  unfold tailWord_586487
  simp only [CollatzResearch.WordTrace]
  refine ⟨21390938226265237850245715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14260625484176825233497143 21390938226265237850245715)
  ·
    refine ⟨32086407339397856775368573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21390938226265237850245715 32086407339397856775368573)
    ·
      refine ⟨12032402752274196290763215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32086407339397856775368573 12032402752274196290763215)
      ·
        refine ⟨18048604128411294436144823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12032402752274196290763215 18048604128411294436144823)
        ·
          refine ⟨27072906192616941654217235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18048604128411294436144823 27072906192616941654217235)
          ·
            refine ⟨40609359288925412481325853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27072906192616941654217235 40609359288925412481325853)
            ·
              refine ⟨15228509733347029680497195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40609359288925412481325853 15228509733347029680497195)
              ·
                refine ⟨22842764600020544520745793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15228509733347029680497195 22842764600020544520745793)
                ·
                  refine ⟨17132073450015408390559345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22842764600020544520745793 17132073450015408390559345)
                  ·
                    refine ⟨12849055087511556292919509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17132073450015408390559345 12849055087511556292919509)
                    ·
                      refine ⟨301149728613552100615301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 12849055087511556292919509 301149728613552100615301)
                      ·
                        rfl

theorem cell23_586487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_586487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586487 prefixEnd_586487 := by exact prefixLift 586487
  have htrace : WordTrace (prefixWord ++ tailWord_586487) baseStart_586487 baseEnd_586487 := by
    simpa [prefixWord, tailWord_586487, baseEnd_586487] using wordTrace_append hprefix tailTrace_586487
  have hstable : (prefixWord ++ tailWord_586487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586487).length < 2 ^ (prefixWord ++ tailWord_586487).sum := by decide
  have hdescent : baseEnd_586487 < baseStart_586487 := by decide
  rcases family_descends (prefixWord ++ tailWord_586487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586488 : List Nat := [2, 1, 2, 1, 1, 2, 6, 1, 3, 2, 2]
def baseStart_586488 : Nat := 118140960795 + 586488 * 2 ^ 59
def prefixEnd_586488 : Nat := 4983230072969 + 3 ^ 40 * 586488 * 2
def baseEnd_586488 : Nat := 301150242094206596702797

theorem tailTrace_586488 : CollatzResearch.WordTrace tailWord_586488 prefixEnd_586488 301150242094206596702797 := by
  unfold tailWord_586488
  simp only [CollatzResearch.WordTrace]
  refine ⟨10695487349630807510516059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14260649799507743347354745 10695487349630807510516059)
  ·
    refine ⟨16043231024446211265774089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10695487349630807510516059 16043231024446211265774089)
    ·
      refine ⟨12032423268334658449330567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16043231024446211265774089 12032423268334658449330567)
      ·
        refine ⟨18048634902501987673995851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12032423268334658449330567 18048634902501987673995851)
        ·
          refine ⟨27072952353752981510993777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18048634902501987673995851 27072952353752981510993777)
          ·
            refine ⟨20304714265314736133245333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27072952353752981510993777 20304714265314736133245333)
            ·
              refine ⟨951783481186628256245875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20304714265314736133245333 951783481186628256245875)
              ·
                refine ⟨1427675221779942384368813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 951783481186628256245875 1427675221779942384368813)
                ·
                  refine ⟨535378208167478394138305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1427675221779942384368813 535378208167478394138305)
                  ·
                    refine ⟨401533656125608795603729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 535378208167478394138305 401533656125608795603729)
                    ·
                      refine ⟨301150242094206596702797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 401533656125608795603729 301150242094206596702797)
                      ·
                        rfl

theorem cell23_586488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 3, 2, 2].length) (baseStart_586488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586488 prefixEnd_586488 := by exact prefixLift 586488
  have htrace : WordTrace (prefixWord ++ tailWord_586488) baseStart_586488 baseEnd_586488 := by
    simpa [prefixWord, tailWord_586488, baseEnd_586488] using wordTrace_append hprefix tailTrace_586488
  have hstable : (prefixWord ++ tailWord_586488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586488).length < 2 ^ (prefixWord ++ tailWord_586488).sum := by decide
  have hdescent : baseEnd_586488 < baseStart_586488 := by decide
  rcases family_descends (prefixWord ++ tailWord_586488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586498 : List Nat := [3, 4, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_586498 : Nat := 118140960795 + 586498 * 2 ^ 59
def prefixEnd_586498 : Nat := 4983230072969 + 3 ^ 40 * 586498 * 2
def baseEnd_586498 : Nat := 100385125633583852525917

theorem tailTrace_586498 : CollatzResearch.WordTrace tailWord_586498 prefixEnd_586498 100385125633583852525917 := by
  unfold tailWord_586498
  simp only [CollatzResearch.WordTrace]
  refine ⟨5347834857306346682224037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14260892952816924485930765 5347834857306346682224037)
  ·
    refine ⟨1002719035744940002917007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5347834857306346682224037 1002719035744940002917007)
    ·
      refine ⟨1504078553617410004375511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1002719035744940002917007 1504078553617410004375511)
      ·
        refine ⟨2256117830426115006563267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1504078553617410004375511 2256117830426115006563267)
        ·
          refine ⟨3384176745639172509844901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2256117830426115006563267 3384176745639172509844901)
          ·
            refine ⟨634533139807344845595919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3384176745639172509844901 634533139807344845595919)
            ·
              refine ⟨951799709711017268393879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634533139807344845595919 951799709711017268393879)
              ·
                refine ⟨1427699564566525902590819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 951799709711017268393879 1427699564566525902590819)
                ·
                  refine ⟨2141549346849788853886229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1427699564566525902590819 2141549346849788853886229)
                  ·
                    refine ⟨100385125633583852525917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2141549346849788853886229 100385125633583852525917)
                    ·
                      rfl

theorem cell23_586498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_586498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586498 prefixEnd_586498 := by exact prefixLift 586498
  have htrace : WordTrace (prefixWord ++ tailWord_586498) baseStart_586498 baseEnd_586498 := by
    simpa [prefixWord, tailWord_586498, baseEnd_586498] using wordTrace_append hprefix tailTrace_586498
  have hstable : (prefixWord ++ tailWord_586498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586498).length < 2 ^ (prefixWord ++ tailWord_586498).sum := by decide
  have hdescent : baseEnd_586498 < baseStart_586498 := by decide
  rcases family_descends (prefixWord ++ tailWord_586498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586531 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 5, 3, 2]
def baseStart_586531 : Nat := 118140960795 + 586531 * 2 ^ 59
def prefixEnd_586531 : Nat := 4983230072969 + 3 ^ 40 * 586531 * 2
def baseEnd_586531 : Nat := 301172321762349928465099

theorem tailTrace_586531 : CollatzResearch.WordTrace tailWord_586531 prefixEnd_586531 301172321762349928465099 := by
  unfold tailWord_586531
  simp only [CollatzResearch.WordTrace]
  refine ⟨21392543038105833364847447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14261695358737222243231631 21392543038105833364847447)
  ·
    refine ⟨32088814557158750047271171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21392543038105833364847447 32088814557158750047271171)
    ·
      refine ⟨48133221835738125070906757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32088814557158750047271171 48133221835738125070906757)
      ·
        refine ⟨9024979094200898450795017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48133221835738125070906757 9024979094200898450795017)
        ·
          refine ⟨6768734320650673838096263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9024979094200898450795017 6768734320650673838096263)
          ·
            refine ⟨10153101480976010757144395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6768734320650673838096263 10153101480976010757144395)
            ·
              refine ⟨15229652221464016135716593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10153101480976010757144395 15229652221464016135716593)
              ·
                refine ⟨11422239166098012101787445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15229652221464016135716593 11422239166098012101787445)
                ·
                  refine ⟨1070834921821688634542573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11422239166098012101787445 1070834921821688634542573)
                  ·
                    refine ⟨401563095683133237953465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1070834921821688634542573 401563095683133237953465)
                    ·
                      refine ⟨301172321762349928465099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 401563095683133237953465 301172321762349928465099)
                      ·
                        rfl

theorem cell23_586531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 3, 2].length) (baseStart_586531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586531 prefixEnd_586531 := by exact prefixLift 586531
  have htrace : WordTrace (prefixWord ++ tailWord_586531) baseStart_586531 baseEnd_586531 := by
    simpa [prefixWord, tailWord_586531, baseEnd_586531] using wordTrace_append hprefix tailTrace_586531
  have hstable : (prefixWord ++ tailWord_586531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586531).length < 2 ^ (prefixWord ++ tailWord_586531).sum := by decide
  have hdescent : baseEnd_586531 < baseStart_586531 := by decide
  rcases family_descends (prefixWord ++ tailWord_586531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586578 : List Nat := [3, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2]
def baseStart_586578 : Nat := 118140960795 + 586578 * 2 ^ 59
def prefixEnd_586578 : Nat := 4983230072969 + 3 ^ 40 * 586578 * 2
def baseEnd_586578 : Nat := 301196455353111244577383

theorem tailTrace_586578 : CollatzResearch.WordTrace tailWord_586578 prefixEnd_586578 301196455353111244577383 := by
  unfold tailWord_586578
  simp only [CollatzResearch.WordTrace]
  refine ⟨5348564317233890097952097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14262838179290373594538925 5348564317233890097952097)
  ·
    refine ⟨4011423237925417573464073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5348564317233890097952097 4011423237925417573464073)
    ·
      refine ⟨3008567428444063180098055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4011423237925417573464073 3008567428444063180098055)
      ·
        refine ⟨4512851142666094770147083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3008567428444063180098055 4512851142666094770147083)
        ·
          refine ⟨6769276713999142155220625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4512851142666094770147083 6769276713999142155220625)
          ·
            refine ⟨5076957535499356616415469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6769276713999142155220625 5076957535499356616415469)
            ·
              refine ⟨1903859075812258731155801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5076957535499356616415469 1903859075812258731155801)
              ·
                refine ⟨1427894306859194048366851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1903859075812258731155801 1427894306859194048366851)
                ·
                  refine ⟨2141841460288791072550277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1427894306859194048366851 2141841460288791072550277)
                  ·
                    refine ⟨401595273804148326103177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2141841460288791072550277 401595273804148326103177)
                    ·
                      refine ⟨301196455353111244577383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 401595273804148326103177 301196455353111244577383)
                      ·
                        rfl

theorem cell23_586578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_586578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586578 prefixEnd_586578 := by exact prefixLift 586578
  have htrace : WordTrace (prefixWord ++ tailWord_586578) baseStart_586578 baseEnd_586578 := by
    simpa [prefixWord, tailWord_586578, baseEnd_586578] using wordTrace_append hprefix tailTrace_586578
  have hstable : (prefixWord ++ tailWord_586578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586578).length < 2 ^ (prefixWord ++ tailWord_586578).sum := by decide
  have hdescent : baseEnd_586578 < baseStart_586578 := by decide
  rcases family_descends (prefixWord ++ tailWord_586578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586595 : List Nat := [1, 1, 1, 5, 3, 1, 1, 4, 2, 2, 2]
def baseStart_586595 : Nat := 118140960795 + 586595 * 2 ^ 59
def prefixEnd_586595 : Nat := 4983230072969 + 3 ^ 40 * 586595 * 2
def baseEnd_586595 : Nat := 301205184524237678064805

theorem tailTrace_586595 : CollatzResearch.WordTrace tailWord_586595 prefixEnd_586595 301205184524237678064805 := by
  unfold tailWord_586595
  simp only [CollatzResearch.WordTrace]
  refine ⟨21394877309873972295177239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14263251539915981530118159 21394877309873972295177239)
  ·
    refine ⟨32092315964810958442765859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21394877309873972295177239 32092315964810958442765859)
    ·
      refine ⟨48138473947216437664148789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32092315964810958442765859 48138473947216437664148789)
      ·
        refine ⟨4512981932551541031013949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48138473947216437664148789 4512981932551541031013949)
        ·
          refine ⟨1692368224706827886630231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4512981932551541031013949 1692368224706827886630231)
          ·
            refine ⟨2538552337060241829945347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1692368224706827886630231 2538552337060241829945347)
            ·
              refine ⟨3807828505590362744918021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2538552337060241829945347 3807828505590362744918021)
              ·
                refine ⟨713967844798193014672129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3807828505590362744918021 713967844798193014672129)
                ·
                  refine ⟨535475883598644761004097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 713967844798193014672129 535475883598644761004097)
                  ·
                    refine ⟨401606912698983570753073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 535475883598644761004097 401606912698983570753073)
                    ·
                      refine ⟨301205184524237678064805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 401606912698983570753073 301205184524237678064805)
                      ·
                        rfl

theorem cell23_586595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_586595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586595 prefixEnd_586595 := by exact prefixLift 586595
  have htrace : WordTrace (prefixWord ++ tailWord_586595) baseStart_586595 baseEnd_586595 := by
    simpa [prefixWord, tailWord_586595, baseEnd_586595] using wordTrace_append hprefix tailTrace_586595
  have hstable : (prefixWord ++ tailWord_586595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586595).length < 2 ^ (prefixWord ++ tailWord_586595).sum := by decide
  have hdescent : baseEnd_586595 < baseStart_586595 := by decide
  rcases family_descends (prefixWord ++ tailWord_586595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586624 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 5]
def baseStart_586624 : Nat := 118140960795 + 586624 * 2 ^ 59
def prefixEnd_586624 : Nat := 4983230072969 + 3 ^ 40 * 586624 * 2
def baseEnd_586624 : Nat := 301220075463218064602171

theorem tailTrace_586624 : CollatzResearch.WordTrace tailWord_586624 prefixEnd_586624 301220075463218064602171 := by
  unfold tailWord_586624
  simp only [CollatzResearch.WordTrace]
  refine ⟨10697967513384455123991463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14263956684512606831988617 10697967513384455123991463)
  ·
    refine ⟨16046951270076682685987195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10697967513384455123991463 16046951270076682685987195)
    ·
      refine ⟨24070426905115024028980793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16046951270076682685987195 24070426905115024028980793)
      ·
        refine ⟨18052820178836268021735595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24070426905115024028980793 18052820178836268021735595)
        ·
          refine ⟨27079230268254402032603393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18052820178836268021735595 27079230268254402032603393)
          ·
            refine ⟨20309422701190801524452545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27079230268254402032603393 20309422701190801524452545)
            ·
              refine ⟨15232067025893101143339409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20309422701190801524452545 15232067025893101143339409)
              ·
                refine ⟨11424050269419825857504557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15232067025893101143339409 11424050269419825857504557)
                ·
                  refine ⟨4284018851032434696564209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11424050269419825857504557 4284018851032434696564209)
                  ·
                    refine ⟨3213014138274326022423157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4284018851032434696564209 3213014138274326022423157)
                    ·
                      refine ⟨301220075463218064602171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3213014138274326022423157 301220075463218064602171)
                      ·
                        rfl

theorem cell23_586624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_586624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586624 prefixEnd_586624 := by exact prefixLift 586624
  have htrace : WordTrace (prefixWord ++ tailWord_586624) baseStart_586624 baseEnd_586624 := by
    simpa [prefixWord, tailWord_586624, baseEnd_586624] using wordTrace_append hprefix tailTrace_586624
  have hstable : (prefixWord ++ tailWord_586624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586624).length < 2 ^ (prefixWord ++ tailWord_586624).sum := by decide
  have hdescent : baseEnd_586624 < baseStart_586624 := by decide
  rcases family_descends (prefixWord ++ tailWord_586624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586631 : List Nat := [1, 1, 4, 2, 3, 2, 1, 1, 1, 7]
def baseStart_586631 : Nat := 118140960795 + 586631 * 2 ^ 59
def prefixEnd_586631 : Nat := 4983230072969 + 3 ^ 40 * 586631 * 2
def baseEnd_586631 : Nat := 100407889942599845738213

theorem tailTrace_586631 : CollatzResearch.WordTrace tailWord_586631 prefixEnd_586631 100407889942599845738213 := by
  unfold tailWord_586631
  simp only [CollatzResearch.WordTrace]
  refine ⟨21396190337743550443487747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14264126891829033628991831 21396190337743550443487747)
  ·
    refine ⟨32094285506615325665231621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21396190337743550443487747 32094285506615325665231621)
    ·
      refine ⟨6017678532490373562230929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32094285506615325665231621 6017678532490373562230929)
      ·
        refine ⟨4513258899367780171673197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6017678532490373562230929 4513258899367780171673197)
        ·
          refine ⟨1692472087262917564377449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4513258899367780171673197 1692472087262917564377449)
          ·
            refine ⟨1269354065447188173283087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1692472087262917564377449 1269354065447188173283087)
            ·
              refine ⟨1904031098170782259924631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1269354065447188173283087 1904031098170782259924631)
              ·
                refine ⟨2856046647256173389886947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1904031098170782259924631 2856046647256173389886947)
                ·
                  refine ⟨4284069970884260084830421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2856046647256173389886947 4284069970884260084830421)
                  ·
                    refine ⟨100407889942599845738213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4284069970884260084830421 100407889942599845738213)
                    ·
                      rfl

theorem cell23_586631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_586631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586631 prefixEnd_586631 := by exact prefixLift 586631
  have htrace : WordTrace (prefixWord ++ tailWord_586631) baseStart_586631 baseEnd_586631 := by
    simpa [prefixWord, tailWord_586631, baseEnd_586631] using wordTrace_append hprefix tailTrace_586631
  have hstable : (prefixWord ++ tailWord_586631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586631).length < 2 ^ (prefixWord ++ tailWord_586631).sum := by decide
  have hdescent : baseEnd_586631 < baseStart_586631 := by decide
  rcases family_descends (prefixWord ++ tailWord_586631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586646 : List Nat := [5, 3, 1, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_586646 : Nat := 118140960795 + 586646 * 2 ^ 59
def prefixEnd_586646 : Nat := 4983230072969 + 3 ^ 40 * 586646 * 2
def baseEnd_586646 : Nat := 301231372037616978527071

theorem tailTrace_586646 : CollatzResearch.WordTrace tailWord_586646 prefixEnd_586646 301231372037616978527071 := by
  unfold tailWord_586646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1337296089543075500330237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14264491621792805336855861 1337296089543075500330237)
  ·
    refine ⟨501486033578653312623839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1337296089543075500330237 501486033578653312623839)
    ·
      refine ⟨752229050367979968935759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 501486033578653312623839 752229050367979968935759)
      ·
        refine ⟨1128343575551969953403639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 752229050367979968935759 1128343575551969953403639)
        ·
          refine ⟨1692515363327954930105459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1128343575551969953403639 1692515363327954930105459)
          ·
            refine ⟨2538773044991932395158189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1692515363327954930105459 2538773044991932395158189)
            ·
              refine ⟨952039891871974648184321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2538773044991932395158189 952039891871974648184321)
              ·
                refine ⟨714029918903980986138241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 952039891871974648184321 714029918903980986138241)
                ·
                  refine ⟨535522439177985739603681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 714029918903980986138241 535522439177985739603681)
                  ·
                    refine ⟨401641829383489304702761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 535522439177985739603681 401641829383489304702761)
                    ·
                      refine ⟨301231372037616978527071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 401641829383489304702761 301231372037616978527071)
                      ·
                        rfl

theorem cell23_586646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_586646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586646 prefixEnd_586646 := by exact prefixLift 586646
  have htrace : WordTrace (prefixWord ++ tailWord_586646) baseStart_586646 baseEnd_586646 := by
    simpa [prefixWord, tailWord_586646, baseEnd_586646] using wordTrace_append hprefix tailTrace_586646
  have hstable : (prefixWord ++ tailWord_586646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586646).length < 2 ^ (prefixWord ++ tailWord_586646).sum := by decide
  have hdescent : baseEnd_586646 < baseStart_586646 := by decide
  rcases family_descends (prefixWord ++ tailWord_586646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586671 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 3]
def baseStart_586671 : Nat := 118140960795 + 586671 * 2 ^ 59
def prefixEnd_586671 : Nat := 4983230072969 + 3 ^ 40 * 586671 * 2
def baseEnd_586671 : Nat := 301244209053979380714455

theorem tailTrace_586671 : CollatzResearch.WordTrace tailWord_586671 prefixEnd_586671 301244209053979380714455 := by
  unfold tailWord_586671
  simp only [CollatzResearch.WordTrace]
  refine ⟨21397649257598637274943867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14265099505065758183295911 21397649257598637274943867)
  ·
    refine ⟨32096473886397955912415801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21397649257598637274943867 32096473886397955912415801)
    ·
      refine ⟨24072355414798466934311851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32096473886397955912415801 24072355414798466934311851)
      ·
        refine ⟨36108533122197700401467777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24072355414798466934311851 36108533122197700401467777)
        ·
          refine ⟨27081399841648275301100833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36108533122197700401467777 27081399841648275301100833)
          ·
            refine ⟨20311049881236206475825625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27081399841648275301100833 20311049881236206475825625)
            ·
              refine ⟨15233287410927154856869219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20311049881236206475825625 15233287410927154856869219)
              ·
                refine ⟨22849931116390732285303829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15233287410927154856869219 22849931116390732285303829)
                ·
                  refine ⟨1071090521080815575873617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22849931116390732285303829 1071090521080815575873617)
                  ·
                    refine ⟨803317890810611681905213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1071090521080815575873617 803317890810611681905213)
                    ·
                      refine ⟨301244209053979380714455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 803317890810611681905213 301244209053979380714455)
                      ·
                        rfl

theorem cell23_586671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 3].length) (baseStart_586671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_586671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_586671 prefixEnd_586671 := by exact prefixLift 586671
  have htrace : WordTrace (prefixWord ++ tailWord_586671) baseStart_586671 baseEnd_586671 := by
    simpa [prefixWord, tailWord_586671, baseEnd_586671] using wordTrace_append hprefix tailTrace_586671
  have hstable : (prefixWord ++ tailWord_586671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586671).length < 2 ^ (prefixWord ++ tailWord_586671).sum := by decide
  have hdescent : baseEnd_586671 < baseStart_586671 := by decide
  rcases family_descends (prefixWord ++ tailWord_586671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
