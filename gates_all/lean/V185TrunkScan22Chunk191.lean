import V185TrunkScan22Chunk190

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1703576 : List Nat := [2, 1, 2, 4, 1, 2, 2, 2, 2, 4]
def baseStart_1703576 : Nat := 118140960795 + 1703576 * 2 ^ 59
def prefixEnd_1703576 : Nat := 4983230072969 + 3 ^ 40 * 1703576 * 2
def baseEnd_1703576 : Nat := 583168879642621323176935

theorem tailTrace_1703576 : CollatzResearch.WordTrace tailWord_1703576 prefixEnd_1703576 583168879642621323176935 := by
  unfold tailWord_1703576
  simp only [CollatzResearch.WordTrace]
  refine ⟨31067260638121287231193291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41423014184161716308257721 31067260638121287231193291)
  ·
    refine ⟨46600890957181930846789937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31067260638121287231193291 46600890957181930846789937)
    ·
      refine ⟨34950668217886448135092453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46600890957181930846789937 34950668217886448135092453)
      ·
        refine ⟨6553250290853709025329835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34950668217886448135092453 6553250290853709025329835)
        ·
          refine ⟨9829875436280563537994753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6553250290853709025329835 9829875436280563537994753)
          ·
            refine ⟨7372406577210422653496065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9829875436280563537994753 7372406577210422653496065)
            ·
              refine ⟨5529304932907816990122049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7372406577210422653496065 5529304932907816990122049)
              ·
                refine ⟨4146978699680862742591537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5529304932907816990122049 4146978699680862742591537)
                ·
                  refine ⟨3110234024760647056943653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4146978699680862742591537 3110234024760647056943653)
                  ·
                    refine ⟨583168879642621323176935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3110234024760647056943653 583168879642621323176935)
                    ·
                      rfl

theorem cell22_1703576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_1703576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1703576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1703576 prefixEnd_1703576 := by exact prefixLift 1703576
  have htrace : WordTrace (prefixWord ++ tailWord_1703576) baseStart_1703576 baseEnd_1703576 := by
    simpa [prefixWord, tailWord_1703576, baseEnd_1703576] using wordTrace_append hprefix tailTrace_1703576
  have hstable : (prefixWord ++ tailWord_1703576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703576).length < 2 ^ (prefixWord ++ tailWord_1703576).sum := by decide
  have hdescent : baseEnd_1703576 < baseStart_1703576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703653 : List Nat := [1, 3, 1, 4, 1, 1, 5, 1, 5]
def baseStart_1703653 : Nat := 118140960795 + 1703653 * 2 ^ 59
def prefixEnd_1703653 : Nat := 4983230072969 + 3 ^ 40 * 1703653 * 2
def baseEnd_1703653 : Nat := 194398412772072929667233

theorem tailTrace_1703653 : CollatzResearch.WordTrace tailWord_1703653 prefixEnd_1703653 194398412772072929667233 := by
  unfold tailWord_1703653
  simp only [CollatzResearch.WordTrace]
  refine ⟨62137329696963616612939613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41424886464642411075293075 62137329696963616612939613)
  ·
    refine ⟨23301498636361356229852355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62137329696963616612939613 23301498636361356229852355)
    ·
      refine ⟨34952247954542034344778533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23301498636361356229852355 34952247954542034344778533)
      ·
        refine ⟨6553546491476631439645975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34952247954542034344778533 6553546491476631439645975)
        ·
          refine ⟨9830319737214947159468963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6553546491476631439645975 9830319737214947159468963)
          ·
            refine ⟨14745479605822420739203445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9830319737214947159468963 14745479605822420739203445)
            ·
              refine ⟨1382388713045851944300323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14745479605822420739203445 1382388713045851944300323)
              ·
                refine ⟨2073583069568777916450485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1382388713045851944300323 2073583069568777916450485)
                ·
                  refine ⟨194398412772072929667233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2073583069568777916450485 194398412772072929667233)
                  ·
                    rfl

theorem cell22_1703653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 5].length) (baseStart_1703653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1703653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1703653 prefixEnd_1703653 := by exact prefixLift 1703653
  have htrace : WordTrace (prefixWord ++ tailWord_1703653) baseStart_1703653 baseEnd_1703653 := by
    simpa [prefixWord, tailWord_1703653, baseEnd_1703653] using wordTrace_append hprefix tailTrace_1703653
  have hstable : (prefixWord ++ tailWord_1703653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703653).length < 2 ^ (prefixWord ++ tailWord_1703653).sum := by decide
  have hdescent : baseEnd_1703653 < baseStart_1703653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703664 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 8]
def baseStart_1703664 : Nat := 118140960795 + 1703664 * 2 ^ 59
def prefixEnd_1703664 : Nat := 4983230072969 + 3 ^ 40 * 1703664 * 2
def baseEnd_1703664 : Nat := 194399667947006142325555

theorem tailTrace_1703664 : CollatzResearch.WordTrace tailWord_1703664 prefixEnd_1703664 194399667947006142325555 := by
  unfold tailWord_1703664
  simp only [CollatzResearch.WordTrace]
  refine ⟨31068865449961882745795023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41425153933282510327726697 31068865449961882745795023)
  ·
    refine ⟨46603298174942824118692535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31068865449961882745795023 46603298174942824118692535)
    ·
      refine ⟨69904947262414236178038803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46603298174942824118692535 69904947262414236178038803)
      ·
        refine ⟨104857420893621354267058205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69904947262414236178038803 104857420893621354267058205)
        ·
          refine ⟨39321532835108007850146827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104857420893621354267058205 39321532835108007850146827)
          ·
            refine ⟨58982299252662011775220241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39321532835108007850146827 58982299252662011775220241)
            ·
              refine ⟨44236724439496508831415181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58982299252662011775220241 44236724439496508831415181)
              ·
                refine ⟨16588771664811190811780693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44236724439496508831415181 16588771664811190811780693)
                ·
                  refine ⟨194399667947006142325555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16588771664811190811780693 194399667947006142325555)
                  ·
                    rfl

theorem cell22_1703664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 8].length) (baseStart_1703664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1703664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1703664 prefixEnd_1703664 := by exact prefixLift 1703664
  have htrace : WordTrace (prefixWord ++ tailWord_1703664) baseStart_1703664 baseEnd_1703664 := by
    simpa [prefixWord, tailWord_1703664, baseEnd_1703664] using wordTrace_append hprefix tailTrace_1703664
  have hstable : (prefixWord ++ tailWord_1703664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703664).length < 2 ^ (prefixWord ++ tailWord_1703664).sum := by decide
  have hdescent : baseEnd_1703664 < baseStart_1703664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703711 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 4, 4]
def baseStart_1703711 : Nat := 118140960795 + 1703711 * 2 ^ 59
def prefixEnd_1703711 : Nat := 4983230072969 + 3 ^ 40 * 1703711 * 2
def baseEnd_1703711 : Nat := 583215092901525971051521

theorem tailTrace_1703711 : CollatzResearch.WordTrace tailWord_1703711 prefixEnd_1703711 583215092901525971051521 := by
  unfold tailWord_1703711
  simp only [CollatzResearch.WordTrace]
  refine ⟨62139445130753492518550987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41426296753835661679033991 62139445130753492518550987)
  ·
    refine ⟨93209167696130238777826481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62139445130753492518550987 93209167696130238777826481)
    ·
      refine ⟨69906875772097679083369861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93209167696130238777826481 69906875772097679083369861)
      ·
        refine ⟨13107539207268314828131849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69906875772097679083369861 13107539207268314828131849)
        ·
          refine ⟨9830654405451236121098887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13107539207268314828131849 9830654405451236121098887)
          ·
            refine ⟨14745981608176854181648331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9830654405451236121098887 14745981608176854181648331)
            ·
              refine ⟨22118972412265281272472497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14745981608176854181648331 22118972412265281272472497)
              ·
                refine ⟨16589229309198960954354373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22118972412265281272472497 16589229309198960954354373)
                ·
                  refine ⟨3110480495474805178941445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16589229309198960954354373 3110480495474805178941445)
                  ·
                    refine ⟨583215092901525971051521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3110480495474805178941445 583215092901525971051521)
                    ·
                      rfl

theorem cell22_1703711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 4].length) (baseStart_1703711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1703711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1703711 prefixEnd_1703711 := by exact prefixLift 1703711
  have htrace : WordTrace (prefixWord ++ tailWord_1703711) baseStart_1703711 baseEnd_1703711 := by
    simpa [prefixWord, tailWord_1703711, baseEnd_1703711] using wordTrace_append hprefix tailTrace_1703711
  have hstable : (prefixWord ++ tailWord_1703711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703711).length < 2 ^ (prefixWord ++ tailWord_1703711).sum := by decide
  have hdescent : baseEnd_1703711 < baseStart_1703711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703865 : List Nat := [1, 2, 1, 4, 2, 1, 2, 4, 2, 3]
def baseStart_1703865 : Nat := 118140960795 + 1703865 * 2 ^ 59
def prefixEnd_1703865 : Nat := 4983230072969 + 3 ^ 40 * 1703865 * 2
def baseEnd_1703865 : Nat := 583267810248720902701049

theorem tailTrace_1703865 : CollatzResearch.WordTrace tailWord_1703865 prefixEnd_1703865 583267810248720902701049 := by
  unfold tailWord_1703865
  simp only [CollatzResearch.WordTrace]
  refine ⟨62145061972195576819657049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41430041314797051213104699 62145061972195576819657049)
  ·
    refine ⟨46608796479146682614742787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62145061972195576819657049 46608796479146682614742787)
    ·
      refine ⟨69913194718720023922114181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46608796479146682614742787 69913194718720023922114181)
      ·
        refine ⟨13108724009760004485396409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69913194718720023922114181 13108724009760004485396409)
        ·
          refine ⟨9831543007320003364047307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13108724009760004485396409 9831543007320003364047307)
          ·
            refine ⟨14747314510980005046070961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9831543007320003364047307 14747314510980005046070961)
            ·
              refine ⟨11060485883235003784553221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14747314510980005046070961 11060485883235003784553221)
              ·
                refine ⟨2073841103106563209603729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11060485883235003784553221 2073841103106563209603729)
                ·
                  refine ⟨1555380827329922407202797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2073841103106563209603729 1555380827329922407202797)
                  ·
                    refine ⟨583267810248720902701049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1555380827329922407202797 583267810248720902701049)
                    ·
                      rfl

theorem cell22_1703865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 3].length) (baseStart_1703865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1703865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1703865 prefixEnd_1703865 := by exact prefixLift 1703865
  have htrace : WordTrace (prefixWord ++ tailWord_1703865) baseStart_1703865 baseEnd_1703865 := by
    simpa [prefixWord, tailWord_1703865, baseEnd_1703865] using wordTrace_append hprefix tailTrace_1703865
  have hstable : (prefixWord ++ tailWord_1703865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703865).length < 2 ^ (prefixWord ++ tailWord_1703865).sum := by decide
  have hdescent : baseEnd_1703865 < baseStart_1703865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703882 : List Nat := [3, 1, 2, 1, 2, 1, 6, 1, 2, 3]
def baseStart_1703882 : Nat := 118140960795 + 1703882 * 2 ^ 59
def prefixEnd_1703882 : Nat := 4983230072969 + 3 ^ 40 * 1703882 * 2
def baseEnd_1703882 : Nat := 583273629696138525025997

theorem tailTrace_1703882 : CollatzResearch.WordTrace tailWord_1703882 prefixEnd_1703882 583273629696138525025997 := by
  unfold tailWord_1703882
  simp only [CollatzResearch.WordTrace]
  refine ⟨15536420503283497180756475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41430454675422659148683933 15536420503283497180756475)
  ·
    refine ⟨23304630754925245771134713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15536420503283497180756475 23304630754925245771134713)
    ·
      refine ⟨17478473066193934328351035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23304630754925245771134713 17478473066193934328351035)
      ·
        refine ⟨26217709599290901492526553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17478473066193934328351035 26217709599290901492526553)
        ·
          refine ⟨19663282199468176119394915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26217709599290901492526553 19663282199468176119394915)
          ·
            refine ⟨29494923299202264179092373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19663282199468176119394915 29494923299202264179092373)
            ·
              refine ⟨1382574529650106133394955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29494923299202264179092373 1382574529650106133394955)
              ·
                refine ⟨2073861794475159200092433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1382574529650106133394955 2073861794475159200092433)
                ·
                  refine ⟨1555396345856369400069325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2073861794475159200092433 1555396345856369400069325)
                  ·
                    refine ⟨583273629696138525025997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1555396345856369400069325 583273629696138525025997)
                    ·
                      rfl

theorem cell22_1703882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_1703882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1703882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1703882 prefixEnd_1703882 := by exact prefixLift 1703882
  have htrace : WordTrace (prefixWord ++ tailWord_1703882) baseStart_1703882 baseEnd_1703882 := by
    simpa [prefixWord, tailWord_1703882, baseEnd_1703882] using wordTrace_append hprefix tailTrace_1703882
  have hstable : (prefixWord ++ tailWord_1703882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703882).length < 2 ^ (prefixWord ++ tailWord_1703882).sum := by decide
  have hdescent : baseEnd_1703882 < baseStart_1703882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703985 : List Nat := [1, 2, 2, 3, 1, 4, 2, 1, 6]
def baseStart_1703985 : Nat := 118140960795 + 1703985 * 2 ^ 59
def prefixEnd_1703985 : Nat := 4983230072969 + 3 ^ 40 * 1703985 * 2
def baseEnd_1703985 : Nat := 194436296233693529900227

theorem tailTrace_1703985 : CollatzResearch.WordTrace tailWord_1703985 prefixEnd_1703985 194436296233693529900227 := by
  unfold tailWord_1703985
  simp only [CollatzResearch.WordTrace]
  refine ⟨62149438731760837314025409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41432959154507224876016939 62149438731760837314025409)
  ·
    refine ⟨46612079048820627985519057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62149438731760837314025409 46612079048820627985519057)
    ·
      refine ⟨34959059286615470989139293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46612079048820627985519057 34959059286615470989139293)
      ·
        refine ⟨13109647232480801620927235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34959059286615470989139293 13109647232480801620927235)
        ·
          refine ⟨19664470848721202431390853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13109647232480801620927235 19664470848721202431390853)
          ·
            refine ⟨3687088284135225455885785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19664470848721202431390853 3687088284135225455885785)
            ·
              refine ⟨2765316213101419091914339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3687088284135225455885785 2765316213101419091914339)
              ·
                refine ⟨4147974319652128637871509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2765316213101419091914339 4147974319652128637871509)
                ·
                  refine ⟨194436296233693529900227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4147974319652128637871509 194436296233693529900227)
                  ·
                    rfl

theorem cell22_1703985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 6].length) (baseStart_1703985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1703985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1703985 prefixEnd_1703985 := by exact prefixLift 1703985
  have htrace : WordTrace (prefixWord ++ tailWord_1703985) baseStart_1703985 baseEnd_1703985 := by
    simpa [prefixWord, tailWord_1703985, baseEnd_1703985] using wordTrace_append hprefix tailTrace_1703985
  have hstable : (prefixWord ++ tailWord_1703985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703985).length < 2 ^ (prefixWord ++ tailWord_1703985).sum := by decide
  have hdescent : baseEnd_1703985 < baseStart_1703985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704000 : List Nat := [2, 1, 1, 2, 2, 4, 3, 1, 1, 5]
def baseStart_1704000 : Nat := 118140960795 + 1704000 * 2 ^ 59
def prefixEnd_1704000 : Nat := 4983230072969 + 3 ^ 40 * 1704000 * 2
def baseEnd_1704000 : Nat := 583314023507625550575635

theorem tailTrace_1704000 : CollatzResearch.WordTrace tailWord_1704000 prefixEnd_1704000 583314023507625550575635 := by
  unfold tailWord_1704000
  simp only [CollatzResearch.WordTrace]
  refine ⟨31074992913353247437910727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41433323884470996583880969 31074992913353247437910727)
  ·
    refine ⟨46612489370029871156866091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31074992913353247437910727 46612489370029871156866091)
    ·
      refine ⟨69918734055044806735299137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46612489370029871156866091 69918734055044806735299137)
      ·
        refine ⟨52439050541283605051474353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69918734055044806735299137 52439050541283605051474353)
        ·
          refine ⟨39329287905962703788605765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52439050541283605051474353 39329287905962703788605765)
          ·
            refine ⟨7374241482368006960363581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39329287905962703788605765 7374241482368006960363581)
            ·
              refine ⟨2765340555888002610136343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7374241482368006960363581 2765340555888002610136343)
              ·
                refine ⟨4148010833832003915204515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2765340555888002610136343 4148010833832003915204515)
                ·
                  refine ⟨6222016250748005872806773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4148010833832003915204515 6222016250748005872806773)
                  ·
                    refine ⟨583314023507625550575635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6222016250748005872806773 583314023507625550575635)
                    ·
                      rfl

theorem cell22_1704000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 1, 5].length) (baseStart_1704000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704000 prefixEnd_1704000 := by exact prefixLift 1704000
  have htrace : WordTrace (prefixWord ++ tailWord_1704000) baseStart_1704000 baseEnd_1704000 := by
    simpa [prefixWord, tailWord_1704000, baseEnd_1704000] using wordTrace_append hprefix tailTrace_1704000
  have hstable : (prefixWord ++ tailWord_1704000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704000).length < 2 ^ (prefixWord ++ tailWord_1704000).sum := by decide
  have hdescent : baseEnd_1704000 < baseStart_1704000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704092 : List Nat := [2, 2, 3, 2, 1, 1, 4, 2, 5]
def baseStart_1704092 : Nat := 118140960795 + 1704092 * 2 ^ 59
def prefixEnd_1704092 : Nat := 4983230072969 + 3 ^ 40 * 1704092 * 2
def baseEnd_1704092 : Nat := 194448505662589325758451

theorem tailTrace_1704092 : CollatzResearch.WordTrace tailWord_1704092 prefixEnd_1704092 194448505662589325758451 := by
  unfold tailWord_1704092
  simp only [CollatzResearch.WordTrace]
  refine ⟨31076670671186597294085265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41435560894915463058780353 31076670671186597294085265)
  ·
    refine ⟨23307503003389947970563949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31076670671186597294085265 23307503003389947970563949)
    ·
      refine ⟨8740313626271230488961481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23307503003389947970563949 8740313626271230488961481)
      ·
        refine ⟨6555235219703422866721111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8740313626271230488961481 6555235219703422866721111)
        ·
          refine ⟨9832852829555134300081667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6555235219703422866721111 9832852829555134300081667)
          ·
            refine ⟨14749279244332701450122501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9832852829555134300081667 14749279244332701450122501)
            ·
              refine ⟨2765489858312381521897969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14749279244332701450122501 2765489858312381521897969)
              ·
                refine ⟨2074117393734286141423477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2765489858312381521897969 2074117393734286141423477)
                ·
                  refine ⟨194448505662589325758451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2074117393734286141423477 194448505662589325758451)
                  ·
                    rfl

theorem cell22_1704092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 5].length) (baseStart_1704092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704092 prefixEnd_1704092 := by exact prefixLift 1704092
  have htrace : WordTrace (prefixWord ++ tailWord_1704092) baseStart_1704092 baseEnd_1704092 := by
    simpa [prefixWord, tailWord_1704092, baseEnd_1704092] using wordTrace_append hprefix tailTrace_1704092
  have hstable : (prefixWord ++ tailWord_1704092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704092).length < 2 ^ (prefixWord ++ tailWord_1704092).sum := by decide
  have hdescent : baseEnd_1704092 < baseStart_1704092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704096 : List Nat := [2, 1, 1, 4, 2, 2, 4, 2, 1, 3]
def baseStart_1704096 : Nat := 118140960795 + 1704096 * 2 ^ 59
def prefixEnd_1704096 : Nat := 4983230072969 + 3 ^ 40 * 1704096 * 2
def baseEnd_1704096 : Nat := 583346886269513300175341

theorem tailTrace_1704096 : CollatzResearch.WordTrace tailWord_1704096 prefixEnd_1704096 583346886269513300175341 := by
  unfold tailWord_1704096
  simp only [CollatzResearch.WordTrace]
  refine ⟨31076743617179351635658071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41435658156239135514210761 31076743617179351635658071)
  ·
    refine ⟨46615115425769027453487107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31076743617179351635658071 46615115425769027453487107)
    ·
      refine ⟨69922673138653541180230661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46615115425769027453487107 69922673138653541180230661)
      ·
        refine ⟨13110501213497538971293249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69922673138653541180230661 13110501213497538971293249)
        ·
          refine ⟨9832875910123154228469937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13110501213497538971293249 9832875910123154228469937)
          ·
            refine ⟨7374656932592365671352453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9832875910123154228469937 7374656932592365671352453)
            ·
              refine ⟨1382748174861068563378585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7374656932592365671352453 1382748174861068563378585)
              ·
                refine ⟨1037061131145801422533939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1382748174861068563378585 1037061131145801422533939)
                ·
                  refine ⟨1555591696718702133800909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1037061131145801422533939 1555591696718702133800909)
                  ·
                    refine ⟨583346886269513300175341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1555591696718702133800909 583346886269513300175341)
                    ·
                      rfl

theorem cell22_1704096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 1, 3].length) (baseStart_1704096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704096 prefixEnd_1704096 := by exact prefixLift 1704096
  have htrace : WordTrace (prefixWord ++ tailWord_1704096) baseStart_1704096 baseEnd_1704096 := by
    simpa [prefixWord, tailWord_1704096, baseEnd_1704096] using wordTrace_append hprefix tailTrace_1704096
  have hstable : (prefixWord ++ tailWord_1704096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704096).length < 2 ^ (prefixWord ++ tailWord_1704096).sum := by decide
  have hdescent : baseEnd_1704096 < baseStart_1704096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704120 : List Nat := [2, 1, 2, 1, 2, 1, 5, 2, 6]
def baseStart_1704120 : Nat := 118140960795 + 1704120 * 2 ^ 59
def prefixEnd_1704120 : Nat := 4983230072969 + 3 ^ 40 * 1704120 * 2
def baseEnd_1704120 : Nat := 194451700653328412525089

theorem tailTrace_1704120 : CollatzResearch.WordTrace tailWord_1704120 prefixEnd_1704120 194451700653328412525089 := by
  unfold tailWord_1704120
  simp only [CollatzResearch.WordTrace]
  refine ⟨31077181293135877685094907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41436241724181170246793209 31077181293135877685094907)
  ·
    refine ⟨46615771939703816527642361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31077181293135877685094907 46615771939703816527642361)
    ·
      refine ⟨34961828954777862395731771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46615771939703816527642361 34961828954777862395731771)
      ·
        refine ⟨52442743432166793593597657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34961828954777862395731771 52442743432166793593597657)
        ·
          refine ⟨39332057574125095195198243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52442743432166793593597657 39332057574125095195198243)
          ·
            refine ⟨58998086361187642792797365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39332057574125095195198243 58998086361187642792797365)
            ·
              refine ⟨5531070596361341511824753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58998086361187642792797365 5531070596361341511824753)
              ·
                refine ⟨4148302947271006133868565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5531070596361341511824753 4148302947271006133868565)
                ·
                  refine ⟨194451700653328412525089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4148302947271006133868565 194451700653328412525089)
                  ·
                    rfl

theorem cell22_1704120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 6].length) (baseStart_1704120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704120 prefixEnd_1704120 := by exact prefixLift 1704120
  have htrace : WordTrace (prefixWord ++ tailWord_1704120) baseStart_1704120 baseEnd_1704120 := by
    simpa [prefixWord, tailWord_1704120, baseEnd_1704120] using wordTrace_append hprefix tailTrace_1704120
  have hstable : (prefixWord ++ tailWord_1704120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704120).length < 2 ^ (prefixWord ++ tailWord_1704120).sum := by decide
  have hdescent : baseEnd_1704120 < baseStart_1704120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704130 : List Nat := [3, 5, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_1704130 : Nat := 118140960795 + 1704130 * 2 ^ 59
def prefixEnd_1704130 : Nat := 4983230072969 + 3 ^ 40 * 1704130 * 2
def baseEnd_1704130 : Nat := 583358525164348544825237

theorem tailTrace_1704130 : CollatzResearch.WordTrace tailWord_1704130 prefixEnd_1704130 583358525164348544825237 := by
  unfold tailWord_1704130
  simp only [CollatzResearch.WordTrace]
  refine ⟨15538681829058881769513461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41436484877490351385369229 15538681829058881769513461)
  ·
    refine ⟨1456751421474270165891887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15538681829058881769513461 1456751421474270165891887)
    ·
      refine ⟨2185127132211405248837831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1456751421474270165891887 2185127132211405248837831)
      ·
        refine ⟨3277690698317107873256747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2185127132211405248837831 3277690698317107873256747)
        ·
          refine ⟨4916536047475661809885121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3277690698317107873256747 4916536047475661809885121)
          ·
            refine ⟨3687402035606746357413841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4916536047475661809885121 3687402035606746357413841)
            ·
              refine ⟨2765551526705059768060381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3687402035606746357413841 2765551526705059768060381)
              ·
                refine ⟨1037081822514397413022643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2765551526705059768060381 1037081822514397413022643)
                ·
                  refine ⟨1555622733771596119533965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1037081822514397413022643 1555622733771596119533965)
                  ·
                    refine ⟨583358525164348544825237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1555622733771596119533965 583358525164348544825237)
                    ·
                      rfl

theorem cell22_1704130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_1704130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704130 prefixEnd_1704130 := by exact prefixLift 1704130
  have htrace : WordTrace (prefixWord ++ tailWord_1704130) baseStart_1704130 baseEnd_1704130 := by
    simpa [prefixWord, tailWord_1704130, baseEnd_1704130] using wordTrace_append hprefix tailTrace_1704130
  have hstable : (prefixWord ++ tailWord_1704130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704130).length < 2 ^ (prefixWord ++ tailWord_1704130).sum := by decide
  have hdescent : baseEnd_1704130 < baseStart_1704130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704167 : List Nat := [1, 1, 5, 3, 1, 1, 1, 2, 1, 6]
def baseStart_1704167 : Nat := 118140960795 + 1704167 * 2 ^ 59
def prefixEnd_1704167 : Nat := 4983230072969 + 3 ^ 40 * 1704167 * 2
def baseEnd_1704167 : Nat := 583371191020492781650123

theorem tailTrace_1704167 : CollatzResearch.WordTrace tailWord_1704167 prefixEnd_1704167 583371191020492781650123 := by
  unfold tailWord_1704167
  simp only [CollatzResearch.WordTrace]
  refine ⟨62156076817101482397150755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41437384544734321598100503 62156076817101482397150755)
  ·
    refine ⟨93234115225652223595726133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62156076817101482397150755 93234115225652223595726133)
    ·
      refine ⟨8740698302404895962099325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93234115225652223595726133 8740698302404895962099325)
      ·
        refine ⟨3277761863401835985787247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8740698302404895962099325 3277761863401835985787247)
        ·
          refine ⟨4916642795102753978680871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3277761863401835985787247 4916642795102753978680871)
          ·
            refine ⟨7374964192654130968021307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4916642795102753978680871 7374964192654130968021307)
            ·
              refine ⟨11062446288981196452031961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7374964192654130968021307 11062446288981196452031961)
              ·
                refine ⟨8296834716735897339023971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11062446288981196452031961 8296834716735897339023971)
                ·
                  refine ⟨12445252075103846008535957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8296834716735897339023971 12445252075103846008535957)
                  ·
                    refine ⟨583371191020492781650123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12445252075103846008535957 583371191020492781650123)
                    ·
                      rfl

theorem cell22_1704167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_1704167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704167 prefixEnd_1704167 := by exact prefixLift 1704167
  have htrace : WordTrace (prefixWord ++ tailWord_1704167) baseStart_1704167 baseEnd_1704167 := by
    simpa [prefixWord, tailWord_1704167, baseEnd_1704167] using wordTrace_append hprefix tailTrace_1704167
  have hstable : (prefixWord ++ tailWord_1704167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704167).length < 2 ^ (prefixWord ++ tailWord_1704167).sum := by decide
  have hdescent : baseEnd_1704167 < baseStart_1704167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704199 : List Nat := [1, 1, 4, 5, 1, 2, 8]
def baseStart_1704199 : Nat := 118140960795 + 1704199 * 2 ^ 59
def prefixEnd_1704199 : Nat := 4983230072969 + 3 ^ 40 * 1704199 * 2
def baseEnd_1704199 : Nat := 21606746121276124624075

theorem tailTrace_1704199 : CollatzResearch.WordTrace tailWord_1704199 prefixEnd_1704199 21606746121276124624075 := by
  unfold tailWord_1704199
  simp only [CollatzResearch.WordTrace]
  refine ⟨62157243952985551862315651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41438162635323701241543767 62157243952985551862315651)
  ·
    refine ⟨93235865929478327793473477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62157243952985551862315651 93235865929478327793473477)
    ·
      refine ⟨17481724861777186461276277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93235865929478327793473477 17481724861777186461276277)
      ·
        refine ⟨1638911705791611230744651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17481724861777186461276277 1638911705791611230744651)
        ·
          refine ⟨2458367558687416846116977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1638911705791611230744651 2458367558687416846116977)
          ·
            refine ⟨1843775669015562634587733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2458367558687416846116977 1843775669015562634587733)
            ·
              refine ⟨21606746121276124624075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1843775669015562634587733 21606746121276124624075)
              ·
                rfl

theorem cell22_1704199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 8].length) (baseStart_1704199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704199 prefixEnd_1704199 := by exact prefixLift 1704199
  have htrace : WordTrace (prefixWord ++ tailWord_1704199) baseStart_1704199 baseEnd_1704199 := by
    simpa [prefixWord, tailWord_1704199, baseEnd_1704199] using wordTrace_append hprefix tailTrace_1704199
  have hstable : (prefixWord ++ tailWord_1704199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704199).length < 2 ^ (prefixWord ++ tailWord_1704199).sum := by decide
  have hdescent : baseEnd_1704199 < baseStart_1704199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704227 : List Nat := [1, 1, 1, 4, 2, 2, 3, 3, 5]
def baseStart_1704227 : Nat := 118140960795 + 1704227 * 2 ^ 59
def prefixEnd_1704227 : Nat := 4983230072969 + 3 ^ 40 * 1704227 * 2
def baseEnd_1704227 : Nat := 194463910082224208383313

theorem tailTrace_1704227 : CollatzResearch.WordTrace tailWord_1704227 prefixEnd_1704227 194463910082224208383313 := by
  unfold tailWord_1704227
  simp only [CollatzResearch.WordTrace]
  refine ⟨62158265196884112644334935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41438843464589408429556623 62158265196884112644334935)
  ·
    refine ⟨93237397795326168966502403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62158265196884112644334935 93237397795326168966502403)
    ·
      refine ⟨139856096692989253449753605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93237397795326168966502403 139856096692989253449753605)
      ·
        refine ⟨26223018129935485021828801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139856096692989253449753605 26223018129935485021828801)
        ·
          refine ⟨19667263597451613766371601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26223018129935485021828801 19667263597451613766371601)
          ·
            refine ⟨14750447698088710324778701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19667263597451613766371601 14750447698088710324778701)
            ·
              refine ⟨5531417886783266371792013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14750447698088710324778701 5531417886783266371792013)
              ·
                refine ⟨2074281707543724889422005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5531417886783266371792013 2074281707543724889422005)
                ·
                  refine ⟨194463910082224208383313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2074281707543724889422005 194463910082224208383313)
                  ·
                    rfl

theorem cell22_1704227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 5].length) (baseStart_1704227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704227 prefixEnd_1704227 := by exact prefixLift 1704227
  have htrace : WordTrace (prefixWord ++ tailWord_1704227) baseStart_1704227 baseEnd_1704227 := by
    simpa [prefixWord, tailWord_1704227, baseEnd_1704227] using wordTrace_append hprefix tailTrace_1704227
  have hstable : (prefixWord ++ tailWord_1704227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704227).length < 2 ^ (prefixWord ++ tailWord_1704227).sum := by decide
  have hdescent : baseEnd_1704227 < baseStart_1704227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704287 : List Nat := [1, 1, 2, 3, 1, 2, 3, 3, 1, 5]
def baseStart_1704287 : Nat := 118140960795 + 1704287 * 2 ^ 59
def prefixEnd_1704287 : Nat := 4983230072969 + 3 ^ 40 * 1704287 * 2
def baseEnd_1704287 : Nat := 583412269472852468649755

theorem tailTrace_1704287 : CollatzResearch.WordTrace tailWord_1704287 prefixEnd_1704287 583412269472852468649755 := by
  unfold tailWord_1704287
  simp only [CollatzResearch.WordTrace]
  refine ⟨62160453576666742891519115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41440302384444495261012743 62160453576666742891519115)
  ·
    refine ⟨93240680365000114337278673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62160453576666742891519115 93240680365000114337278673)
    ·
      refine ⟨69930510273750085752959005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93240680365000114337278673 69930510273750085752959005)
      ·
        refine ⟨26223941352656282157359627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69930510273750085752959005 26223941352656282157359627)
        ·
          refine ⟨39335912028984423236039441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26223941352656282157359627 39335912028984423236039441)
          ·
            refine ⟨29501934021738317427029581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39335912028984423236039441 29501934021738317427029581)
            ·
              refine ⟨11063225258151869035136093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29501934021738317427029581 11063225258151869035136093)
              ·
                refine ⟨4148709471806950888176035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11063225258151869035136093 4148709471806950888176035)
                ·
                  refine ⟨6223064207710426332264053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4148709471806950888176035 6223064207710426332264053)
                  ·
                    refine ⟨583412269472852468649755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6223064207710426332264053 583412269472852468649755)
                    ·
                      rfl

theorem cell22_1704287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 5].length) (baseStart_1704287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704287 prefixEnd_1704287 := by exact prefixLift 1704287
  have htrace : WordTrace (prefixWord ++ tailWord_1704287) baseStart_1704287 baseEnd_1704287 := by
    simpa [prefixWord, tailWord_1704287, baseEnd_1704287] using wordTrace_append hprefix tailTrace_1704287
  have hstable : (prefixWord ++ tailWord_1704287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704287).length < 2 ^ (prefixWord ++ tailWord_1704287).sum := by decide
  have hdescent : baseEnd_1704287 < baseStart_1704287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704306 : List Nat := [3, 2, 1, 2, 1, 4, 2, 3, 4]
def baseStart_1704306 : Nat := 118140960795 + 1704306 * 2 ^ 59
def prefixEnd_1704306 : Nat := 4983230072969 + 3 ^ 40 * 1704306 * 2
def baseEnd_1704306 : Nat := 194472924520380917474899

theorem tailTrace_1704306 : CollatzResearch.WordTrace tailWord_1704306 prefixEnd_1704306 194472924520380917474899 := by
  unfold tailWord_1704306
  simp only [CollatzResearch.WordTrace]
  refine ⟨15540286640899477284115193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41440764375731939424307181 15540286640899477284115193)
  ·
    refine ⟨11655214980674607963086395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15540286640899477284115193 11655214980674607963086395)
    ·
      refine ⟨17482822471011911944629593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11655214980674607963086395 17482822471011911944629593)
      ·
        refine ⟨13112116853258933958472195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17482822471011911944629593 13112116853258933958472195)
        ·
          refine ⟨19668175279888400937708293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13112116853258933958472195 19668175279888400937708293)
          ·
            refine ⟨3687782864979075175820305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19668175279888400937708293 3687782864979075175820305)
            ·
              refine ⟨2765837148734306381865229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3687782864979075175820305 2765837148734306381865229)
              ·
                refine ⟨1037188930775364893199461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2765837148734306381865229 1037188930775364893199461)
                ·
                  refine ⟨194472924520380917474899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1037188930775364893199461 194472924520380917474899)
                  ·
                    rfl

theorem cell22_1704306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_1704306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704306 prefixEnd_1704306 := by exact prefixLift 1704306
  have htrace : WordTrace (prefixWord ++ tailWord_1704306) baseStart_1704306 baseEnd_1704306 := by
    simpa [prefixWord, tailWord_1704306, baseEnd_1704306] using wordTrace_append hprefix tailTrace_1704306
  have hstable : (prefixWord ++ tailWord_1704306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704306).length < 2 ^ (prefixWord ++ tailWord_1704306).sum := by decide
  have hdescent : baseEnd_1704306 < baseStart_1704306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704317 : List Nat := [1, 4, 1, 1, 2, 4, 9]
def baseStart_1704317 : Nat := 118140960795 + 1704317 * 2 ^ 59
def prefixEnd_1704317 : Nat := 4983230072969 + 3 ^ 40 * 1704317 * 2
def baseEnd_1704317 : Nat := 21608242188368236681469

theorem tailTrace_1704317 : CollatzResearch.WordTrace tailWord_1704317 prefixEnd_1704317 21608242188368236681469 := by
  unfold tailWord_1704317
  simp only [CollatzResearch.WordTrace]
  refine ⟨62161547766558058015111205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41441031844372038676740803 62161547766558058015111205)
  ·
    refine ⟨11655290206229635877833351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62161547766558058015111205 11655290206229635877833351)
    ·
      refine ⟨17482935309344453816750027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11655290206229635877833351 17482935309344453816750027)
      ·
        refine ⟨26224402964016680725125041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17482935309344453816750027 26224402964016680725125041)
        ·
          refine ⟨19668302223012510543843781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26224402964016680725125041 19668302223012510543843781)
          ·
            refine ⟨3687806666814845726970709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19668302223012510543843781 3687806666814845726970709)
            ·
              refine ⟨21608242188368236681469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3687806666814845726970709 21608242188368236681469)
              ·
                rfl

theorem cell22_1704317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 9].length) (baseStart_1704317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704317 prefixEnd_1704317 := by exact prefixLift 1704317
  have htrace : WordTrace (prefixWord ++ tailWord_1704317) baseStart_1704317 baseEnd_1704317 := by
    simpa [prefixWord, tailWord_1704317, baseEnd_1704317] using wordTrace_append hprefix tailTrace_1704317
  have hstable : (prefixWord ++ tailWord_1704317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704317).length < 2 ^ (prefixWord ++ tailWord_1704317).sum := by decide
  have hdescent : baseEnd_1704317 < baseStart_1704317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704321 : List Nat := [1, 2, 4, 3, 1, 2, 1, 1, 4, 3]
def baseStart_1704321 : Nat := 118140960795 + 1704321 * 2 ^ 59
def prefixEnd_1704321 : Nat := 4983230072969 + 3 ^ 40 * 1704321 * 2
def baseEnd_1704321 : Nat := 583423908367687713299651

theorem tailTrace_1704321 : CollatzResearch.WordTrace tailWord_1704321 prefixEnd_1704321 583423908367687713299651 := by
  unfold tailWord_1704321
  simp only [CollatzResearch.WordTrace]
  refine ⟨62161693658543566698256817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41441129105695711132171211 62161693658543566698256817)
  ·
    refine ⟨46621270243907675023692613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62161693658543566698256817 46621270243907675023692613)
    ·
      refine ⟨8741488170732689066942365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46621270243907675023692613 8741488170732689066942365)
      ·
        refine ⟨3278058064024758400103387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8741488170732689066942365 3278058064024758400103387)
        ·
          refine ⟨4917087096037137600155081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3278058064024758400103387 4917087096037137600155081)
          ·
            refine ⟨3687815322027853200116311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4917087096037137600155081 3687815322027853200116311)
            ·
              refine ⟨5531722983041779800174467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3687815322027853200116311 5531722983041779800174467)
              ·
                refine ⟨8297584474562669700261701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5531722983041779800174467 8297584474562669700261701)
                ·
                  refine ⟨1555797088980500568799069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8297584474562669700261701 1555797088980500568799069)
                  ·
                    refine ⟨583423908367687713299651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1555797088980500568799069 583423908367687713299651)
                    ·
                      rfl

theorem cell22_1704321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_1704321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704321 prefixEnd_1704321 := by exact prefixLift 1704321
  have htrace : WordTrace (prefixWord ++ tailWord_1704321) baseStart_1704321 baseEnd_1704321 := by
    simpa [prefixWord, tailWord_1704321, baseEnd_1704321] using wordTrace_append hprefix tailTrace_1704321
  have hstable : (prefixWord ++ tailWord_1704321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704321).length < 2 ^ (prefixWord ++ tailWord_1704321).sum := by decide
  have hdescent : baseEnd_1704321 < baseStart_1704321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704342 : List Nat := [5, 3, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_1704342 : Nat := 118140960795 + 1704342 * 2 ^ 59
def prefixEnd_1704342 : Nat := 4983230072969 + 3 ^ 40 * 1704342 * 2
def baseEnd_1704342 : Nat := 583431097096850658524587

theorem tailTrace_1704342 : CollatzResearch.WordTrace tailWord_1704342 prefixEnd_1704342 583431097096850658524587 := by
  unfold tailWord_1704342
  simp only [CollatzResearch.WordTrace]
  refine ⟨3885153724466717955298205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41441639727644991523180853 3885153724466717955298205)
  ·
    refine ⟨1456932646675019233236827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3885153724466717955298205 1456932646675019233236827)
    ·
      refine ⟨2185398970012528849855241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1456932646675019233236827 2185398970012528849855241)
      ·
        refine ⟨1639049227509396637391431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2185398970012528849855241 1639049227509396637391431)
        ·
          refine ⟨2458573841264094956087147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1639049227509396637391431 2458573841264094956087147)
          ·
            refine ⟨3687860761896142434130721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2458573841264094956087147 3687860761896142434130721)
            ·
              refine ⟨2765895571422106825598041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3687860761896142434130721 2765895571422106825598041)
              ·
                refine ⟨2074421678566580119198531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2765895571422106825598041 2074421678566580119198531)
                ·
                  refine ⟨3111632517849870178797797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2074421678566580119198531 3111632517849870178797797)
                  ·
                    refine ⟨583431097096850658524587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3111632517849870178797797 583431097096850658524587)
                    ·
                      rfl

theorem cell22_1704342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_1704342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704342 prefixEnd_1704342 := by exact prefixLift 1704342
  have htrace : WordTrace (prefixWord ++ tailWord_1704342) baseStart_1704342 baseEnd_1704342 := by
    simpa [prefixWord, tailWord_1704342, baseEnd_1704342] using wordTrace_append hprefix tailTrace_1704342
  have hstable : (prefixWord ++ tailWord_1704342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704342).length < 2 ^ (prefixWord ++ tailWord_1704342).sum := by decide
  have hdescent : baseEnd_1704342 < baseStart_1704342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704396 : List Nat := [2, 2, 1, 4, 3, 1, 1, 3, 5]
def baseStart_1704396 : Nat := 118140960795 + 1704396 * 2 ^ 59
def prefixEnd_1704396 : Nat := 4983230072969 + 3 ^ 40 * 1704396 * 2
def baseEnd_1704396 : Nat := 194483194133470839224807

theorem tailTrace_1704396 : CollatzResearch.WordTrace tailWord_1704396 prefixEnd_1704396 194483194133470839224807 := by
  unfold tailWord_1704396
  simp only [CollatzResearch.WordTrace]
  refine ⟨31082214566635927253618521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41442952755514569671491361 31082214566635927253618521)
  ·
    refine ⟨23311660924976945440213891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31082214566635927253618521 23311660924976945440213891)
    ·
      refine ⟨34967491387465418160320837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23311660924976945440213891 34967491387465418160320837)
      ·
        refine ⟨6556404635149765905060157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34967491387465418160320837 6556404635149765905060157)
        ·
          refine ⟨2458651738181162214397559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6556404635149765905060157 2458651738181162214397559)
          ·
            refine ⟨3687977607271743321596339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2458651738181162214397559 3687977607271743321596339)
            ·
              refine ⟨5531966410907614982394509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3687977607271743321596339 5531966410907614982394509)
              ·
                refine ⟨2074487404090355618397941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5531966410907614982394509 2074487404090355618397941)
                ·
                  refine ⟨194483194133470839224807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2074487404090355618397941 194483194133470839224807)
                  ·
                    rfl

theorem cell22_1704396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 5].length) (baseStart_1704396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704396 prefixEnd_1704396 := by exact prefixLift 1704396
  have htrace : WordTrace (prefixWord ++ tailWord_1704396) baseStart_1704396 baseEnd_1704396 := by
    simpa [prefixWord, tailWord_1704396, baseEnd_1704396] using wordTrace_append hprefix tailTrace_1704396
  have hstable : (prefixWord ++ tailWord_1704396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704396).length < 2 ^ (prefixWord ++ tailWord_1704396).sum := by decide
  have hdescent : baseEnd_1704396 < baseStart_1704396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704409 : List Nat := [1, 2, 1, 2, 4, 1, 3, 1, 3, 4]
def baseStart_1704409 : Nat := 118140960795 + 1704409 * 2 ^ 59
def prefixEnd_1704409 : Nat := 4983230072969 + 3 ^ 40 * 1704409 * 2
def baseEnd_1704409 : Nat := 583454032566084817099381

theorem tailTrace_1704409 : CollatzResearch.WordTrace tailWord_1704409 prefixEnd_1704409 583454032566084817099381 := by
  unfold tailWord_1704409
  simp only [CollatzResearch.WordTrace]
  refine ⟨62164903282224757727460281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41443268854816505151640187 62164903282224757727460281)
  ·
    refine ⟨46623677461668568295595211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62164903282224757727460281 46623677461668568295595211)
    ·
      refine ⟨69935516192502852443392817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46623677461668568295595211 69935516192502852443392817)
      ·
        refine ⟨52451637144377139332544613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69935516192502852443392817 52451637144377139332544613)
        ·
          refine ⟨9834681964570713624852115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52451637144377139332544613 9834681964570713624852115)
          ·
            refine ⟨14752022946856070437278173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9834681964570713624852115 14752022946856070437278173)
            ·
              refine ⟨5532008605071026413979315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14752022946856070437278173 5532008605071026413979315)
              ·
                refine ⟨8298012907606539620968973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5532008605071026413979315 8298012907606539620968973)
                ·
                  refine ⟨3111754840352452357863365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8298012907606539620968973 3111754840352452357863365)
                  ·
                    refine ⟨583454032566084817099381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3111754840352452357863365 583454032566084817099381)
                    ·
                      rfl

theorem cell22_1704409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 4].length) (baseStart_1704409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704409 prefixEnd_1704409 := by exact prefixLift 1704409
  have htrace : WordTrace (prefixWord ++ tailWord_1704409) baseStart_1704409 baseEnd_1704409 := by
    simpa [prefixWord, tailWord_1704409, baseEnd_1704409] using wordTrace_append hprefix tailTrace_1704409
  have hstable : (prefixWord ++ tailWord_1704409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704409).length < 2 ^ (prefixWord ++ tailWord_1704409).sum := by decide
  have hdescent : baseEnd_1704409 < baseStart_1704409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704434 : List Nat := [3, 2, 1, 4, 3, 1, 2, 2, 1, 3]
def baseStart_1704434 : Nat := 118140960795 + 1704434 * 2 ^ 59
def prefixEnd_1704434 : Nat := 4983230072969 + 3 ^ 40 * 1704434 * 2
def baseEnd_1704434 : Nat := 583462590576993085224305

theorem tailTrace_1704434 : CollatzResearch.WordTrace tailWord_1704434 prefixEnd_1704434 583462590576993085224305 := by
  unfold tailWord_1704434
  simp only [CollatzResearch.WordTrace]
  refine ⟨15541453776783546749280089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41443876738089457998080237 15541453776783546749280089)
  ·
    refine ⟨11656090332587660061960067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15541453776783546749280089 11656090332587660061960067)
    ·
      refine ⟨17484135498881490092940101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11656090332587660061960067 17484135498881490092940101)
      ·
        refine ⟨3278275406040279392426269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17484135498881490092940101 3278275406040279392426269)
        ·
          refine ⟨1229353277265104772159851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3278275406040279392426269 1229353277265104772159851)
          ·
            refine ⟨1844029915897657158239777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1229353277265104772159851 1844029915897657158239777)
            ·
              refine ⟨1383022436923242868679833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1844029915897657158239777 1383022436923242868679833)
              ·
                refine ⟨1037266827692432151509875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1383022436923242868679833 1037266827692432151509875)
                ·
                  refine ⟨1555900241538648227264813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1037266827692432151509875 1555900241538648227264813)
                  ·
                    refine ⟨583462590576993085224305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1555900241538648227264813 583462590576993085224305)
                    ·
                      rfl

theorem cell22_1704434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_1704434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704434 prefixEnd_1704434 := by exact prefixLift 1704434
  have htrace : WordTrace (prefixWord ++ tailWord_1704434) baseStart_1704434 baseEnd_1704434 := by
    simpa [prefixWord, tailWord_1704434, baseEnd_1704434] using wordTrace_append hprefix tailTrace_1704434
  have hstable : (prefixWord ++ tailWord_1704434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704434).length < 2 ^ (prefixWord ++ tailWord_1704434).sum := by decide
  have hdescent : baseEnd_1704434 < baseStart_1704434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704439 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 8, 3]
def baseStart_1704439 : Nat := 118140960795 + 1704439 * 2 ^ 59
def prefixEnd_1704439 : Nat := 4983230072969 + 3 ^ 40 * 1704439 * 2
def baseEnd_1704439 : Nat := 583464302179174738849289

theorem tailTrace_1704439 : CollatzResearch.WordTrace tailWord_1704439 prefixEnd_1704439 583464302179174738849289 := by
  unfold tailWord_1704439
  simp only [CollatzResearch.WordTrace]
  refine ⟨62165997472116072851052371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41443998314744048567368247 62165997472116072851052371)
  ·
    refine ⟨93248996208174109276578557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62165997472116072851052371 93248996208174109276578557)
    ·
      refine ⟨34968373578065290978716959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93248996208174109276578557 34968373578065290978716959)
      ·
        refine ⟨52452560367097936468075439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34968373578065290978716959 52452560367097936468075439)
        ·
          refine ⟨78678840550646904702113159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52452560367097936468075439 78678840550646904702113159)
          ·
            refine ⟨118018260825970357053169739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78678840550646904702113159 118018260825970357053169739)
            ·
              refine ⟨177027391238955535579754609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118018260825970357053169739 177027391238955535579754609)
              ·
                refine ⟨132770543429216651684815957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177027391238955535579754609 132770543429216651684815957)
                ·
                  refine ⟨1555904805811132636931437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 132770543429216651684815957 1555904805811132636931437)
                  ·
                    refine ⟨583464302179174738849289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1555904805811132636931437 583464302179174738849289)
                    ·
                      rfl

theorem cell22_1704439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 3].length) (baseStart_1704439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704439 prefixEnd_1704439 := by exact prefixLift 1704439
  have htrace : WordTrace (prefixWord ++ tailWord_1704439) baseStart_1704439 baseEnd_1704439 := by
    simpa [prefixWord, tailWord_1704439, baseEnd_1704439] using wordTrace_append hprefix tailTrace_1704439
  have hstable : (prefixWord ++ tailWord_1704439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704439).length < 2 ^ (prefixWord ++ tailWord_1704439).sum := by decide
  have hdescent : baseEnd_1704439 < baseStart_1704439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704490 : List Nat := [3, 1, 4, 1, 1, 4, 1, 2, 2, 3]
def baseStart_1704490 : Nat := 118140960795 + 1704490 * 2 ^ 59
def prefixEnd_1704490 : Nat := 4983230072969 + 3 ^ 40 * 1704490 * 2
def baseEnd_1704490 : Nat := 583481760521427605824133

theorem tailTrace_1704490 : CollatzResearch.WordTrace tailWord_1704490 prefixEnd_1704490 583481760521427605824133 := by
  unfold tailWord_1704490
  simp only [CollatzResearch.WordTrace]
  refine ⟨15541964398732827140289731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41445238396620872374105949 15541964398732827140289731)
  ·
    refine ⟨23312946598099240710434597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15541964398732827140289731 23312946598099240710434597)
    ·
      refine ⟨4371177487143607633206487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23312946598099240710434597 4371177487143607633206487)
      ·
        refine ⟨6556766230715411449809731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4371177487143607633206487 6556766230715411449809731)
        ·
          refine ⟨9835149346073117174714597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6556766230715411449809731 9835149346073117174714597)
          ·
            refine ⟨1844090502388709470258987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9835149346073117174714597 1844090502388709470258987)
            ·
              refine ⟨2766135753583064205388481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1844090502388709470258987 2766135753583064205388481)
              ·
                refine ⟨2074601815187298154041361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2766135753583064205388481 2074601815187298154041361)
                ·
                  refine ⟨1555951361390473615531021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2074601815187298154041361 1555951361390473615531021)
                  ·
                    refine ⟨583481760521427605824133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1555951361390473615531021 583481760521427605824133)
                    ·
                      rfl

theorem cell22_1704490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_1704490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704490 prefixEnd_1704490 := by exact prefixLift 1704490
  have htrace : WordTrace (prefixWord ++ tailWord_1704490) baseStart_1704490 baseEnd_1704490 := by
    simpa [prefixWord, tailWord_1704490, baseEnd_1704490] using wordTrace_append hprefix tailTrace_1704490
  have hstable : (prefixWord ++ tailWord_1704490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704490).length < 2 ^ (prefixWord ++ tailWord_1704490).sum := by decide
  have hdescent : baseEnd_1704490 < baseStart_1704490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704552 : List Nat := [2, 1, 4, 3, 3, 1, 1, 1, 3, 3]
def baseStart_1704552 : Nat := 118140960795 + 1704552 * 2 ^ 59
def prefixEnd_1704552 : Nat := 4983230072969 + 3 ^ 40 * 1704552 * 2
def baseEnd_1704552 : Nat := 583502984388480110773943

theorem tailTrace_1704552 : CollatzResearch.WordTrace tailWord_1704552 prefixEnd_1704552 583502984388480110773943 := by
  unfold tailWord_1704552
  simp only [CollatzResearch.WordTrace]
  refine ⟨31085059460353346574957955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41446745947137795433277273 31085059460353346574957955)
  ·
    refine ⟨46627589190530019862436933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31085059460353346574957955 46627589190530019862436933)
    ·
      refine ⟨8742672973224378724206925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46627589190530019862436933 8742672973224378724206925)
      ·
        refine ⟨3278502364959142021577597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8742672973224378724206925 3278502364959142021577597)
        ·
          refine ⟨1229438386859678258091599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3278502364959142021577597 1229438386859678258091599)
          ·
            refine ⟨1844157580289517387137399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1229438386859678258091599 1844157580289517387137399)
            ·
              refine ⟨2766236370434276080706099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1844157580289517387137399 2766236370434276080706099)
              ·
                refine ⟨4149354555651414121059149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2766236370434276080706099 4149354555651414121059149)
                ·
                  refine ⟨1556007958369280295397181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4149354555651414121059149 1556007958369280295397181)
                  ·
                    refine ⟨583502984388480110773943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1556007958369280295397181 583502984388480110773943)
                    ·
                      rfl

theorem cell22_1704552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_1704552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704552 prefixEnd_1704552 := by exact prefixLift 1704552
  have htrace : WordTrace (prefixWord ++ tailWord_1704552) baseStart_1704552 baseEnd_1704552 := by
    simpa [prefixWord, tailWord_1704552, baseEnd_1704552] using wordTrace_append hprefix tailTrace_1704552
  have hstable : (prefixWord ++ tailWord_1704552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704552).length < 2 ^ (prefixWord ++ tailWord_1704552).sum := by decide
  have hdescent : baseEnd_1704552 < baseStart_1704552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704625 : List Nat := [1, 2, 2, 6, 1, 1, 2, 1, 1, 5]
def baseStart_1704625 : Nat := 118140960795 + 1704625 * 2 ^ 59
def prefixEnd_1704625 : Nat := 4983230072969 + 3 ^ 40 * 1704625 * 2
def baseEnd_1704625 : Nat := 583527973780332253698719

theorem tailTrace_1704625 : CollatzResearch.WordTrace tailWord_1704625 prefixEnd_1704625 583527973780332253698719 := by
  unfold tailWord_1704625
  simp only [CollatzResearch.WordTrace]
  refine ⟨62172781449442226617323329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41448520966294817744882219 62172781449442226617323329)
  ·
    refine ⟨46629586087081669962992497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62172781449442226617323329 46629586087081669962992497)
    ·
      refine ⟨34972189565311252472244373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46629586087081669962992497 34972189565311252472244373)
      ·
        refine ⟨1639321385873964959636455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34972189565311252472244373 1639321385873964959636455)
        ·
          refine ⟨2458982078810947439454683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1639321385873964959636455 2458982078810947439454683)
          ·
            refine ⟨3688473118216421159182025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2458982078810947439454683 3688473118216421159182025)
            ·
              refine ⟨2766354838662315869386519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3688473118216421159182025 2766354838662315869386519)
              ·
                refine ⟨4149532257993473804079779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2766354838662315869386519 4149532257993473804079779)
                ·
                  refine ⟨6224298386990210706119669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4149532257993473804079779 6224298386990210706119669)
                  ·
                    refine ⟨583527973780332253698719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6224298386990210706119669 583527973780332253698719)
                    ·
                      rfl

theorem cell22_1704625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 5].length) (baseStart_1704625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704625 prefixEnd_1704625 := by exact prefixLift 1704625
  have htrace : WordTrace (prefixWord ++ tailWord_1704625) baseStart_1704625 baseEnd_1704625 := by
    simpa [prefixWord, tailWord_1704625, baseEnd_1704625] using wordTrace_append hprefix tailTrace_1704625
  have hstable : (prefixWord ++ tailWord_1704625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704625).length < 2 ^ (prefixWord ++ tailWord_1704625).sum := by decide
  have hdescent : baseEnd_1704625 < baseStart_1704625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704638 : List Nat := [4, 2, 1, 1, 2, 1, 5, 6]
def baseStart_1704638 : Nat := 118140960795 + 1704638 * 2 ^ 59
def prefixEnd_1704638 : Nat := 4983230072969 + 3 ^ 40 * 1704638 * 2
def baseEnd_1704638 : Nat := 64836935994000505902631

theorem tailTrace_1704638 : CollatzResearch.WordTrace tailWord_1704638 prefixEnd_1704638 64836935994000505902631 := by
  unfold tailWord_1704638
  simp only [CollatzResearch.WordTrace]
  refine ⟨7771656949799391229693321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41448837065596753225031045 7771656949799391229693321)
  ·
    refine ⟨5828742712349543422269991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7771656949799391229693321 5828742712349543422269991)
    ·
      refine ⟨8743114068524315133404987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5828742712349543422269991 8743114068524315133404987)
      ·
        refine ⟨13114671102786472700107481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8743114068524315133404987 13114671102786472700107481)
        ·
          refine ⟨9836003327089854525080611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13114671102786472700107481 9836003327089854525080611)
          ·
            refine ⟨14754004990634781787620917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9836003327089854525080611 14754004990634781787620917)
            ·
              refine ⟨1383187967872010792589461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14754004990634781787620917 1383187967872010792589461)
              ·
                refine ⟨64836935994000505902631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1383187967872010792589461 64836935994000505902631)
                ·
                  rfl

theorem cell22_1704638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_1704638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704638 prefixEnd_1704638 := by exact prefixLift 1704638
  have htrace : WordTrace (prefixWord ++ tailWord_1704638) baseStart_1704638 baseEnd_1704638 := by
    simpa [prefixWord, tailWord_1704638, baseEnd_1704638] using wordTrace_append hprefix tailTrace_1704638
  have hstable : (prefixWord ++ tailWord_1704638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704638).length < 2 ^ (prefixWord ++ tailWord_1704638).sum := by decide
  have hdescent : baseEnd_1704638 < baseStart_1704638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704646 : List Nat := [6, 1, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_1704646 : Nat := 118140960795 + 1704646 * 2 ^ 59
def prefixEnd_1704646 : Nat := 4983230072969 + 3 ^ 40 * 1704646 * 2
def baseEnd_1704646 : Nat := 583535162509495198923655

theorem tailTrace_1704646 : CollatzResearch.WordTrace tailWord_1704646 prefixEnd_1704646 583535162509495198923655 := by
  unfold tailWord_1704646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1942923355698942100119931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41449031588244098135891861 1942923355698942100119931)
  ·
    refine ⟨2914385033548413150179897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1942923355698942100119931 2914385033548413150179897)
    ·
      refine ⟨2185788775161309862634923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2914385033548413150179897 2185788775161309862634923)
      ·
        refine ⟨3278683162741964793952385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2185788775161309862634923 3278683162741964793952385)
        ·
          refine ⟨2459012372056473595464289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3278683162741964793952385 2459012372056473595464289)
          ·
            refine ⟨1844259279042355196598217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2459012372056473595464289 1844259279042355196598217)
            ·
              refine ⟨1383194459281766397448663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1844259279042355196598217 1383194459281766397448663)
              ·
                refine ⟨2074791688922649596172995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1383194459281766397448663 2074791688922649596172995)
                ·
                  refine ⟨3112187533383974394259493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2074791688922649596172995 3112187533383974394259493)
                  ·
                    refine ⟨583535162509495198923655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3112187533383974394259493 583535162509495198923655)
                    ·
                      rfl

theorem cell22_1704646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_1704646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704646 prefixEnd_1704646 := by exact prefixLift 1704646
  have htrace : WordTrace (prefixWord ++ tailWord_1704646) baseStart_1704646 baseEnd_1704646 := by
    simpa [prefixWord, tailWord_1704646, baseEnd_1704646] using wordTrace_append hprefix tailTrace_1704646
  have hstable : (prefixWord ++ tailWord_1704646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704646).length < 2 ^ (prefixWord ++ tailWord_1704646).sum := by decide
  have hdescent : baseEnd_1704646 < baseStart_1704646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704666 : List Nat := [3, 1, 1, 2, 2, 2, 3, 1, 7]
def baseStart_1704666 : Nat := 118140960795 + 1704666 * 2 ^ 59
def prefixEnd_1704666 : Nat := 4983230072969 + 3 ^ 40 * 1704666 * 2
def baseEnd_1704666 : Nat := 194514002972740604474531

theorem tailTrace_1704666 : CollatzResearch.WordTrace tailWord_1704666 prefixEnd_1704666 194514002972740604474531 := by
  unfold tailWord_1704666
  simp only [CollatzResearch.WordTrace]
  refine ⟨15543569210573422654891463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41449517894862460413043901 15543569210573422654891463)
  ·
    refine ⟨23315353815860133982337195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15543569210573422654891463 23315353815860133982337195)
    ·
      refine ⟨34973030723790200973505793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23315353815860133982337195 34973030723790200973505793)
      ·
        refine ⟨26229773042842650730129345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34973030723790200973505793 26229773042842650730129345)
        ·
          refine ⟨19672329782131988047597009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26229773042842650730129345 19672329782131988047597009)
          ·
            refine ⟨14754247336598991035697757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19672329782131988047597009 14754247336598991035697757)
            ·
              refine ⟨5532842751224621638386659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14754247336598991035697757 5532842751224621638386659)
              ·
                refine ⟨8299264126836932457579989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5532842751224621638386659 8299264126836932457579989)
                ·
                  refine ⟨194514002972740604474531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8299264126836932457579989 194514002972740604474531)
                  ·
                    rfl

theorem cell22_1704666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_1704666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704666 prefixEnd_1704666 := by exact prefixLift 1704666
  have htrace : WordTrace (prefixWord ++ tailWord_1704666) baseStart_1704666 baseEnd_1704666 := by
    simpa [prefixWord, tailWord_1704666, baseEnd_1704666] using wordTrace_append hprefix tailTrace_1704666
  have hstable : (prefixWord ++ tailWord_1704666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704666).length < 2 ^ (prefixWord ++ tailWord_1704666).sum := by decide
  have hdescent : baseEnd_1704666 < baseStart_1704666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704681 : List Nat := [1, 2, 1, 1, 1, 2, 6, 1, 2, 5]
def baseStart_1704681 : Nat := 118140960795 + 1704681 * 2 ^ 59
def prefixEnd_1704681 : Nat := 4983230072969 + 3 ^ 40 * 1704681 * 2
def baseEnd_1704681 : Nat := 583547143724766774298547

theorem tailTrace_1704681 : CollatzResearch.WordTrace tailWord_1704681 prefixEnd_1704681 583547143724766774298547 := by
  unfold tailWord_1704681
  simp only [CollatzResearch.WordTrace]
  refine ⟨62174823937239348181361897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41449882624826232120907931 62174823937239348181361897)
  ·
    refine ⟨46631117952929511136021423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62174823937239348181361897 46631117952929511136021423)
    ·
      refine ⟨69946676929394266704032135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46631117952929511136021423 69946676929394266704032135)
      ·
        refine ⟨104920015394091400056048203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69946676929394266704032135 104920015394091400056048203)
        ·
          refine ⟨157380023091137100084072305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104920015394091400056048203 157380023091137100084072305)
          ·
            refine ⟨118035017318352825063054229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157380023091137100084072305 118035017318352825063054229)
            ·
              refine ⟨5532891436797788674830667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118035017318352825063054229 5532891436797788674830667)
              ·
                refine ⟨8299337155196683012246001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5532891436797788674830667 8299337155196683012246001)
                ·
                  refine ⟨6224502866397512259184501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8299337155196683012246001 6224502866397512259184501)
                  ·
                    refine ⟨583547143724766774298547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6224502866397512259184501 583547143724766774298547)
                    ·
                      rfl

theorem cell22_1704681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 5].length) (baseStart_1704681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704681 prefixEnd_1704681 := by exact prefixLift 1704681
  have htrace : WordTrace (prefixWord ++ tailWord_1704681) baseStart_1704681 baseEnd_1704681 := by
    simpa [prefixWord, tailWord_1704681, baseEnd_1704681] using wordTrace_append hprefix tailTrace_1704681
  have hstable : (prefixWord ++ tailWord_1704681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704681).length < 2 ^ (prefixWord ++ tailWord_1704681).sum := by decide
  have hdescent : baseEnd_1704681 < baseStart_1704681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704713 : List Nat := [1, 2, 1, 1, 3, 2, 4, 3, 1, 4]
def baseStart_1704713 : Nat := 118140960795 + 1704713 * 2 ^ 59
def prefixEnd_1704713 : Nat := 4983230072969 + 3 ^ 40 * 1704713 * 2
def baseEnd_1704713 : Nat := 583558097978729357498449

theorem tailTrace_1704713 : CollatzResearch.WordTrace tailWord_1704713 prefixEnd_1704713 583558097978729357498449 := by
  unfold tailWord_1704713
  simp only [CollatzResearch.WordTrace]
  refine ⟨62175991073123417646526793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41450660715415611764351195 62175991073123417646526793)
  ·
    refine ⟨46631993304842563234895095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62175991073123417646526793 46631993304842563234895095)
    ·
      refine ⟨69947989957263844852342643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46631993304842563234895095 69947989957263844852342643)
      ·
        refine ⟨104921984935895767278513965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69947989957263844852342643 104921984935895767278513965)
        ·
          refine ⟨39345744350960912729442737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104921984935895767278513965 39345744350960912729442737)
          ·
            refine ⟨29509308263220684547082053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39345744350960912729442737 29509308263220684547082053)
            ·
              refine ⟨5532995299353878352577885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29509308263220684547082053 5532995299353878352577885)
              ·
                refine ⟨2074873237257704382216707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5532995299353878352577885 2074873237257704382216707)
                ·
                  refine ⟨3112309855886556573325061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2074873237257704382216707 3112309855886556573325061)
                  ·
                    refine ⟨583558097978729357498449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3112309855886556573325061 583558097978729357498449)
                    ·
                      rfl

theorem cell22_1704713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 4].length) (baseStart_1704713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704713 prefixEnd_1704713 := by exact prefixLift 1704713
  have htrace : WordTrace (prefixWord ++ tailWord_1704713) baseStart_1704713 baseEnd_1704713 := by
    simpa [prefixWord, tailWord_1704713, baseEnd_1704713] using wordTrace_append hprefix tailTrace_1704713
  have hstable : (prefixWord ++ tailWord_1704713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704713).length < 2 ^ (prefixWord ++ tailWord_1704713).sum := by decide
  have hdescent : baseEnd_1704713 < baseStart_1704713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704852 : List Nat := [2, 4, 2, 1, 1, 1, 5, 1, 5]
def baseStart_1704852 : Nat := 118140960795 + 1704852 * 2 ^ 59
def prefixEnd_1704852 : Nat := 4983230072969 + 3 ^ 40 * 1704852 * 2
def baseEnd_1704852 : Nat := 194535226839793109424341

theorem tailTrace_1704852 : CollatzResearch.WordTrace tailWord_1704852 prefixEnd_1704852 194535226839793109424341 := by
  unfold tailWord_1704852
  simp only [CollatzResearch.WordTrace]
  refine ⟨31090530409809922192918405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41454040546413229590557873 31090530409809922192918405)
  ·
    refine ⟨5829474451839360411172201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31090530409809922192918405 5829474451839360411172201)
    ·
      refine ⟨4372105838879520308379151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5829474451839360411172201 4372105838879520308379151)
      ·
        refine ⟨6558158758319280462568727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4372105838879520308379151 6558158758319280462568727)
        ·
          refine ⟨9837238137478920693853091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6558158758319280462568727 9837238137478920693853091)
          ·
            refine ⟨14755857206218381040779637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9837238137478920693853091 14755857206218381040779637)
            ·
              refine ⟨1383361613082973222573091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14755857206218381040779637 1383361613082973222573091)
              ·
                refine ⟨2075042419624459833859637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1383361613082973222573091 2075042419624459833859637)
                ·
                  refine ⟨194535226839793109424341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2075042419624459833859637 194535226839793109424341)
                  ·
                    rfl

theorem cell22_1704852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_1704852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704852 prefixEnd_1704852 := by exact prefixLift 1704852
  have htrace : WordTrace (prefixWord ++ tailWord_1704852) baseStart_1704852 baseEnd_1704852 := by
    simpa [prefixWord, tailWord_1704852, baseEnd_1704852] using wordTrace_append hprefix tailTrace_1704852
  have hstable : (prefixWord ++ tailWord_1704852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704852).length < 2 ^ (prefixWord ++ tailWord_1704852).sum := by decide
  have hdescent : baseEnd_1704852 < baseStart_1704852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704925 : List Nat := [1, 4, 3, 1, 2, 1, 2, 8]
def baseStart_1704925 : Nat := 118140960795 + 1704925 * 2 ^ 59
def prefixEnd_1704925 : Nat := 4983230072969 + 3 ^ 40 * 1704925 * 2
def baseEnd_1704925 : Nat := 64847852212359052355311

theorem tailTrace_1704925 : CollatzResearch.WordTrace tailWord_1704925 prefixEnd_1704925 64847852212359052355311 := by
  unfold tailWord_1704925
  simp only [CollatzResearch.WordTrace]
  refine ⟨62183723348355377853244229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41455815565570251902162819 62183723348355377853244229)
  ·
    refine ⟨11659448127816633347483293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62183723348355377853244229 11659448127816633347483293)
    ·
      refine ⟨4372293047931237505306235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11659448127816633347483293 4372293047931237505306235)
      ·
        refine ⟨6558439571896856257959353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4372293047931237505306235 6558439571896856257959353)
        ·
          refine ⟨4918829678922642193469515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6558439571896856257959353 4918829678922642193469515)
          ·
            refine ⟨7378244518383963290204273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4918829678922642193469515 7378244518383963290204273)
            ·
              refine ⟨5533683388787972467653205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7378244518383963290204273 5533683388787972467653205)
              ·
                refine ⟨64847852212359052355311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5533683388787972467653205 64847852212359052355311)
                ·
                  rfl

theorem cell22_1704925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 8].length) (baseStart_1704925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704925 prefixEnd_1704925 := by exact prefixLift 1704925
  have htrace : WordTrace (prefixWord ++ tailWord_1704925) baseStart_1704925 baseEnd_1704925 := by
    simpa [prefixWord, tailWord_1704925, baseEnd_1704925] using wordTrace_append hprefix tailTrace_1704925
  have hstable : (prefixWord ++ tailWord_1704925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704925).length < 2 ^ (prefixWord ++ tailWord_1704925).sum := by decide
  have hdescent : baseEnd_1704925 < baseStart_1704925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704927 : List Nat := [1, 1, 2, 3, 5, 1, 2, 1, 2, 4]
def baseStart_1704927 : Nat := 118140960795 + 1704927 * 2 ^ 59
def prefixEnd_1704927 : Nat := 4983230072969 + 3 ^ 40 * 1704927 * 2
def baseEnd_1704927 : Nat := 583631354552104132647793

theorem tailTrace_1704927 : CollatzResearch.WordTrace tailWord_1704927 prefixEnd_1704927 583631354552104132647793 := by
  unfold tailWord_1704927
  simp only [CollatzResearch.WordTrace]
  refine ⟨62183796294348132194817035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41455864196232088129878023 62183796294348132194817035)
  ·
    refine ⟨93275694441522198292225553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62183796294348132194817035 93275694441522198292225553)
    ·
      refine ⟨69956770831141648719169165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93275694441522198292225553 69956770831141648719169165)
      ·
        refine ⟨26233789061678118269688437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69956770831141648719169165 26233789061678118269688437)
        ·
          refine ⟨2459417724532323587783291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26233789061678118269688437 2459417724532323587783291)
          ·
            refine ⟨3689126586798485381674937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2459417724532323587783291 3689126586798485381674937)
            ·
              refine ⟨2766844940098864036256203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3689126586798485381674937 2766844940098864036256203)
              ·
                refine ⟨4150267410148296054384305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2766844940098864036256203 4150267410148296054384305)
                ·
                  refine ⟨3112700557611222040788229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4150267410148296054384305 3112700557611222040788229)
                  ·
                    refine ⟨583631354552104132647793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3112700557611222040788229 583631354552104132647793)
                    ·
                      rfl

theorem cell22_1704927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 4].length) (baseStart_1704927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704927 prefixEnd_1704927 := by exact prefixLift 1704927
  have htrace : WordTrace (prefixWord ++ tailWord_1704927) baseStart_1704927 baseEnd_1704927 := by
    simpa [prefixWord, tailWord_1704927, baseEnd_1704927] using wordTrace_append hprefix tailTrace_1704927
  have hstable : (prefixWord ++ tailWord_1704927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704927).length < 2 ^ (prefixWord ++ tailWord_1704927).sum := by decide
  have hdescent : baseEnd_1704927 < baseStart_1704927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704946 : List Nat := [3, 2, 1, 5, 1, 1, 2, 2, 2, 3]
def baseStart_1704946 : Nat := 118140960795 + 1704946 * 2 ^ 59
def prefixEnd_1704946 : Nat := 4983230072969 + 3 ^ 40 * 1704946 * 2
def baseEnd_1704946 : Nat := 583637858640394416422735

theorem tailTrace_1704946 : CollatzResearch.WordTrace tailWord_1704946 prefixEnd_1704946 583637858640394416422735 := by
  unfold tailWord_1704946
  simp only [CollatzResearch.WordTrace]
  refine ⟨15546122320319824609939673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41456326187519532293172461 15546122320319824609939673)
  ·
    refine ⟨11659591740239868457454755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15546122320319824609939673 11659591740239868457454755)
    ·
      refine ⟨17489387610359802686182133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11659591740239868457454755 17489387610359802686182133)
      ·
        refine ⟨1639630088471231501829575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17489387610359802686182133 1639630088471231501829575)
        ·
          refine ⟨2459445132706847252744363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1639630088471231501829575 2459445132706847252744363)
          ·
            refine ⟨3689167699060270879116545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2459445132706847252744363 3689167699060270879116545)
            ·
              refine ⟨2766875774295203159337409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3689167699060270879116545 2766875774295203159337409)
              ·
                refine ⟨2075156830721402369503057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2766875774295203159337409 2075156830721402369503057)
                ·
                  refine ⟨1556367623041051777127293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2075156830721402369503057 1556367623041051777127293)
                  ·
                    refine ⟨583637858640394416422735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1556367623041051777127293 583637858640394416422735)
                    ·
                      rfl

theorem cell22_1704946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_1704946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704946 prefixEnd_1704946 := by exact prefixLift 1704946
  have htrace : WordTrace (prefixWord ++ tailWord_1704946) baseStart_1704946 baseEnd_1704946 := by
    simpa [prefixWord, tailWord_1704946, baseEnd_1704946] using wordTrace_append hprefix tailTrace_1704946
  have hstable : (prefixWord ++ tailWord_1704946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704946).length < 2 ^ (prefixWord ++ tailWord_1704946).sum := by decide
  have hdescent : baseEnd_1704946 < baseStart_1704946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704978 : List Nat := [3, 2, 5, 1, 1, 2, 1, 1, 2, 4]
def baseStart_1704978 : Nat := 118140960795 + 1704978 * 2 ^ 59
def prefixEnd_1704978 : Nat := 4983230072969 + 3 ^ 40 * 1704978 * 2
def baseEnd_1704978 : Nat := 583648812894356999622637

theorem tailTrace_1704978 : CollatzResearch.WordTrace tailWord_1704978 prefixEnd_1704978 583648812894356999622637 := by
  unfold tailWord_1704978
  simp only [CollatzResearch.WordTrace]
  refine ⟨15546414104290841976230897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41457104278108911936615725 15546414104290841976230897)
  ·
    refine ⟨11659810578218131482173173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15546414104290841976230897 11659810578218131482173173)
    ·
      refine ⟨1093107241707949826453735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11659810578218131482173173 1093107241707949826453735)
      ·
        refine ⟨1639660862561924739680603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1093107241707949826453735 1639660862561924739680603)
        ·
          refine ⟨2459491293842887109520905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1639660862561924739680603 2459491293842887109520905)
          ·
            refine ⟨1844618470382165332140679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2459491293842887109520905 1844618470382165332140679)
            ·
              refine ⟨2766927705573247998211019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1844618470382165332140679 2766927705573247998211019)
              ·
                refine ⟨4150391558359871997316529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2766927705573247998211019 4150391558359871997316529)
                ·
                  refine ⟨3112793668769903997987397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4150391558359871997316529 3112793668769903997987397)
                  ·
                    refine ⟨583648812894356999622637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3112793668769903997987397 583648812894356999622637)
                    ·
                      rfl

theorem cell22_1704978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_1704978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1704978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1704978 prefixEnd_1704978 := by exact prefixLift 1704978
  have htrace : WordTrace (prefixWord ++ tailWord_1704978) baseStart_1704978 baseEnd_1704978 := by
    simpa [prefixWord, tailWord_1704978, baseEnd_1704978] using wordTrace_append hprefix tailTrace_1704978
  have hstable : (prefixWord ++ tailWord_1704978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704978).length < 2 ^ (prefixWord ++ tailWord_1704978).sum := by decide
  have hdescent : baseEnd_1704978 < baseStart_1704978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705045 : List Nat := [1, 3, 2, 2, 1, 2, 1, 3, 1, 6]
def baseStart_1705045 : Nat := 118140960795 + 1705045 * 2 ^ 59
def prefixEnd_1705045 : Nat := 4983230072969 + 3 ^ 40 * 1705045 * 2
def baseEnd_1705045 : Nat := 583671748363591158197431

theorem tailTrace_1705045 : CollatzResearch.WordTrace tailWord_1705045 prefixEnd_1705045 583671748363591158197431 := by
  unfold tailWord_1705045
  simp only [CollatzResearch.WordTrace]
  refine ⟨62188100107920638347612589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41458733405280425565075059 62188100107920638347612589)
  ·
    refine ⟨23320537540470239380354721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62188100107920638347612589 23320537540470239380354721)
    ·
      refine ⟨17490403155352679535266041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23320537540470239380354721 17490403155352679535266041)
      ·
        refine ⟨13117802366514509651449531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17490403155352679535266041 13117802366514509651449531)
        ·
          refine ⟨19676703549771764477174297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13117802366514509651449531 19676703549771764477174297)
          ·
            refine ⟨14757527662328823357880723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19676703549771764477174297 14757527662328823357880723)
            ·
              refine ⟨22136291493493235036821085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14757527662328823357880723 22136291493493235036821085)
              ·
                refine ⟨8301109310059963138807907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22136291493493235036821085 8301109310059963138807907)
                ·
                  refine ⟨12451663965089944708211861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8301109310059963138807907 12451663965089944708211861)
                  ·
                    refine ⟨583671748363591158197431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12451663965089944708211861 583671748363591158197431)
                    ·
                      rfl

theorem cell22_1705045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_1705045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1705045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1705045 prefixEnd_1705045 := by exact prefixLift 1705045
  have htrace : WordTrace (prefixWord ++ tailWord_1705045) baseStart_1705045 baseEnd_1705045 := by
    simpa [prefixWord, tailWord_1705045, baseEnd_1705045] using wordTrace_append hprefix tailTrace_1705045
  have hstable : (prefixWord ++ tailWord_1705045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705045).length < 2 ^ (prefixWord ++ tailWord_1705045).sum := by decide
  have hdescent : baseEnd_1705045 < baseStart_1705045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705066 : List Nat := [3, 1, 3, 2, 2, 2, 3, 2, 4]
def baseStart_1705066 : Nat := 118140960795 + 1705066 * 2 ^ 59
def prefixEnd_1705066 : Nat := 4983230072969 + 3 ^ 40 * 1705066 * 2
def baseEnd_1705066 : Nat := 194559645697584701140789

theorem tailTrace_1705066 : CollatzResearch.WordTrace tailWord_1705066 prefixEnd_1705066 194559645697584701140789 := by
  unfold tailWord_1705066
  simp only [CollatzResearch.WordTrace]
  refine ⟨15547216510211139733531763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41459244027229705956084701 15547216510211139733531763)
  ·
    refine ⟨23320824765316709600297645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15547216510211139733531763 23320824765316709600297645)
    ·
      refine ⟨8745309286993766100111617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23320824765316709600297645 8745309286993766100111617)
      ·
        refine ⟨6558981965245324575083713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8745309286993766100111617 6558981965245324575083713)
        ·
          refine ⟨4919236473933993431312785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6558981965245324575083713 4919236473933993431312785)
          ·
            refine ⟨3689427355450495073484589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4919236473933993431312785 3689427355450495073484589)
            ·
              refine ⟨1383535258293935652556721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3689427355450495073484589 1383535258293935652556721)
              ·
                refine ⟨1037651443720451739417541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1383535258293935652556721 1037651443720451739417541)
                ·
                  refine ⟨194559645697584701140789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1037651443720451739417541 194559645697584701140789)
                  ·
                    rfl

theorem cell22_1705066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 4].length) (baseStart_1705066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1705066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1705066 prefixEnd_1705066 := by exact prefixLift 1705066
  have htrace : WordTrace (prefixWord ++ tailWord_1705066) baseStart_1705066 baseEnd_1705066 := by
    simpa [prefixWord, tailWord_1705066, baseEnd_1705066] using wordTrace_append hprefix tailTrace_1705066
  have hstable : (prefixWord ++ tailWord_1705066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705066).length < 2 ^ (prefixWord ++ tailWord_1705066).sum := by decide
  have hdescent : baseEnd_1705066 < baseStart_1705066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705137 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 1, 7]
def baseStart_1705137 : Nat := 118140960795 + 1705137 * 2 ^ 59
def prefixEnd_1705137 : Nat := 4983230072969 + 3 ^ 40 * 1705137 * 2
def baseEnd_1705137 : Nat := 583703241843733584897149

theorem tailTrace_1705137 : CollatzResearch.WordTrace tailWord_1705137 prefixEnd_1705137 583703241843733584897149 := by
  unfold tailWord_1705137
  simp only [CollatzResearch.WordTrace]
  refine ⟨62191455623587338059961665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41460970415724892039974443 62191455623587338059961665)
  ·
    refine ⟨46643591717690503544971249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62191455623587338059961665 46643591717690503544971249)
    ·
      refine ⟨34982693788267877658728437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46643591717690503544971249 34982693788267877658728437)
      ·
        refine ⟨3279627542650113530505791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34982693788267877658728437 3279627542650113530505791)
        ·
          refine ⟨4919441313975170295758687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3279627542650113530505791 4919441313975170295758687)
          ·
            refine ⟨7379161970962755443638031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4919441313975170295758687 7379161970962755443638031)
            ·
              refine ⟨11068742956444133165457047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7379161970962755443638031 11068742956444133165457047)
              ·
                refine ⟨16603114434666199748185571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11068742956444133165457047 16603114434666199748185571)
                ·
                  refine ⟨24904671651999299622278357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16603114434666199748185571 24904671651999299622278357)
                  ·
                    refine ⟨583703241843733584897149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24904671651999299622278357 583703241843733584897149)
                    ·
                      rfl

theorem cell22_1705137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_1705137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1705137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1705137 prefixEnd_1705137 := by exact prefixLift 1705137
  have htrace : WordTrace (prefixWord ++ tailWord_1705137) baseStart_1705137 baseEnd_1705137 := by
    simpa [prefixWord, tailWord_1705137, baseEnd_1705137] using wordTrace_append hprefix tailTrace_1705137
  have hstable : (prefixWord ++ tailWord_1705137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705137).length < 2 ^ (prefixWord ++ tailWord_1705137).sum := by decide
  have hdescent : baseEnd_1705137 < baseStart_1705137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705184 : List Nat := [2, 1, 1, 3, 1, 4, 2, 4, 4]
def baseStart_1705184 : Nat := 118140960795 + 1705184 * 2 ^ 59
def prefixEnd_1705184 : Nat := 4983230072969 + 3 ^ 40 * 1705184 * 2
def baseEnd_1705184 : Nat := 194573110301413709657335

theorem tailTrace_1705184 : CollatzResearch.WordTrace tailWord_1705184 prefixEnd_1705184 194573110301413709657335 := by
  unfold tailWord_1705184
  simp only [CollatzResearch.WordTrace]
  refine ⟨31096584927208532543461303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41462113236278043391281737 31096584927208532543461303)
  ·
    refine ⟨46644877390812798815191955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31096584927208532543461303 46644877390812798815191955)
    ·
      refine ⟨69967316086219198222787933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46644877390812798815191955 69967316086219198222787933)
      ·
        refine ⟨26237743532332199333545475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69967316086219198222787933 26237743532332199333545475)
        ·
          refine ⟨39356615298498299000318213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26237743532332199333545475 39356615298498299000318213)
          ·
            refine ⟨7379365368468431062559665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39356615298498299000318213 7379365368468431062559665)
            ·
              refine ⟨5534524026351323296919749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7379365368468431062559665 5534524026351323296919749)
              ·
                refine ⟨1037723254940873118172453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5534524026351323296919749 1037723254940873118172453)
                ·
                  refine ⟨194573110301413709657335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1037723254940873118172453 194573110301413709657335)
                  ·
                    rfl

theorem cell22_1705184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 4].length) (baseStart_1705184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1705184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1705184 prefixEnd_1705184 := by exact prefixLift 1705184
  have htrace : WordTrace (prefixWord ++ tailWord_1705184) baseStart_1705184 baseEnd_1705184 := by
    simpa [prefixWord, tailWord_1705184, baseEnd_1705184] using wordTrace_append hprefix tailTrace_1705184
  have hstable : (prefixWord ++ tailWord_1705184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705184).length < 2 ^ (prefixWord ++ tailWord_1705184).sum := by decide
  have hdescent : baseEnd_1705184 < baseStart_1705184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705214 : List Nat := [4, 2, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_1705214 : Nat := 118140960795 + 1705214 * 2 ^ 59
def prefixEnd_1705214 : Nat := 4983230072969 + 3 ^ 40 * 1705214 * 2
def baseEnd_1705214 : Nat := 583729600517331050721913

theorem tailTrace_1705214 : CollatzResearch.WordTrace tailWord_1705214 prefixEnd_1705214 583729600517331050721913 := by
  unfold tailWord_1705214
  simp only [CollatzResearch.WordTrace]
  refine ⟨7774283005538547526314337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41462842696205586807009797 7774283005538547526314337)
  ·
    refine ⟨5830712254153910644735753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7774283005538547526314337 5830712254153910644735753)
    ·
      refine ⟨4373034190615432983551815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5830712254153910644735753 4373034190615432983551815)
      ·
        refine ⟨6559551285923149475327723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4373034190615432983551815 6559551285923149475327723)
        ·
          refine ⟨9839326928884724212991585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6559551285923149475327723 9839326928884724212991585)
          ·
            refine ⟨7379495196663543159743689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9839326928884724212991585 7379495196663543159743689)
            ·
              refine ⟨5534621397497657369807767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7379495196663543159743689 5534621397497657369807767)
              ·
                refine ⟨8301932096246486054711651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5534621397497657369807767 8301932096246486054711651)
                ·
                  refine ⟨12452898144369729082067477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8301932096246486054711651 12452898144369729082067477)
                  ·
                    refine ⟨583729600517331050721913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12452898144369729082067477 583729600517331050721913)
                    ·
                      rfl

theorem cell22_1705214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_1705214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1705214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1705214 prefixEnd_1705214 := by exact prefixLift 1705214
  have htrace : WordTrace (prefixWord ++ tailWord_1705214) baseStart_1705214 baseEnd_1705214 := by
    simpa [prefixWord, tailWord_1705214, baseEnd_1705214] using wordTrace_append hprefix tailTrace_1705214
  have hstable : (prefixWord ++ tailWord_1705214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705214).length < 2 ^ (prefixWord ++ tailWord_1705214).sum := by decide
  have hdescent : baseEnd_1705214 < baseStart_1705214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705250 : List Nat := [3, 3, 1, 1, 4, 2, 2, 1, 2, 3]
def baseStart_1705250 : Nat := 118140960795 + 1705250 * 2 ^ 59
def prefixEnd_1705250 : Nat := 4983230072969 + 3 ^ 40 * 1705250 * 2
def baseEnd_1705250 : Nat := 583741924053038956821803

theorem tailTrace_1705250 : CollatzResearch.WordTrace tailWord_1705250 prefixEnd_1705250 583741924053038956821803 := by
  unfold tailWord_1705250
  simp only [CollatzResearch.WordTrace]
  refine ⟨15548894268044489589706301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41463718048118638905883469 15548894268044489589706301)
  ·
    refine ⟨5830835350516683596139863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15548894268044489589706301 5830835350516683596139863)
    ·
      refine ⟨8746253025775025394209795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5830835350516683596139863 8746253025775025394209795)
      ·
        refine ⟨13119379538662538091314693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8746253025775025394209795 13119379538662538091314693)
        ·
          refine ⟨2459883663499225892121505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13119379538662538091314693 2459883663499225892121505)
          ·
            refine ⟨1844912747624419419091129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2459883663499225892121505 1844912747624419419091129)
            ·
              refine ⟨1383684560718314564318347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1844912747624419419091129 1383684560718314564318347)
              ·
                refine ⟨2075526841077471846477521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1383684560718314564318347 2075526841077471846477521)
                ·
                  refine ⟨1556645130808103884858141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2075526841077471846477521 1556645130808103884858141)
                  ·
                    refine ⟨583741924053038956821803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1556645130808103884858141 583741924053038956821803)
                    ·
                      rfl

theorem cell22_1705250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_1705250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1705250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1705250 prefixEnd_1705250 := by exact prefixLift 1705250
  have htrace : WordTrace (prefixWord ++ tailWord_1705250) baseStart_1705250 baseEnd_1705250 := by
    simpa [prefixWord, tailWord_1705250, baseEnd_1705250] using wordTrace_append hprefix tailTrace_1705250
  have hstable : (prefixWord ++ tailWord_1705250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705250).length < 2 ^ (prefixWord ++ tailWord_1705250).sum := by decide
  have hdescent : baseEnd_1705250 < baseStart_1705250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705272 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 4, 5]
def baseStart_1705272 : Nat := 118140960795 + 1705272 * 2 ^ 59
def prefixEnd_1705272 : Nat := 4983230072969 + 3 ^ 40 * 1705272 * 2
def baseEnd_1705272 : Nat := 583749455102638232771735

theorem tailTrace_1705272 : CollatzResearch.WordTrace tailWord_1705272 prefixEnd_1705272 583749455102638232771735 := by
  unfold tailWord_1705272
  simp only [CollatzResearch.WordTrace]
  refine ⟨31098189739049128058063035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41464252985398837410750713 31098189739049128058063035)
  ·
    refine ⟨46647284608573692087094553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31098189739049128058063035 46647284608573692087094553)
    ·
      refine ⟨34985463456430269065320915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46647284608573692087094553 34985463456430269065320915)
      ·
        refine ⟨52478195184645403597981373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34985463456430269065320915 52478195184645403597981373)
        ·
          refine ⟨19679323194242026349243015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52478195184645403597981373 19679323194242026349243015)
          ·
            refine ⟨29518984791363039523864523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19679323194242026349243015 29518984791363039523864523)
            ·
              refine ⟨44278477187044559285796785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29518984791363039523864523 44278477187044559285796785)
              ·
                refine ⟨33208857890283419464347589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44278477187044559285796785 33208857890283419464347589)
                ·
                  refine ⟨6226660854428141149565173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33208857890283419464347589 6226660854428141149565173)
                  ·
                    refine ⟨583749455102638232771735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6226660854428141149565173 583749455102638232771735)
                    ·
                      rfl

theorem cell22_1705272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_1705272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1705272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1705272 prefixEnd_1705272 := by exact prefixLift 1705272
  have htrace : WordTrace (prefixWord ++ tailWord_1705272) baseStart_1705272 baseEnd_1705272 := by
    simpa [prefixWord, tailWord_1705272, baseEnd_1705272] using wordTrace_append hprefix tailTrace_1705272
  have hstable : (prefixWord ++ tailWord_1705272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705272).length < 2 ^ (prefixWord ++ tailWord_1705272).sum := by decide
  have hdescent : baseEnd_1705272 < baseStart_1705272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705278 : List Nat := [4, 2, 1, 2, 1, 1, 2, 5, 1, 3]
def baseStart_1705278 : Nat := 118140960795 + 1705278 * 2 ^ 59
def prefixEnd_1705278 : Nat := 4983230072969 + 3 ^ 40 * 1705278 * 2
def baseEnd_1705278 : Nat := 583751509025256217121717

theorem tailTrace_1705278 : CollatzResearch.WordTrace tailWord_1705278 prefixEnd_1705278 583751509025256217121717 := by
  unfold tailWord_1705278
  simp only [CollatzResearch.WordTrace]
  refine ⟨7774574789509564892605561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41464398877384346093896325 7774574789509564892605561)
  ·
    refine ⟨5830931092132173669454171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7774574789509564892605561 5830931092132173669454171)
    ·
      refine ⟨8746396638198260504181257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5830931092132173669454171 8746396638198260504181257)
      ·
        refine ⟨6559797478648695378135943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8746396638198260504181257 6559797478648695378135943)
        ·
          refine ⟨9839696217973043067203915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6559797478648695378135943 9839696217973043067203915)
          ·
            refine ⟨14759544326959564600805873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9839696217973043067203915 14759544326959564600805873)
            ·
              refine ⟨11069658245219673450604405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14759544326959564600805873 11069658245219673450604405)
              ·
                refine ⟨1037780460489344385994163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11069658245219673450604405 1037780460489344385994163)
                ·
                  refine ⟨1556670690734016578991245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1037780460489344385994163 1556670690734016578991245)
                  ·
                    refine ⟨583751509025256217121717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1556670690734016578991245 583751509025256217121717)
                    ·
                      rfl

theorem cell22_1705278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_1705278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1705278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1705278 prefixEnd_1705278 := by exact prefixLift 1705278
  have htrace : WordTrace (prefixWord ++ tailWord_1705278) baseStart_1705278 baseEnd_1705278 := by
    simpa [prefixWord, tailWord_1705278, baseEnd_1705278] using wordTrace_append hprefix tailTrace_1705278
  have hstable : (prefixWord ++ tailWord_1705278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705278).length < 2 ^ (prefixWord ++ tailWord_1705278).sum := by decide
  have hdescent : baseEnd_1705278 < baseStart_1705278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705342 : List Nat := [4, 2, 3, 2, 2, 1, 1, 2, 5]
def baseStart_1705342 : Nat := 118140960795 + 1705342 * 2 ^ 59
def prefixEnd_1705342 : Nat := 4983230072969 + 3 ^ 40 * 1705342 * 2
def baseEnd_1705342 : Nat := 194591139177727127840507

theorem tailTrace_1705342 : CollatzResearch.WordTrace tailWord_1705342 prefixEnd_1705342 194591139177727127840507 := by
  unfold tailWord_1705342
  simp only [CollatzResearch.WordTrace]
  refine ⟨7774866573480582258896785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41465955058563105380782853 7774866573480582258896785)
  ·
    refine ⟨5831149930110436694172589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7774866573480582258896785 5831149930110436694172589)
    ·
      refine ⟨2186681223791413760314721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5831149930110436694172589 2186681223791413760314721)
      ·
        refine ⟨1640010917843560320236041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2186681223791413760314721 1640010917843560320236041)
        ·
          refine ⟨1230008188382670240177031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1640010917843560320236041 1230008188382670240177031)
          ·
            refine ⟨1845012282574005360265547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1230008188382670240177031 1845012282574005360265547)
            ·
              refine ⟨2767518423861008040398321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1845012282574005360265547 2767518423861008040398321)
              ·
                refine ⟨2075638817895756030298741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2767518423861008040398321 2075638817895756030298741)
                ·
                  refine ⟨194591139177727127840507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2075638817895756030298741 194591139177727127840507)
                  ·
                    rfl

theorem cell22_1705342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_1705342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1705342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1705342 prefixEnd_1705342 := by exact prefixLift 1705342
  have htrace : WordTrace (prefixWord ++ tailWord_1705342) baseStart_1705342 baseEnd_1705342 := by
    simpa [prefixWord, tailWord_1705342, baseEnd_1705342] using wordTrace_append hprefix tailTrace_1705342
  have hstable : (prefixWord ++ tailWord_1705342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705342).length < 2 ^ (prefixWord ++ tailWord_1705342).sum := by decide
  have hdescent : baseEnd_1705342 < baseStart_1705342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705349 : List Nat := [1, 3, 1, 1, 3, 1, 2, 4, 2, 4]
def baseStart_1705349 : Nat := 118140960795 + 1705349 * 2 ^ 59
def prefixEnd_1705349 : Nat := 4983230072969 + 3 ^ 40 * 1705349 * 2
def baseEnd_1705349 : Nat := 583775813776235698596499

theorem tailTrace_1705349 : CollatzResearch.WordTrace tailWord_1705349 prefixEnd_1705349 583775813776235698596499 := by
  unfold tailWord_1705349
  simp only [CollatzResearch.WordTrace]
  refine ⟨62199187898819298266679101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41466125265879532177786067 62199187898819298266679101)
  ·
    refine ⟨23324695462057236850004663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62199187898819298266679101 23324695462057236850004663)
    ·
      refine ⟨34987043193085855275006995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23324695462057236850004663 34987043193085855275006995)
      ·
        refine ⟨52480564789628782912510493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34987043193085855275006995 52480564789628782912510493)
        ·
          refine ⟨19680211796110793592191435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52480564789628782912510493 19680211796110793592191435)
          ·
            refine ⟨29520317694166190388287153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19680211796110793592191435 29520317694166190388287153)
            ·
              refine ⟨22140238270624642791215365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29520317694166190388287153 22140238270624642791215365)
              ·
                refine ⟨4151294675742120523352881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22140238270624642791215365 4151294675742120523352881)
                ·
                  refine ⟨3113471006806590392514661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4151294675742120523352881 3113471006806590392514661)
                  ·
                    refine ⟨583775813776235698596499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3113471006806590392514661 583775813776235698596499)
                    ·
                      rfl

theorem cell22_1705349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_1705349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1705349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1705349 prefixEnd_1705349 := by exact prefixLift 1705349
  have htrace : WordTrace (prefixWord ++ tailWord_1705349) baseStart_1705349 baseEnd_1705349 := by
    simpa [prefixWord, tailWord_1705349, baseEnd_1705349] using wordTrace_append hprefix tailTrace_1705349
  have hstable : (prefixWord ++ tailWord_1705349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705349).length < 2 ^ (prefixWord ++ tailWord_1705349).sum := by decide
  have hdescent : baseEnd_1705349 < baseStart_1705349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705351 : List Nat := [1, 1, 4, 2, 2, 3, 1, 1, 4, 3]
def baseStart_1705351 : Nat := 118140960795 + 1705351 * 2 ^ 59
def prefixEnd_1705351 : Nat := 4983230072969 + 3 ^ 40 * 1705351 * 2
def baseEnd_1705351 : Nat := 583776498417108360046493

theorem tailTrace_1705351 : CollatzResearch.WordTrace tailWord_1705351 prefixEnd_1705351 583776498417108360046493 := by
  unfold tailWord_1705351
  simp only [CollatzResearch.WordTrace]
  refine ⟨62199260844812052608251907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41466173896541368405501271 62199260844812052608251907)
  ·
    refine ⟨93298891267218078912377861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62199260844812052608251907 93298891267218078912377861)
    ·
      refine ⟨17493542112603389796070849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93298891267218078912377861 17493542112603389796070849)
      ·
        refine ⟨13120156584452542347053137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17493542112603389796070849 13120156584452542347053137)
        ·
          refine ⟨9840117438339406760289853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13120156584452542347053137 9840117438339406760289853)
          ·
            refine ⟨3690044039377277535108695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9840117438339406760289853 3690044039377277535108695)
            ·
              refine ⟨5535066059065916302663043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3690044039377277535108695 5535066059065916302663043)
              ·
                refine ⟨8302599088598874453994565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5535066059065916302663043 8302599088598874453994565)
                ·
                  refine ⟨1556737329112288960123981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8302599088598874453994565 1556737329112288960123981)
                  ·
                    refine ⟨583776498417108360046493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1556737329112288960123981 583776498417108360046493)
                    ·
                      rfl

theorem cell22_1705351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_1705351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1705351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1705351 prefixEnd_1705351 := by exact prefixLift 1705351
  have htrace : WordTrace (prefixWord ++ tailWord_1705351) baseStart_1705351 baseEnd_1705351 := by
    simpa [prefixWord, tailWord_1705351, baseEnd_1705351] using wordTrace_append hprefix tailTrace_1705351
  have hstable : (prefixWord ++ tailWord_1705351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705351).length < 2 ^ (prefixWord ++ tailWord_1705351).sum := by decide
  have hdescent : baseEnd_1705351 < baseStart_1705351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705368 : List Nat := [2, 1, 2, 5, 2, 2, 1, 1, 1, 5]
def baseStart_1705368 : Nat := 118140960795 + 1705368 * 2 ^ 59
def prefixEnd_1705368 : Nat := 4983230072969 + 3 ^ 40 * 1705368 * 2
def baseEnd_1705368 : Nat := 583782317864525982371441

theorem tailTrace_1705368 : CollatzResearch.WordTrace tailWord_1705368 prefixEnd_1705368 583782317864525982371441 := by
  unfold tailWord_1705368
  simp only [CollatzResearch.WordTrace]
  refine ⟨31099940442875232255810379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41466587257166976341080505 31099940442875232255810379)
  ·
    refine ⟨46649910664312848383715569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31099940442875232255810379 46649910664312848383715569)
    ·
      refine ⟨34987432998234636287786677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46649910664312848383715569 34987432998234636287786677)
      ·
        refine ⟨3280071843584497151980001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34987432998234636287786677 3280071843584497151980001)
        ·
          refine ⟨2460053882688372863985001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3280071843584497151980001 2460053882688372863985001)
          ·
            refine ⟨1845040412016279647988751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2460053882688372863985001 1845040412016279647988751)
            ·
              refine ⟨2767560618024419471983127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1845040412016279647988751 2767560618024419471983127)
              ·
                refine ⟨4151340927036629207974691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2767560618024419471983127 4151340927036629207974691)
                ·
                  refine ⟨6227011390554943811962037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4151340927036629207974691 6227011390554943811962037)
                  ·
                    refine ⟨583782317864525982371441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6227011390554943811962037 583782317864525982371441)
                    ·
                      rfl

theorem cell22_1705368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 1, 5].length) (baseStart_1705368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1705368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1705368 prefixEnd_1705368 := by exact prefixLift 1705368
  have htrace : WordTrace (prefixWord ++ tailWord_1705368) baseStart_1705368 baseEnd_1705368 := by
    simpa [prefixWord, tailWord_1705368, baseEnd_1705368] using wordTrace_append hprefix tailTrace_1705368
  have hstable : (prefixWord ++ tailWord_1705368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705368).length < 2 ^ (prefixWord ++ tailWord_1705368).sum := by decide
  have hdescent : baseEnd_1705368 < baseStart_1705368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705501 : List Nat := [1, 4, 2, 2, 1, 1, 3, 1, 1, 6]
def baseStart_1705501 : Nat := 118140960795 + 1705501 * 2 ^ 59
def prefixEnd_1705501 : Nat := 4983230072969 + 3 ^ 40 * 1705501 * 2
def baseEnd_1705501 : Nat := 583827846482557968796033

theorem tailTrace_1705501 : CollatzResearch.WordTrace tailWord_1705501 prefixEnd_1705501 583827846482557968796033 := by
  unfold tailWord_1705501
  simp only [CollatzResearch.WordTrace]
  refine ⟨62204731794268628226212357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41469821196179085484141571 62204731794268628226212357)
  ·
    refine ⟨11663387211425367792414817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62204731794268628226212357 11663387211425367792414817)
    ·
      refine ⟨8747540408569025844311113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11663387211425367792414817 8747540408569025844311113)
      ·
        refine ⟨6560655306426769383233335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8747540408569025844311113 6560655306426769383233335)
        ·
          refine ⟨9840982959640154074850003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6560655306426769383233335 9840982959640154074850003)
          ·
            refine ⟨14761474439460231112275005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9840982959640154074850003 14761474439460231112275005)
            ·
              refine ⟨5535552914797586667103127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14761474439460231112275005 5535552914797586667103127)
              ·
                refine ⟨8303329372196380000654691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5535552914797586667103127 8303329372196380000654691)
                ·
                  refine ⟨12454994058294570000982037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8303329372196380000654691 12454994058294570000982037)
                  ·
                    refine ⟨583827846482557968796033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12454994058294570000982037 583827846482557968796033)
                    ·
                      rfl

theorem cell22_1705501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_1705501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1705501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1705501 prefixEnd_1705501 := by exact prefixLift 1705501
  have htrace : WordTrace (prefixWord ++ tailWord_1705501) baseStart_1705501 baseEnd_1705501 := by
    simpa [prefixWord, tailWord_1705501, baseEnd_1705501] using wordTrace_append hprefix tailTrace_1705501
  have hstable : (prefixWord ++ tailWord_1705501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705501).length < 2 ^ (prefixWord ++ tailWord_1705501).sum := by decide
  have hdescent : baseEnd_1705501 < baseStart_1705501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705507 : List Nat := [1, 1, 1, 4, 6, 1, 2, 1, 1, 4]
def baseStart_1705507 : Nat := 118140960795 + 1705507 * 2 ^ 59
def prefixEnd_1705507 : Nat := 4983230072969 + 3 ^ 40 * 1705507 * 2
def baseEnd_1705507 : Nat := 583829900405175953146015

theorem tailTrace_1705507 : CollatzResearch.WordTrace tailWord_1705507 prefixEnd_1705507 583829900405175953146015 := by
  unfold tailWord_1705507
  simp only [CollatzResearch.WordTrace]
  refine ⟨62204950632246891250930775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41469967088164594167287183 62204950632246891250930775)
  ·
    refine ⟨93307425948370336876396163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62204950632246891250930775 93307425948370336876396163)
    ·
      refine ⟨139961138922555505314594245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93307425948370336876396163 139961138922555505314594245)
      ·
        refine ⟨26242713547979157246486421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139961138922555505314594245 26242713547979157246486421)
        ·
          refine ⟨1230127197561522995929051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26242713547979157246486421 1230127197561522995929051)
          ·
            refine ⟨1845190796342284493893577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1230127197561522995929051 1845190796342284493893577)
            ·
              refine ⟨1383893097256713370420183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1845190796342284493893577 1383893097256713370420183)
              ·
                refine ⟨2075839645885070055630275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1383893097256713370420183 2075839645885070055630275)
                ·
                  refine ⟨3113759468827605083445413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2075839645885070055630275 3113759468827605083445413)
                  ·
                    refine ⟨583829900405175953146015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3113759468827605083445413 583829900405175953146015)
                    ·
                      rfl

theorem cell22_1705507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 1, 4].length) (baseStart_1705507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1705507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1705507 prefixEnd_1705507 := by exact prefixLift 1705507
  have htrace : WordTrace (prefixWord ++ tailWord_1705507) baseStart_1705507 baseEnd_1705507 := by
    simpa [prefixWord, tailWord_1705507, baseEnd_1705507] using wordTrace_append hprefix tailTrace_1705507
  have hstable : (prefixWord ++ tailWord_1705507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705507).length < 2 ^ (prefixWord ++ tailWord_1705507).sum := by decide
  have hdescent : baseEnd_1705507 < baseStart_1705507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705548 : List Nat := [2, 2, 1, 3, 1, 3, 2, 2, 3, 3]
def baseStart_1705548 : Nat := 118140960795 + 1705548 * 2 ^ 59
def prefixEnd_1705548 : Nat := 4983230072969 + 3 ^ 40 * 1705548 * 2
def baseEnd_1705548 : Nat := 583843935543065512870889

theorem tailTrace_1705548 : CollatzResearch.WordTrace tailWord_1705548 prefixEnd_1705548 583843935543065512870889 := by
  unfold tailWord_1705548
  simp only [CollatzResearch.WordTrace]
  refine ⟨31103223012549177626586649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41470964016732236835448865 31103223012549177626586649)
  ·
    refine ⟨23327417259411883219939987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31103223012549177626586649 23327417259411883219939987)
    ·
      refine ⟨34991125889117824829909981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23327417259411883219939987 34991125889117824829909981)
      ·
        refine ⟨13121672208419184311216243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34991125889117824829909981 13121672208419184311216243)
        ·
          refine ⟨19682508312628776466824365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13121672208419184311216243 19682508312628776466824365)
          ·
            refine ⟨7380940617235791175059137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19682508312628776466824365 7380940617235791175059137)
            ·
              refine ⟨5535705462926843381294353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7380940617235791175059137 5535705462926843381294353)
              ·
                refine ⟨4151779097195132535970765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5535705462926843381294353 4151779097195132535970765)
                ·
                  refine ⟨1556917161448174700989037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4151779097195132535970765 1556917161448174700989037)
                  ·
                    refine ⟨583843935543065512870889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1556917161448174700989037 583843935543065512870889)
                    ·
                      rfl

theorem cell22_1705548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 3, 3].length) (baseStart_1705548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1705548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1705548 prefixEnd_1705548 := by exact prefixLift 1705548
  have htrace : WordTrace (prefixWord ++ tailWord_1705548) baseStart_1705548 baseEnd_1705548 := by
    simpa [prefixWord, tailWord_1705548, baseEnd_1705548] using wordTrace_append hprefix tailTrace_1705548
  have hstable : (prefixWord ++ tailWord_1705548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705548).length < 2 ^ (prefixWord ++ tailWord_1705548).sum := by decide
  have hdescent : baseEnd_1705548 < baseStart_1705548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705582 : List Nat := [4, 1, 2, 2, 3, 2, 1, 1, 3, 3]
def baseStart_1705582 : Nat := 118140960795 + 1705582 * 2 ^ 59
def prefixEnd_1705582 : Nat := 4983230072969 + 3 ^ 40 * 1705582 * 2
def baseEnd_1705582 : Nat := 583855574437900757520785

theorem tailTrace_1705582 : CollatzResearch.WordTrace tailWord_1705582 prefixEnd_1705582 583855574437900757520785 := by
  unfold tailWord_1705582
  simp only [CollatzResearch.WordTrace]
  refine ⟨7775960763371897382488875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41471790737983452706607333 7775960763371897382488875)
  ·
    refine ⟨11663941145057846073733313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7775960763371897382488875 11663941145057846073733313)
    ·
      refine ⟨8747955858793384555299985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11663941145057846073733313 8747955858793384555299985)
      ·
        refine ⟨6560966894095038416474989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8747955858793384555299985 6560966894095038416474989)
        ·
          refine ⟨2460362585285639406178121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6560966894095038416474989 2460362585285639406178121)
          ·
            refine ⟨1845271938964229554633591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2460362585285639406178121 1845271938964229554633591)
            ·
              refine ⟨2767907908446344331950387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1845271938964229554633591 2767907908446344331950387)
              ·
                refine ⟨4151861862669516497925581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2767907908446344331950387 4151861862669516497925581)
                ·
                  refine ⟨1556948198501068686722093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4151861862669516497925581 1556948198501068686722093)
                  ·
                    refine ⟨583855574437900757520785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1556948198501068686722093 583855574437900757520785)
                    ·
                      rfl

theorem cell22_1705582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_1705582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1705582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1705582 prefixEnd_1705582 := by exact prefixLift 1705582
  have htrace : WordTrace (prefixWord ++ tailWord_1705582) baseStart_1705582 baseEnd_1705582 := by
    simpa [prefixWord, tailWord_1705582, baseEnd_1705582] using wordTrace_append hprefix tailTrace_1705582
  have hstable : (prefixWord ++ tailWord_1705582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705582).length < 2 ^ (prefixWord ++ tailWord_1705582).sum := by decide
  have hdescent : baseEnd_1705582 < baseStart_1705582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705591 : List Nat := [1, 1, 3, 1, 1, 3, 1, 4, 3, 4]
def baseStart_1705591 : Nat := 118140960795 + 1705591 * 2 ^ 59
def prefixEnd_1705591 : Nat := 4983230072969 + 3 ^ 40 * 1705591 * 2
def baseEnd_1705591 : Nat := 583858655321827734045757

theorem tailTrace_1705591 : CollatzResearch.WordTrace tailWord_1705591 prefixEnd_1705591 583858655321827734045757 := by
  unfold tailWord_1705591
  simp only [CollatzResearch.WordTrace]
  refine ⟨62208014363942573596988627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41472009575961715731325751 62208014363942573596988627)
  ·
    refine ⟨93312021545913860395482941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62208014363942573596988627 93312021545913860395482941)
    ·
      refine ⟨34992008079717697648306103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93312021545913860395482941 34992008079717697648306103)
      ·
        refine ⟨52488012119576546472459155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34992008079717697648306103 52488012119576546472459155)
        ·
          refine ⟨78732018179364819708688733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52488012119576546472459155 78732018179364819708688733)
          ·
            refine ⟨29524506817261807390758275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78732018179364819708688733 29524506817261807390758275)
            ·
              refine ⟨44286760225892711086137413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29524506817261807390758275 44286760225892711086137413)
              ·
                refine ⟨8303767542354883328650765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44286760225892711086137413 8303767542354883328650765)
                ·
                  refine ⟨3113912828383081248244037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8303767542354883328650765 3113912828383081248244037)
                  ·
                    refine ⟨583858655321827734045757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3113912828383081248244037 583858655321827734045757)
                    ·
                      rfl

theorem cell22_1705591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_1705591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1705591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1705591 prefixEnd_1705591 := by exact prefixLift 1705591
  have htrace : WordTrace (prefixWord ++ tailWord_1705591) baseStart_1705591 baseEnd_1705591 := by
    simpa [prefixWord, tailWord_1705591, baseEnd_1705591] using wordTrace_append hprefix tailTrace_1705591
  have hstable : (prefixWord ++ tailWord_1705591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705591).length < 2 ^ (prefixWord ++ tailWord_1705591).sum := by decide
  have hdescent : baseEnd_1705591 < baseStart_1705591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705655 : List Nat := [1, 1, 3, 1, 5, 1, 2, 3, 2, 3]
def baseStart_1705655 : Nat := 118140960795 + 1705655 * 2 ^ 59
def prefixEnd_1705655 : Nat := 4983230072969 + 3 ^ 40 * 1705655 * 2
def baseEnd_1705655 : Nat := 583880563829752900445561

theorem tailTrace_1705655 : CollatzResearch.WordTrace tailWord_1705655 prefixEnd_1705655 583880563829752900445561 := by
  unfold tailWord_1705655
  simp only [CollatzResearch.WordTrace]
  refine ⟨62210348635710712527318419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41473565757140475018212279 62210348635710712527318419)
  ·
    refine ⟨93315522953566068790977629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62210348635710712527318419 93315522953566068790977629)
    ·
      refine ⟨34993321107587275796616611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93315522953566068790977629 34993321107587275796616611)
      ·
        refine ⟨52489981661380913694924917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34993321107587275796616611 52489981661380913694924917)
        ·
          refine ⟨4920935780754460658899211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52489981661380913694924917 4920935780754460658899211)
          ·
            refine ⟨7381403671131690988348817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4920935780754460658899211 7381403671131690988348817)
            ·
              refine ⟨5536052753348768241261613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7381403671131690988348817 5536052753348768241261613)
              ·
                refine ⟨2076019782505788090473105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5536052753348768241261613 2076019782505788090473105)
                ·
                  refine ⟨1557014836879341067854829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2076019782505788090473105 1557014836879341067854829)
                  ·
                    refine ⟨583880563829752900445561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1557014836879341067854829 583880563829752900445561)
                    ·
                      rfl

theorem cell22_1705655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 3].length) (baseStart_1705655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1705655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1705655 prefixEnd_1705655 := by exact prefixLift 1705655
  have htrace : WordTrace (prefixWord ++ tailWord_1705655) baseStart_1705655 baseEnd_1705655 := by
    simpa [prefixWord, tailWord_1705655, baseEnd_1705655] using wordTrace_append hprefix tailTrace_1705655
  have hstable : (prefixWord ++ tailWord_1705655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705655).length < 2 ^ (prefixWord ++ tailWord_1705655).sum := by decide
  have hdescent : baseEnd_1705655 < baseStart_1705655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705700 : List Nat := [2, 3, 1, 1, 1, 3, 4, 1, 3, 3]
def baseStart_1705700 : Nat := 118140960795 + 1705700 * 2 ^ 59
def prefixEnd_1705700 : Nat := 4983230072969 + 3 ^ 40 * 1705700 * 2
def baseEnd_1705700 : Nat := 583895968249387783070423

theorem tailTrace_1705700 : CollatzResearch.WordTrace tailWord_1705700 prefixEnd_1705700 583895968249387783070423 := by
  unfold tailWord_1705700
  simp only [CollatzResearch.WordTrace]
  refine ⟨31105994960273842606353277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41474659947031790141804369 31105994960273842606353277)
  ·
    refine ⟨11664748110102690977382479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31105994960273842606353277 11664748110102690977382479)
    ·
      refine ⟨17497122165154036466073719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11664748110102690977382479 17497122165154036466073719)
      ·
        refine ⟨26245683247731054699110579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17497122165154036466073719 26245683247731054699110579)
        ·
          refine ⟨39368524871596582048665869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26245683247731054699110579 39368524871596582048665869)
          ·
            refine ⟨14763196826848718268249701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39368524871596582048665869 14763196826848718268249701)
            ·
              refine ⟨2768099405034134675296819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14763196826848718268249701 2768099405034134675296819)
              ·
                refine ⟨4152149107551202012945229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2768099405034134675296819 4152149107551202012945229)
                ·
                  refine ⟨1557055915331700754854461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4152149107551202012945229 1557055915331700754854461)
                  ·
                    refine ⟨583895968249387783070423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1557055915331700754854461 583895968249387783070423)
                    ·
                      rfl

theorem cell22_1705700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_1705700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1705700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1705700 prefixEnd_1705700 := by exact prefixLift 1705700
  have htrace : WordTrace (prefixWord ++ tailWord_1705700) baseStart_1705700 baseEnd_1705700 := by
    simpa [prefixWord, tailWord_1705700, baseEnd_1705700] using wordTrace_append hprefix tailTrace_1705700
  have hstable : (prefixWord ++ tailWord_1705700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705700).length < 2 ^ (prefixWord ++ tailWord_1705700).sum := by decide
  have hdescent : baseEnd_1705700 < baseStart_1705700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705777 : List Nat := [1, 2, 2, 3, 2, 4, 1, 2, 1, 4]
def baseStart_1705777 : Nat := 118140960795 + 1705777 * 2 ^ 59
def prefixEnd_1705777 : Nat := 4983230072969 + 3 ^ 40 * 1705777 * 2
def baseEnd_1705777 : Nat := 583922326922985248895187

theorem tailTrace_1705777 : CollatzResearch.WordTrace tailWord_1705777 prefixEnd_1705777 583922326922985248895187 := by
  unfold tailWord_1705777
  simp only [CollatzResearch.WordTrace]
  refine ⟨62214798341268727363259585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41476532227512484908839723 62214798341268727363259585)
  ·
    refine ⟨46661098755951545522444689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62214798341268727363259585 46661098755951545522444689)
    ·
      refine ⟨34995824066963659141833517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46661098755951545522444689 34995824066963659141833517)
      ·
        refine ⟨13123434025111372178187569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34995824066963659141833517 13123434025111372178187569)
        ·
          refine ⟨9842575518833529133640677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13123434025111372178187569 9842575518833529133640677)
          ·
            refine ⟨1845482909781286712557627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9842575518833529133640677 1845482909781286712557627)
            ·
              refine ⟨2768224364671930068836441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1845482909781286712557627 2768224364671930068836441)
              ·
                refine ⟨2076168273503947551627331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2768224364671930068836441 2076168273503947551627331)
                ·
                  refine ⟨3114252410255921327440997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2076168273503947551627331 3114252410255921327440997)
                  ·
                    refine ⟨583922326922985248895187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3114252410255921327440997 583922326922985248895187)
                    ·
                      rfl

theorem cell22_1705777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 4].length) (baseStart_1705777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1705777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1705777 prefixEnd_1705777 := by exact prefixLift 1705777
  have htrace : WordTrace (prefixWord ++ tailWord_1705777) baseStart_1705777 baseEnd_1705777 := by
    simpa [prefixWord, tailWord_1705777, baseEnd_1705777] using wordTrace_append hprefix tailTrace_1705777
  have hstable : (prefixWord ++ tailWord_1705777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705777).length < 2 ^ (prefixWord ++ tailWord_1705777).sum := by decide
  have hdescent : baseEnd_1705777 < baseStart_1705777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705788 : List Nat := [2, 2, 2, 2, 1, 1, 2, 3, 1, 6]
def baseStart_1705788 : Nat := 118140960795 + 1705788 * 2 ^ 59
def prefixEnd_1705788 : Nat := 4983230072969 + 3 ^ 40 * 1705788 * 2
def baseEnd_1705788 : Nat := 583926092447784886870153

theorem tailTrace_1705788 : CollatzResearch.WordTrace tailWord_1705788 prefixEnd_1705788 583926092447784886870153 := by
  unfold tailWord_1705788
  simp only [CollatzResearch.WordTrace]
  refine ⟨31107599772114438120955009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41476799696152584161273345 31107599772114438120955009)
  ·
    refine ⟨23330699829085828590716257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31107599772114438120955009 23330699829085828590716257)
    ·
      refine ⟨17498024871814371443037193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23330699829085828590716257 17498024871814371443037193)
      ·
        refine ⟨13123518653860778582277895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17498024871814371443037193 13123518653860778582277895)
        ·
          refine ⟨19685277980791167873416843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13123518653860778582277895 19685277980791167873416843)
          ·
            refine ⟨29527916971186751810125265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19685277980791167873416843 29527916971186751810125265)
            ·
              refine ⟨22145937728390063857593949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29527916971186751810125265 22145937728390063857593949)
              ·
                refine ⟨8304726648146273946597731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22145937728390063857593949 8304726648146273946597731)
                ·
                  refine ⟨12457089972219410919896597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8304726648146273946597731 12457089972219410919896597)
                  ·
                    refine ⟨583926092447784886870153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12457089972219410919896597 583926092447784886870153)
                    ·
                      rfl

theorem cell22_1705788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_1705788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1705788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1705788 prefixEnd_1705788 := by exact prefixLift 1705788
  have htrace : WordTrace (prefixWord ++ tailWord_1705788) baseStart_1705788 baseEnd_1705788 := by
    simpa [prefixWord, tailWord_1705788, baseEnd_1705788] using wordTrace_append hprefix tailTrace_1705788
  have hstable : (prefixWord ++ tailWord_1705788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705788).length < 2 ^ (prefixWord ++ tailWord_1705788).sum := by decide
  have hdescent : baseEnd_1705788 < baseStart_1705788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705790 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_1705790 : Nat := 118140960795 + 1705790 * 2 ^ 59
def prefixEnd_1705790 : Nat := 4983230072969 + 3 ^ 40 * 1705790 * 2
def baseEnd_1705790 : Nat := 583926777088657548320147

theorem tailTrace_1705790 : CollatzResearch.WordTrace tailWord_1705790 prefixEnd_1705790 583926777088657548320147 := by
  unfold tailWord_1705790
  simp only [CollatzResearch.WordTrace]
  refine ⟨7776909061277703822935353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41476848326814420388988549 7776909061277703822935353)
  ·
    refine ⟨5832681795958277867201515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7776909061277703822935353 5832681795958277867201515)
    ·
      refine ⟨8749022693937416800802273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5832681795958277867201515 8749022693937416800802273)
      ·
        refine ⟨6561767020453062600601705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8749022693937416800802273 6561767020453062600601705)
        ·
          refine ⟨4921325265339796950451279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6561767020453062600601705 4921325265339796950451279)
          ·
            refine ⟨7381987898009695425676919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4921325265339796950451279 7381987898009695425676919)
            ·
              refine ⟨11072981847014543138515379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7381987898009695425676919 11072981847014543138515379)
              ·
                refine ⟨16609472770521814707773069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11072981847014543138515379 16609472770521814707773069)
                ·
                  refine ⟨6228552288945680515414901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16609472770521814707773069 6228552288945680515414901)
                  ·
                    refine ⟨583926777088657548320147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6228552288945680515414901 583926777088657548320147)
                    ·
                      rfl

theorem cell22_1705790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_1705790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1705790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1705790 prefixEnd_1705790 := by exact prefixLift 1705790
  have htrace : WordTrace (prefixWord ++ tailWord_1705790) baseStart_1705790 baseEnd_1705790 := by
    simpa [prefixWord, tailWord_1705790, baseEnd_1705790] using wordTrace_append hprefix tailTrace_1705790
  have hstable : (prefixWord ++ tailWord_1705790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705790).length < 2 ^ (prefixWord ++ tailWord_1705790).sum := by decide
  have hdescent : baseEnd_1705790 < baseStart_1705790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705809 : List Nat := [1, 2, 2, 1, 5, 3, 2, 2, 4]
def baseStart_1705809 : Nat := 118140960795 + 1705809 * 2 ^ 59
def prefixEnd_1705809 : Nat := 4983230072969 + 3 ^ 40 * 1705809 * 2
def baseEnd_1705809 : Nat := 194644427058982610698363

theorem tailTrace_1705809 : CollatzResearch.WordTrace tailWord_1705809 prefixEnd_1705809 194644427058982610698363 := by
  unfold tailWord_1705809
  simp only [CollatzResearch.WordTrace]
  refine ⟨62215965477152796828424481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41477310318101864552282987 62215965477152796828424481)
  ·
    refine ⟨46661974107864597621318361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62215965477152796828424481 46661974107864597621318361)
    ·
      refine ⟨34996480580898448215988771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46661974107864597621318361 34996480580898448215988771)
      ·
        refine ⟨52494720871347672323983157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34996480580898448215988771 52494720871347672323983157)
        ·
          refine ⟨4921380081688844280373421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52494720871347672323983157 4921380081688844280373421)
          ·
            refine ⟨1845517530633316605140033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4921380081688844280373421 1845517530633316605140033)
            ·
              refine ⟨1384138147974987453855025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1845517530633316605140033 1384138147974987453855025)
              ·
                refine ⟨1038103610981240590391269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1384138147974987453855025 1038103610981240590391269)
                ·
                  refine ⟨194644427058982610698363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1038103610981240590391269 194644427058982610698363)
                  ·
                    rfl

theorem cell22_1705809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 4].length) (baseStart_1705809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1705809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1705809 prefixEnd_1705809 := by exact prefixLift 1705809
  have htrace : WordTrace (prefixWord ++ tailWord_1705809) baseStart_1705809 baseEnd_1705809 := by
    simpa [prefixWord, tailWord_1705809, baseEnd_1705809] using wordTrace_append hprefix tailTrace_1705809
  have hstable : (prefixWord ++ tailWord_1705809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705809).length < 2 ^ (prefixWord ++ tailWord_1705809).sum := by decide
  have hdescent : baseEnd_1705809 < baseStart_1705809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705946 : List Nat := [3, 1, 1, 2, 6, 1, 1, 2, 1, 4]
def baseStart_1705946 : Nat := 118140960795 + 1705946 * 2 ^ 59
def prefixEnd_1705946 : Nat := 4983230072969 + 3 ^ 40 * 1705946 * 2
def baseEnd_1705946 : Nat := 583980179076725141419669

theorem tailTrace_1705946 : CollatzResearch.WordTrace tailWord_1705946 prefixEnd_1705946 583980179076725141419669 := by
  unfold tailWord_1705946
  simp only [CollatzResearch.WordTrace]
  refine ⟨15555240569414117306540423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41480641518437646150774461 15555240569414117306540423)
  ·
    refine ⟨23332860854121175959810635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15555240569414117306540423 23332860854121175959810635)
    ·
      refine ⟨34999291281181763939715953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23332860854121175959810635 34999291281181763939715953)
      ·
        refine ⟨26249468460886322954786965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34999291281181763939715953 26249468460886322954786965)
        ·
          refine ⟨1230443834104046388505639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26249468460886322954786965 1230443834104046388505639)
          ·
            refine ⟨1845665751156069582758459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1230443834104046388505639 1845665751156069582758459)
            ·
              refine ⟨2768498626734104374137689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1845665751156069582758459 2768498626734104374137689)
              ·
                refine ⟨2076373970050578280603267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2768498626734104374137689 2076373970050578280603267)
                ·
                  refine ⟨3114560955075867420904901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2076373970050578280603267 3114560955075867420904901)
                  ·
                    refine ⟨583980179076725141419669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3114560955075867420904901 583980179076725141419669)
                    ·
                      rfl

theorem cell22_1705946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 1, 4].length) (baseStart_1705946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1705946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1705946 prefixEnd_1705946 := by exact prefixLift 1705946
  have htrace : WordTrace (prefixWord ++ tailWord_1705946) baseStart_1705946 baseEnd_1705946 := by
    simpa [prefixWord, tailWord_1705946, baseEnd_1705946] using wordTrace_append hprefix tailTrace_1705946
  have hstable : (prefixWord ++ tailWord_1705946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705946).length < 2 ^ (prefixWord ++ tailWord_1705946).sum := by decide
  have hdescent : baseEnd_1705946 < baseStart_1705946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705955 : List Nat := [1, 1, 1, 6, 1, 2, 2, 8]
def baseStart_1705955 : Nat := 118140960795 + 1705955 * 2 ^ 59
def prefixEnd_1705955 : Nat := 4983230072969 + 3 ^ 40 * 1705955 * 2
def baseEnd_1705955 : Nat := 64887028884516901993849

theorem tailTrace_1705955 : CollatzResearch.WordTrace tailWord_1705955 prefixEnd_1705955 64887028884516901993849 := by
  unfold tailWord_1705955
  simp only [CollatzResearch.WordTrace]
  refine ⟨62221290534623863763239319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41480860356415909175492879 62221290534623863763239319)
  ·
    refine ⟨93331935801935795644858979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62221290534623863763239319 93331935801935795644858979)
    ·
      refine ⟨139997903702903693467288469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93331935801935795644858979 139997903702903693467288469)
      ·
        refine ⟨6562401736073610631279147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 139997903702903693467288469 6562401736073610631279147)
        ·
          refine ⟨9843602604110415946918721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6562401736073610631279147 9843602604110415946918721)
          ·
            refine ⟨7382701953082811960189041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9843602604110415946918721 7382701953082811960189041)
            ·
              refine ⟨5537026464812108970141781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7382701953082811960189041 5537026464812108970141781)
              ·
                refine ⟨64887028884516901993849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5537026464812108970141781 64887028884516901993849)
                ·
                  rfl

theorem cell22_1705955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 8].length) (baseStart_1705955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1705955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1705955 prefixEnd_1705955 := by exact prefixLift 1705955
  have htrace : WordTrace (prefixWord ++ tailWord_1705955) baseStart_1705955 baseEnd_1705955 := by
    simpa [prefixWord, tailWord_1705955, baseEnd_1705955] using wordTrace_append hprefix tailTrace_1705955
  have hstable : (prefixWord ++ tailWord_1705955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705955).length < 2 ^ (prefixWord ++ tailWord_1705955).sum := by decide
  have hdescent : baseEnd_1705955 < baseStart_1705955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705985 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 1, 8]
def baseStart_1705985 : Nat := 118140960795 + 1705985 * 2 ^ 59
def prefixEnd_1705985 : Nat := 4983230072969 + 3 ^ 40 * 1705985 * 2
def baseEnd_1705985 : Nat := 583993529573742039694549

theorem tailTrace_1705985 : CollatzResearch.WordTrace tailWord_1705985 prefixEnd_1705985 583993529573742039694549 := by
  unfold tailWord_1705985
  simp only [CollatzResearch.WordTrace]
  refine ⟨62222384724515178886831409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41481589816343452591220939 62222384724515178886831409)
  ·
    refine ⟨46666788543386384165123557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62222384724515178886831409 46666788543386384165123557)
    ·
      refine ⟨8750022851884947030960667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46666788543386384165123557 8750022851884947030960667)
      ·
        refine ⟨13125034277827420546441001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8750022851884947030960667 13125034277827420546441001)
        ·
          refine ⟨9843775708370565409830751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13125034277827420546441001 9843775708370565409830751)
          ·
            refine ⟨14765663562555848114746127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9843775708370565409830751 14765663562555848114746127)
            ·
              refine ⟨22148495343833772172119191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14765663562555848114746127 22148495343833772172119191)
              ·
                refine ⟨33222743015750658258178787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22148495343833772172119191 33222743015750658258178787)
                ·
                  refine ⟨49834114523625987387268181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33222743015750658258178787 49834114523625987387268181)
                  ·
                    refine ⟨583993529573742039694549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49834114523625987387268181 583993529573742039694549)
                    ·
                      rfl

theorem cell22_1705985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_1705985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1705985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1705985 prefixEnd_1705985 := by exact prefixLift 1705985
  have htrace : WordTrace (prefixWord ++ tailWord_1705985) baseStart_1705985 baseEnd_1705985 := by
    simpa [prefixWord, tailWord_1705985, baseEnd_1705985] using wordTrace_append hprefix tailTrace_1705985
  have hstable : (prefixWord ++ tailWord_1705985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705985).length < 2 ^ (prefixWord ++ tailWord_1705985).sum := by decide
  have hdescent : baseEnd_1705985 < baseStart_1705985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706015 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 1, 7]
def baseStart_1706015 : Nat := 118140960795 + 1706015 * 2 ^ 59
def prefixEnd_1706015 : Nat := 4983230072969 + 3 ^ 40 * 1706015 * 2
def baseEnd_1706015 : Nat := 584003799186831961444457

theorem tailTrace_1706015 : CollatzResearch.WordTrace tailWord_1706015 prefixEnd_1706015 584003799186831961444457 := by
  unfold tailWord_1706015
  simp only [CollatzResearch.WordTrace]
  refine ⟨62223478914406494010423499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41482319276270996006948999 62223478914406494010423499)
  ·
    refine ⟨93335218371609741015635249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62223478914406494010423499 93335218371609741015635249)
    ·
      refine ⟨70001413778707305761726437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93335218371609741015635249 70001413778707305761726437)
      ·
        refine ⟨13125265083507619830323707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70001413778707305761726437 13125265083507619830323707)
        ·
          refine ⟨19687897625261429745485561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13125265083507619830323707 19687897625261429745485561)
          ·
            refine ⟨14765923218946072309114171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19687897625261429745485561 14765923218946072309114171)
            ·
              refine ⟨22148884828419108463671257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14765923218946072309114171 22148884828419108463671257)
              ·
                refine ⟨16611663621314331347753443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22148884828419108463671257 16611663621314331347753443)
                ·
                  refine ⟨24917495431971497021630165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16611663621314331347753443 24917495431971497021630165)
                  ·
                    refine ⟨584003799186831961444457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24917495431971497021630165 584003799186831961444457)
                    ·
                      rfl

theorem cell22_1706015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_1706015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706015 prefixEnd_1706015 := by exact prefixLift 1706015
  have htrace : WordTrace (prefixWord ++ tailWord_1706015) baseStart_1706015 baseEnd_1706015 := by
    simpa [prefixWord, tailWord_1706015, baseEnd_1706015] using wordTrace_append hprefix tailTrace_1706015
  have hstable : (prefixWord ++ tailWord_1706015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706015).length < 2 ^ (prefixWord ++ tailWord_1706015).sum := by decide
  have hdescent : baseEnd_1706015 < baseStart_1706015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706021 : List Nat := [1, 3, 1, 2, 2, 4, 2, 3, 1, 3]
def baseStart_1706021 : Nat := 118140960795 + 1706021 * 2 ^ 59
def prefixEnd_1706021 : Nat := 4983230072969 + 3 ^ 40 * 1706021 * 2
def baseEnd_1706021 : Nat := 584005853109449945794439

theorem tailTrace_1706021 : CollatzResearch.WordTrace tailWord_1706021 prefixEnd_1706021 584005853109449945794439 := by
  unfold tailWord_1706021
  simp only [CollatzResearch.WordTrace]
  refine ⟨62223697752384757035141917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41482465168256504690094611 62223697752384757035141917)
  ·
    refine ⟨23333886657144283888178219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62223697752384757035141917 23333886657144283888178219)
    ·
      refine ⟨35000829985716425832267329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23333886657144283888178219 35000829985716425832267329)
      ·
        refine ⟨26250622489287319374200497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35000829985716425832267329 26250622489287319374200497)
        ·
          refine ⟨19687966866965489530650373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26250622489287319374200497 19687966866965489530650373)
          ·
            refine ⟨3691493787556029286996945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19687966866965489530650373 3691493787556029286996945)
            ·
              refine ⟨2768620340667021965247709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3691493787556029286996945 2768620340667021965247709)
              ·
                refine ⟨1038232627750133236967891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2768620340667021965247709 1038232627750133236967891)
                ·
                  refine ⟨1557348941625199855451837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1038232627750133236967891 1557348941625199855451837)
                  ·
                    refine ⟨584005853109449945794439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1557348941625199855451837 584005853109449945794439)
                    ·
                      rfl

theorem cell22_1706021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 1, 3].length) (baseStart_1706021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706021 prefixEnd_1706021 := by exact prefixLift 1706021
  have htrace : WordTrace (prefixWord ++ tailWord_1706021) baseStart_1706021 baseEnd_1706021 := by
    simpa [prefixWord, tailWord_1706021, baseEnd_1706021] using wordTrace_append hprefix tailTrace_1706021
  have hstable : (prefixWord ++ tailWord_1706021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706021).length < 2 ^ (prefixWord ++ tailWord_1706021).sum := by decide
  have hdescent : baseEnd_1706021 < baseStart_1706021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706034 : List Nat := [3, 2, 1, 1, 2, 5, 1, 2, 5]
def baseStart_1706034 : Nat := 118140960795 + 1706034 * 2 ^ 59
def prefixEnd_1706034 : Nat := 4983230072969 + 3 ^ 40 * 1706034 * 2
def baseEnd_1706034 : Nat := 194670101091707415073133

theorem tailTrace_1706034 : CollatzResearch.WordTrace tailWord_1706034 prefixEnd_1706034 194670101091707415073133 := by
  unfold tailWord_1706034
  simp only [CollatzResearch.WordTrace]
  refine ⟨15556042975334415063841289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41482781267558440170243437 15556042975334415063841289)
  ·
    refine ⟨11667032231500811297880967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15556042975334415063841289 11667032231500811297880967)
    ·
      refine ⟨17500548347251216946821451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11667032231500811297880967 17500548347251216946821451)
      ·
        refine ⟨26250822520876825420232177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17500548347251216946821451 26250822520876825420232177)
        ·
          refine ⟨19688116890657619065174133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26250822520876825420232177 19688116890657619065174133)
          ·
            refine ⟨1845760958499151787360075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19688116890657619065174133 1845760958499151787360075)
            ·
              refine ⟨2768641437748727681040113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1845760958499151787360075 2768641437748727681040113)
              ·
                refine ⟨2076481078311545760780085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2768641437748727681040113 2076481078311545760780085)
                ·
                  refine ⟨194670101091707415073133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2076481078311545760780085 194670101091707415073133)
                  ·
                    rfl

theorem cell22_1706034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_1706034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706034 prefixEnd_1706034 := by exact prefixLift 1706034
  have htrace : WordTrace (prefixWord ++ tailWord_1706034) baseStart_1706034 baseEnd_1706034 := by
    simpa [prefixWord, tailWord_1706034, baseEnd_1706034] using wordTrace_append hprefix tailTrace_1706034
  have hstable : (prefixWord ++ tailWord_1706034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706034).length < 2 ^ (prefixWord ++ tailWord_1706034).sum := by decide
  have hdescent : baseEnd_1706034 < baseStart_1706034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706062 : List Nat := [4, 1, 1, 1, 1, 4, 2, 2, 6]
def baseStart_1706062 : Nat := 118140960795 + 1706062 * 2 ^ 59
def prefixEnd_1706062 : Nat := 4983230072969 + 3 ^ 40 * 1706062 * 2
def baseEnd_1706062 : Nat := 194673296082446501839771

theorem tailTrace_1706062 : CollatzResearch.WordTrace tailWord_1706062 prefixEnd_1706062 194673296082446501839771 := by
  unfold tailWord_1706062
  simp only [CollatzResearch.WordTrace]
  refine ⟨7778149143154527629673055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41483462096824147358256293 7778149143154527629673055)
  ·
    refine ⟨11667223714731791444509583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7778149143154527629673055 11667223714731791444509583)
    ·
      refine ⟨17500835572097687166764375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11667223714731791444509583 17500835572097687166764375)
      ·
        refine ⟨26251253358146530750146563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17500835572097687166764375 26251253358146530750146563)
        ·
          refine ⟨39376880037219796125219845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26251253358146530750146563 39376880037219796125219845)
          ·
            refine ⟨7383165006978711773478721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39376880037219796125219845 7383165006978711773478721)
            ·
              refine ⟨5537373755234033830109041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7383165006978711773478721 5537373755234033830109041)
              ·
                refine ⟨4153030316425525372581781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5537373755234033830109041 4153030316425525372581781)
                ·
                  refine ⟨194673296082446501839771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4153030316425525372581781 194673296082446501839771)
                  ·
                    rfl

theorem cell22_1706062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_1706062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706062 prefixEnd_1706062 := by exact prefixLift 1706062
  have htrace : WordTrace (prefixWord ++ tailWord_1706062) baseStart_1706062 baseEnd_1706062 := by
    simpa [prefixWord, tailWord_1706062, baseEnd_1706062] using wordTrace_append hprefix tailTrace_1706062
  have hstable : (prefixWord ++ tailWord_1706062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706062).length < 2 ^ (prefixWord ++ tailWord_1706062).sum := by decide
  have hdescent : baseEnd_1706062 < baseStart_1706062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706092 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 4, 4]
def baseStart_1706092 : Nat := 118140960795 + 1706092 * 2 ^ 59
def prefixEnd_1706092 : Nat := 4983230072969 + 3 ^ 40 * 1706092 * 2
def baseEnd_1706092 : Nat := 584030157860429427269221

theorem tailTrace_1706092 : CollatzResearch.WordTrace tailWord_1706092 prefixEnd_1706092 584030157860429427269221 := by
  unfold tailWord_1706092
  simp only [CollatzResearch.WordTrace]
  refine ⟨31113143667563768080488265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41484191556751690773984353 31113143667563768080488265)
  ·
    refine ⟨23334857750672826060366199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31113143667563768080488265 23334857750672826060366199)
    ·
      refine ⟨35002286626009239090549299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23334857750672826060366199 35002286626009239090549299)
      ·
        refine ⟨52503429939013858635823949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35002286626009239090549299 52503429939013858635823949)
        ·
          refine ⟨19688786227130196988433981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52503429939013858635823949 19688786227130196988433981)
          ·
            refine ⟨7383294835173823870662743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19688786227130196988433981 7383294835173823870662743)
            ·
              refine ⟨11074942252760735805994115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7383294835173823870662743 11074942252760735805994115)
              ·
                refine ⟨16612413379141103708991173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11074942252760735805994115 16612413379141103708991173)
                ·
                  refine ⟨3114827508588956945435845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16612413379141103708991173 3114827508588956945435845)
                  ·
                    refine ⟨584030157860429427269221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3114827508588956945435845 584030157860429427269221)
                    ·
                      rfl

theorem cell22_1706092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_1706092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706092 prefixEnd_1706092 := by exact prefixLift 1706092
  have htrace : WordTrace (prefixWord ++ tailWord_1706092) baseStart_1706092 baseEnd_1706092 := by
    simpa [prefixWord, tailWord_1706092, baseEnd_1706092] using wordTrace_append hprefix tailTrace_1706092
  have hstable : (prefixWord ++ tailWord_1706092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706092).length < 2 ^ (prefixWord ++ tailWord_1706092).sum := by decide
  have hdescent : baseEnd_1706092 < baseStart_1706092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706094 : List Nat := [4, 1, 2, 2, 1, 1, 1, 3, 4, 3]
def baseStart_1706094 : Nat := 118140960795 + 1706094 * 2 ^ 59
def prefixEnd_1706094 : Nat := 4983230072969 + 3 ^ 40 * 1706094 * 2
def baseEnd_1706094 : Nat := 584030842501302088719215

theorem tailTrace_1706094 : CollatzResearch.WordTrace tailWord_1706094 prefixEnd_1706094 584030842501302088719215 := by
  unfold tailWord_1706094
  simp only [CollatzResearch.WordTrace]
  refine ⟨7778295035140036312818667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41484240187413527001699557 7778295035140036312818667)
  ·
    refine ⟨11667442552710054469228001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7778295035140036312818667 11667442552710054469228001)
    ·
      refine ⟨8750581914532540851921001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11667442552710054469228001 8750581914532540851921001)
      ·
        refine ⟨6562936435899405638940751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8750581914532540851921001 6562936435899405638940751)
        ·
          refine ⟨9844404653849108458411127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6562936435899405638940751 9844404653849108458411127)
          ·
            refine ⟨14766606980773662687616691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9844404653849108458411127 14766606980773662687616691)
            ·
              refine ⟨22149910471160494031425037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14766606980773662687616691 22149910471160494031425037)
              ·
                refine ⟨8306216426685185261784389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22149910471160494031425037 8306216426685185261784389)
                ·
                  refine ⟨1557415580003472236584573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8306216426685185261784389 1557415580003472236584573)
                  ·
                    refine ⟨584030842501302088719215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1557415580003472236584573 584030842501302088719215)
                    ·
                      rfl

theorem cell22_1706094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_1706094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706094 prefixEnd_1706094 := by exact prefixLift 1706094
  have htrace : WordTrace (prefixWord ++ tailWord_1706094) baseStart_1706094 baseEnd_1706094 := by
    simpa [prefixWord, tailWord_1706094, baseEnd_1706094] using wordTrace_append hprefix tailTrace_1706094
  have hstable : (prefixWord ++ tailWord_1706094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706094).length < 2 ^ (prefixWord ++ tailWord_1706094).sum := by decide
  have hdescent : baseEnd_1706094 < baseStart_1706094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706096 : List Nat := [2, 1, 1, 1, 5, 3, 3, 2, 4]
def baseStart_1706096 : Nat := 118140960795 + 1706096 * 2 ^ 59
def prefixEnd_1706096 : Nat := 4983230072969 + 3 ^ 40 * 1706096 * 2
def baseEnd_1706096 : Nat := 194677175714058250056403

theorem tailTrace_1706096 : CollatzResearch.WordTrace tailWord_1706096 prefixEnd_1706096 194677175714058250056403 := by
  unfold tailWord_1706096
  simp only [CollatzResearch.WordTrace]
  refine ⟨31113216613556522422061071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41484288818075363229414761 31113216613556522422061071)
  ·
    refine ⟨46669824920334783633091607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31113216613556522422061071 46669824920334783633091607)
    ·
      refine ⟨70004737380502175449637411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46669824920334783633091607 70004737380502175449637411)
      ·
        refine ⟨105007106070753263174456117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70004737380502175449637411 105007106070753263174456117)
        ·
          refine ⟨9844416194133118422605261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105007106070753263174456117 9844416194133118422605261)
          ·
            refine ⟨3691656072799919408476973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9844416194133118422605261 3691656072799919408476973)
            ·
              refine ⟨1384371027299969778178865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3691656072799919408476973 1384371027299969778178865)
              ·
                refine ⟨1038278270474977333634149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1384371027299969778178865 1038278270474977333634149)
                ·
                  refine ⟨194677175714058250056403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1038278270474977333634149 194677175714058250056403)
                  ·
                    rfl

theorem cell22_1706096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 4].length) (baseStart_1706096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706096 prefixEnd_1706096 := by exact prefixLift 1706096
  have htrace : WordTrace (prefixWord ++ tailWord_1706096) baseStart_1706096 baseEnd_1706096 := by
    simpa [prefixWord, tailWord_1706096, baseEnd_1706096] using wordTrace_append hprefix tailTrace_1706096
  have hstable : (prefixWord ++ tailWord_1706096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706096).length < 2 ^ (prefixWord ++ tailWord_1706096).sum := by decide
  have hdescent : baseEnd_1706096 < baseStart_1706096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706126 : List Nat := [4, 1, 1, 3, 3, 1, 2, 1, 2, 4]
def baseStart_1706126 : Nat := 118140960795 + 1706126 * 2 ^ 59
def prefixEnd_1706126 : Nat := 4983230072969 + 3 ^ 40 * 1706126 * 2
def baseEnd_1706126 : Nat := 584041796755264671919117

theorem tailTrace_1706126 : CollatzResearch.WordTrace tailWord_1706126 prefixEnd_1706126 584041796755264671919117 := by
  unfold tailWord_1706126
  simp only [CollatzResearch.WordTrace]
  refine ⟨7778440927125544995964279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41485018278002906645142821 7778440927125544995964279)
  ·
    refine ⟨11667661390688317493946419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7778440927125544995964279 11667661390688317493946419)
    ·
      refine ⟨17501492086032476240919629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11667661390688317493946419 17501492086032476240919629)
      ·
        refine ⟨6563059532262178590344861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17501492086032476240919629 6563059532262178590344861)
        ·
          refine ⟨2461147324598316971379323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6563059532262178590344861 2461147324598316971379323)
          ·
            refine ⟨3691720986897475457068985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2461147324598316971379323 3691720986897475457068985)
            ·
              refine ⟨2768790740173106592801739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3691720986897475457068985 2768790740173106592801739)
              ·
                refine ⟨4153186110259659889202609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2768790740173106592801739 4153186110259659889202609)
                ·
                  refine ⟨3114889582694744916901957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4153186110259659889202609 3114889582694744916901957)
                  ·
                    refine ⟨584041796755264671919117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3114889582694744916901957 584041796755264671919117)
                    ·
                      rfl

theorem cell22_1706126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_1706126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706126 prefixEnd_1706126 := by exact prefixLift 1706126
  have htrace : WordTrace (prefixWord ++ tailWord_1706126) baseStart_1706126 baseEnd_1706126 := by
    simpa [prefixWord, tailWord_1706126, baseEnd_1706126] using wordTrace_append hprefix tailTrace_1706126
  have hstable : (prefixWord ++ tailWord_1706126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706126).length < 2 ^ (prefixWord ++ tailWord_1706126).sum := by decide
  have hdescent : baseEnd_1706126 < baseStart_1706126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706158 : List Nat := [4, 1, 4, 2, 1, 2, 1, 7]
def baseStart_1706158 : Nat := 118140960795 + 1706158 * 2 ^ 59
def prefixEnd_1706158 : Nat := 4983230072969 + 3 ^ 40 * 1706158 * 2
def baseEnd_1706158 : Nat := 64894750112136361679891

theorem tailTrace_1706158 : CollatzResearch.WordTrace tailWord_1706158 prefixEnd_1706158 64894750112136361679891 := by
  unfold tailWord_1706158
  simp only [CollatzResearch.WordTrace]
  refine ⟨7778586819111053679109891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41485796368592286288586085 7778586819111053679109891)
  ·
    refine ⟨11667880228666580518664837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7778586819111053679109891 11667880228666580518664837)
    ·
      refine ⟨2187727542874983847249657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11667880228666580518664837 2187727542874983847249657)
      ·
        refine ⟨1640795657156237885437243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2187727542874983847249657 1640795657156237885437243)
        ·
          refine ⟨2461193485734356828155865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1640795657156237885437243 2461193485734356828155865)
          ·
            refine ⟨1845895114300767621116899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2461193485734356828155865 1845895114300767621116899)
            ·
              refine ⟨2768842671451151431675349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1845895114300767621116899 2768842671451151431675349)
              ·
                refine ⟨64894750112136361679891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2768842671451151431675349 64894750112136361679891)
                ·
                  rfl

theorem cell22_1706158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_1706158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706158 prefixEnd_1706158 := by exact prefixLift 1706158
  have htrace : WordTrace (prefixWord ++ tailWord_1706158) baseStart_1706158 baseEnd_1706158 := by
    simpa [prefixWord, tailWord_1706158, baseEnd_1706158] using wordTrace_append hprefix tailTrace_1706158
  have hstable : (prefixWord ++ tailWord_1706158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706158).length < 2 ^ (prefixWord ++ tailWord_1706158).sum := by decide
  have hdescent : baseEnd_1706158 < baseStart_1706158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706167 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 1, 7]
def baseStart_1706167 : Nat := 118140960795 + 1706167 * 2 ^ 59
def prefixEnd_1706167 : Nat := 4983230072969 + 3 ^ 40 * 1706167 * 2
def baseEnd_1706167 : Nat := 584055831893154231643991

theorem tailTrace_1706167 : CollatzResearch.WordTrace tailWord_1706167 prefixEnd_1706167 584055831893154231643991 := by
  unfold tailWord_1706167
  simp only [CollatzResearch.WordTrace]
  refine ⟨62229022809855823969956755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41486015206570549313304503 62229022809855823969956755)
  ·
    refine ⟨93343534214783735954935133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62229022809855823969956755 93343534214783735954935133)
    ·
      refine ⟨35003825330543900983100675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93343534214783735954935133 35003825330543900983100675)
      ·
        refine ⟨52505737995815851474651013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35003825330543900983100675 52505737995815851474651013)
        ·
          refine ⟨9844825874215472151497065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52505737995815851474651013 9844825874215472151497065)
          ·
            refine ⟨7383619405661604113622799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9844825874215472151497065 7383619405661604113622799)
            ·
              refine ⟨11075429108492406170434199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7383619405661604113622799 11075429108492406170434199)
              ·
                refine ⟨16613143662738609255651299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11075429108492406170434199 16613143662738609255651299)
                ·
                  refine ⟨24919715494107913883476949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16613143662738609255651299 24919715494107913883476949)
                  ·
                    refine ⟨584055831893154231643991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24919715494107913883476949 584055831893154231643991)
                    ·
                      rfl

theorem cell22_1706167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_1706167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706167 prefixEnd_1706167 := by exact prefixLift 1706167
  have htrace : WordTrace (prefixWord ++ tailWord_1706167) baseStart_1706167 baseEnd_1706167 := by
    simpa [prefixWord, tailWord_1706167, baseEnd_1706167] using wordTrace_append hprefix tailTrace_1706167
  have hstable : (prefixWord ++ tailWord_1706167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706167).length < 2 ^ (prefixWord ++ tailWord_1706167).sum := by decide
  have hdescent : baseEnd_1706167 < baseStart_1706167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706227 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 3, 6]
def baseStart_1706227 : Nat := 118140960795 + 1706227 * 2 ^ 59
def prefixEnd_1706227 : Nat := 4983230072969 + 3 ^ 40 * 1706227 * 2
def baseEnd_1706227 : Nat := 584076371119334075143807

theorem tailTrace_1706227 : CollatzResearch.WordTrace tailWord_1706227 prefixEnd_1706227 584076371119334075143807 := by
  unfold tailWord_1706227
  simp only [CollatzResearch.WordTrace]
  refine ⟨62231211189638454217140935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41487474126425636144760623 62231211189638454217140935)
  ·
    refine ⟨93346816784457681325711403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62231211189638454217140935 93346816784457681325711403)
    ·
      refine ⟨140020225176686521988567105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93346816784457681325711403 140020225176686521988567105)
      ·
        refine ⟨105015168882514891491425329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140020225176686521988567105 105015168882514891491425329)
        ·
          refine ⟨78761376661886168618568997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105015168882514891491425329 78761376661886168618568997)
          ·
            refine ⟨14767758124103656615981687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78761376661886168618568997 14767758124103656615981687)
            ·
              refine ⟨22151637186155484923972531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14767758124103656615981687 22151637186155484923972531)
              ·
                refine ⟨33227455779233227385958797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22151637186155484923972531 33227455779233227385958797)
                ·
                  refine ⟨12460295917212460269734549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33227455779233227385958797 12460295917212460269734549)
                  ·
                    refine ⟨584076371119334075143807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12460295917212460269734549 584076371119334075143807)
                    ·
                      rfl

theorem cell22_1706227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 6].length) (baseStart_1706227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706227 prefixEnd_1706227 := by exact prefixLift 1706227
  have htrace : WordTrace (prefixWord ++ tailWord_1706227) baseStart_1706227 baseEnd_1706227 := by
    simpa [prefixWord, tailWord_1706227, baseEnd_1706227] using wordTrace_append hprefix tailTrace_1706227
  have hstable : (prefixWord ++ tailWord_1706227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706227).length < 2 ^ (prefixWord ++ tailWord_1706227).sum := by decide
  have hdescent : baseEnd_1706227 < baseStart_1706227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706248 : List Nat := [2, 1, 3, 2, 3, 3, 1, 3, 4]
def baseStart_1706248 : Nat := 118140960795 + 1706248 * 2 ^ 59
def prefixEnd_1706248 : Nat := 4983230072969 + 3 ^ 40 * 1706248 * 2
def baseEnd_1706248 : Nat := 194694519949499006789581

theorem tailTrace_1706248 : CollatzResearch.WordTrace tailWord_1706248 prefixEnd_1706248 194694519949499006789581 := by
  unfold tailWord_1706248
  simp only [CollatzResearch.WordTrace]
  refine ⟨31115988561281187401827699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41487984748374916535770265 31115988561281187401827699)
  ·
    refine ⟨46673982841921781102741549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31115988561281187401827699 46673982841921781102741549)
    ·
      refine ⟨17502743565720667913528081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46673982841921781102741549 17502743565720667913528081)
      ·
        refine ⟨13127057674290500935146061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17502743565720667913528081 13127057674290500935146061)
        ·
          refine ⟨4922646627858937850679773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13127057674290500935146061 4922646627858937850679773)
          ·
            refine ⟨1845992485447101694004915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4922646627858937850679773 1845992485447101694004915)
            ·
              refine ⟨2768988728170652541007373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1845992485447101694004915 2768988728170652541007373)
              ·
                refine ⟨1038370773063994702877765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2768988728170652541007373 1038370773063994702877765)
                ·
                  refine ⟨194694519949499006789581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1038370773063994702877765 194694519949499006789581)
                  ·
                    rfl

theorem cell22_1706248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 4].length) (baseStart_1706248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706248 prefixEnd_1706248 := by exact prefixLift 1706248
  have htrace : WordTrace (prefixWord ++ tailWord_1706248) baseStart_1706248 baseEnd_1706248 := by
    simpa [prefixWord, tailWord_1706248, baseEnd_1706248] using wordTrace_append hprefix tailTrace_1706248
  have hstable : (prefixWord ++ tailWord_1706248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706248).length < 2 ^ (prefixWord ++ tailWord_1706248).sum := by decide
  have hdescent : baseEnd_1706248 < baseStart_1706248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706321 : List Nat := [1, 2, 2, 1, 4, 3, 2, 2, 5]
def baseStart_1706321 : Nat := 118140960795 + 1706321 * 2 ^ 59
def prefixEnd_1706321 : Nat := 4983230072969 + 3 ^ 40 * 1706321 * 2
def baseEnd_1706321 : Nat := 194702849746783054431173

theorem tailTrace_1706321 : CollatzResearch.WordTrace tailWord_1706321 prefixEnd_1706321 194702849746783054431173 := by
  unfold tailWord_1706321
  simp only [CollatzResearch.WordTrace]
  refine ⟨62234639651297908271062817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41489759767531938847375211 62234639651297908271062817)
  ·
    refine ⟨46675979738473431203297113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62234639651297908271062817 46675979738473431203297113)
    ·
      refine ⟨35006984803855073402472835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46675979738473431203297113 35006984803855073402472835)
      ·
        refine ⟨52510477205782610103709253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35006984803855073402472835 52510477205782610103709253)
        ·
          refine ⟨9845714476084239394445485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52510477205782610103709253 9845714476084239394445485)
          ·
            refine ⟨3692142928531589772917057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9845714476084239394445485 3692142928531589772917057)
            ·
              refine ⟨2769107196398692329687793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3692142928531589772917057 2769107196398692329687793)
              ·
                refine ⟨2076830397299019247265845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2769107196398692329687793 2076830397299019247265845)
                ·
                  refine ⟨194702849746783054431173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2076830397299019247265845 194702849746783054431173)
                  ·
                    rfl

theorem cell22_1706321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 5].length) (baseStart_1706321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706321 prefixEnd_1706321 := by exact prefixLift 1706321
  have htrace : WordTrace (prefixWord ++ tailWord_1706321) baseStart_1706321 baseEnd_1706321 := by
    simpa [prefixWord, tailWord_1706321, baseEnd_1706321] using wordTrace_append hprefix tailTrace_1706321
  have hstable : (prefixWord ++ tailWord_1706321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706321).length < 2 ^ (prefixWord ++ tailWord_1706321).sum := by decide
  have hdescent : baseEnd_1706321 < baseStart_1706321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706325 : List Nat := [1, 3, 2, 2, 4, 1, 1, 4, 1, 3]
def baseStart_1706325 : Nat := 118140960795 + 1706325 * 2 ^ 59
def prefixEnd_1706325 : Nat := 4983230072969 + 3 ^ 40 * 1706325 * 2
def baseEnd_1706325 : Nat := 584109918522094486193507

theorem tailTrace_1706325 : CollatzResearch.WordTrace tailWord_1706325 prefixEnd_1706325 584109918522094486193507 := by
  unfold tailWord_1706325
  simp only [CollatzResearch.WordTrace]
  refine ⟨62234785543283416954208429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41489857028855611302805619 62234785543283416954208429)
  ·
    refine ⟨23338044578731281357828161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62234785543283416954208429 23338044578731281357828161)
    ·
      refine ⟨17503533434048461018371121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23338044578731281357828161 17503533434048461018371121)
      ·
        refine ⟨13127650075536345763778341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17503533434048461018371121 13127650075536345763778341)
        ·
          refine ⟨2461434389163064830708439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13127650075536345763778341 2461434389163064830708439)
          ·
            refine ⟨3692151583744597246062659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2461434389163064830708439 3692151583744597246062659)
            ·
              refine ⟨5538227375616895869093989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3692151583744597246062659 5538227375616895869093989)
              ·
                refine ⟨1038417632928167975455123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5538227375616895869093989 1038417632928167975455123)
                ·
                  refine ⟨1557626449392251963182685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1038417632928167975455123 1557626449392251963182685)
                  ·
                    refine ⟨584109918522094486193507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1557626449392251963182685 584109918522094486193507)
                    ·
                      rfl

theorem cell22_1706325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_1706325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706325 prefixEnd_1706325 := by exact prefixLift 1706325
  have htrace : WordTrace (prefixWord ++ tailWord_1706325) baseStart_1706325 baseEnd_1706325 := by
    simpa [prefixWord, tailWord_1706325, baseEnd_1706325] using wordTrace_append hprefix tailTrace_1706325
  have hstable : (prefixWord ++ tailWord_1706325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706325).length < 2 ^ (prefixWord ++ tailWord_1706325).sum := by decide
  have hdescent : baseEnd_1706325 < baseStart_1706325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706336 : List Nat := [2, 1, 1, 3, 5, 1, 1, 1, 2, 5]
def baseStart_1706336 : Nat := 118140960795 + 1706336 * 2 ^ 59
def prefixEnd_1706336 : Nat := 4983230072969 + 3 ^ 40 * 1706336 * 2
def baseEnd_1706336 : Nat := 584113684046894124168473

theorem tailTrace_1706336 : CollatzResearch.WordTrace tailWord_1706336 prefixEnd_1706336 584113684046894124168473 := by
  unfold tailWord_1706336
  simp only [CollatzResearch.WordTrace]
  refine ⟨31117593373121782916429431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41490124497495710555239241 31117593373121782916429431)
  ·
    refine ⟨46676390059682674374644147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31117593373121782916429431 46676390059682674374644147)
    ·
      refine ⟨70014585089524011561966221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46676390059682674374644147 70014585089524011561966221)
      ·
        refine ⟨26255469408571504335737333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70014585089524011561966221 26255469408571504335737333)
        ·
          refine ⟨2461450257053578531475375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26255469408571504335737333 2461450257053578531475375)
          ·
            refine ⟨3692175385580367797213063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2461450257053578531475375 3692175385580367797213063)
            ·
              refine ⟨5538263078370551695819595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3692175385580367797213063 5538263078370551695819595)
              ·
                refine ⟨8307394617555827543729393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5538263078370551695819595 8307394617555827543729393)
                ·
                  refine ⟨6230545963166870657797045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8307394617555827543729393 6230545963166870657797045)
                  ·
                    refine ⟨584113684046894124168473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6230545963166870657797045 584113684046894124168473)
                    ·
                      rfl

theorem cell22_1706336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 2, 5].length) (baseStart_1706336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706336 prefixEnd_1706336 := by exact prefixLift 1706336
  have htrace : WordTrace (prefixWord ++ tailWord_1706336) baseStart_1706336 baseEnd_1706336 := by
    simpa [prefixWord, tailWord_1706336, baseEnd_1706336] using wordTrace_append hprefix tailTrace_1706336
  have hstable : (prefixWord ++ tailWord_1706336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706336).length < 2 ^ (prefixWord ++ tailWord_1706336).sum := by decide
  have hdescent : baseEnd_1706336 < baseStart_1706336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706364 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 3, 5]
def baseStart_1706364 : Nat := 118140960795 + 1706364 * 2 ^ 59
def prefixEnd_1706364 : Nat := 4983230072969 + 3 ^ 40 * 1706364 * 2
def baseEnd_1706364 : Nat := 584123269019111384468387

theorem tailTrace_1706364 : CollatzResearch.WordTrace tailWord_1706364 prefixEnd_1706364 584123269019111384468387 := by
  unfold tailWord_1706364
  simp only [CollatzResearch.WordTrace]
  refine ⟨31118103995071063307439073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41490805326761417743252097 31118103995071063307439073)
  ·
    refine ⟨23338577996303297480579305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31118103995071063307439073 23338577996303297480579305)
    ·
      refine ⟨17503933497227473110434479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23338577996303297480579305 17503933497227473110434479)
      ·
        refine ⟨26255900245841209665651719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17503933497227473110434479 26255900245841209665651719)
        ·
          refine ⟨39383850368761814498477579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26255900245841209665651719 39383850368761814498477579)
          ·
            refine ⟨59075775553142721747716369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39383850368761814498477579 59075775553142721747716369)
            ·
              refine ⟨44306831664857041310787277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59075775553142721747716369 44306831664857041310787277)
              ·
                refine ⟨16615061874321390491545229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44306831664857041310787277 16615061874321390491545229)
                ·
                  refine ⟨6230648202870521434329461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16615061874321390491545229 6230648202870521434329461)
                  ·
                    refine ⟨584123269019111384468387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6230648202870521434329461 584123269019111384468387)
                    ·
                      rfl

theorem cell22_1706364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_1706364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706364 prefixEnd_1706364 := by exact prefixLift 1706364
  have htrace : WordTrace (prefixWord ++ tailWord_1706364) baseStart_1706364 baseEnd_1706364 := by
    simpa [prefixWord, tailWord_1706364, baseEnd_1706364] using wordTrace_append hprefix tailTrace_1706364
  have hstable : (prefixWord ++ tailWord_1706364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706364).length < 2 ^ (prefixWord ++ tailWord_1706364).sum := by decide
  have hdescent : baseEnd_1706364 < baseStart_1706364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706424 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 1, 8]
def baseStart_1706424 : Nat := 118140960795 + 1706424 * 2 ^ 59
def prefixEnd_1706424 : Nat := 4983230072969 + 3 ^ 40 * 1706424 * 2
def baseEnd_1706424 : Nat := 584143808245291227968203

theorem tailTrace_1706424 : CollatzResearch.WordTrace tailWord_1706424 prefixEnd_1706424 584143808245291227968203 := by
  unfold tailWord_1706424
  simp only [CollatzResearch.WordTrace]
  refine ⟨31119198184962378431031163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41492264246616504574708217 31119198184962378431031163)
  ·
    refine ⟨46678797277443567646546745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31119198184962378431031163 46678797277443567646546745)
    ·
      refine ⟨35009097958082675734910059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46678797277443567646546745 35009097958082675734910059)
      ·
        refine ⟨52513646937124013602365089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35009097958082675734910059 52513646937124013602365089)
        ·
          refine ⟨39385235202843010201773817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52513646937124013602365089 39385235202843010201773817)
          ·
            refine ⟨29538926402132257651330363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39385235202843010201773817 29538926402132257651330363)
            ·
              refine ⟨44308389603198386476995545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29538926402132257651330363 44308389603198386476995545)
              ·
                refine ⟨33231292202398789857746659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44308389603198386476995545 33231292202398789857746659)
                ·
                  refine ⟨49846938303598184786619989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33231292202398789857746659 49846938303598184786619989)
                  ·
                    refine ⟨584143808245291227968203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49846938303598184786619989 584143808245291227968203)
                    ·
                      rfl

theorem cell22_1706424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_1706424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706424 prefixEnd_1706424 := by exact prefixLift 1706424
  have htrace : WordTrace (prefixWord ++ tailWord_1706424) baseStart_1706424 baseEnd_1706424 := by
    simpa [prefixWord, tailWord_1706424, baseEnd_1706424] using wordTrace_append hprefix tailTrace_1706424
  have hstable : (prefixWord ++ tailWord_1706424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706424).length < 2 ^ (prefixWord ++ tailWord_1706424).sum := by decide
  have hdescent : baseEnd_1706424 < baseStart_1706424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706426 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 5, 3]
def baseStart_1706426 : Nat := 118140960795 + 1706426 * 2 ^ 59
def prefixEnd_1706426 : Nat := 4983230072969 + 3 ^ 40 * 1706426 * 2
def baseEnd_1706426 : Nat := 584144492886163889418197

theorem tailTrace_1706426 : CollatzResearch.WordTrace tailWord_1706426 prefixEnd_1706426 584144492886163889418197 := by
  unfold tailWord_1706426
  simp only [CollatzResearch.WordTrace]
  refine ⟨15559617328979377800908783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41492312877278340802423421 15559617328979377800908783)
  ·
    refine ⟨23339425993469066701363175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15559617328979377800908783 23339425993469066701363175)
    ·
      refine ⟨35009138990203600052044763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23339425993469066701363175 35009138990203600052044763)
      ·
        refine ⟨52513708485305400078067145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35009138990203600052044763 52513708485305400078067145)
        ·
          refine ⟨39385281363979050058550359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52513708485305400078067145 39385281363979050058550359)
          ·
            refine ⟨59077922045968575087825539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39385281363979050058550359 59077922045968575087825539)
            ·
              refine ⟨88616883068952862631738309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59077922045968575087825539 88616883068952862631738309)
              ·
                refine ⟨16615665575428661743450933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88616883068952862631738309 16615665575428661743450933)
                ·
                  refine ⟨1557718647696437038448525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16615665575428661743450933 1557718647696437038448525)
                  ·
                    refine ⟨584144492886163889418197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1557718647696437038448525 584144492886163889418197)
                    ·
                      rfl

theorem cell22_1706426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 5, 3].length) (baseStart_1706426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706426 prefixEnd_1706426 := by exact prefixLift 1706426
  have htrace : WordTrace (prefixWord ++ tailWord_1706426) baseStart_1706426 baseEnd_1706426 := by
    simpa [prefixWord, tailWord_1706426, baseEnd_1706426] using wordTrace_append hprefix tailTrace_1706426
  have hstable : (prefixWord ++ tailWord_1706426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706426).length < 2 ^ (prefixWord ++ tailWord_1706426).sum := by decide
  have hdescent : baseEnd_1706426 < baseStart_1706426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706541 : List Nat := [1, 5, 4, 1, 2, 1, 1, 2, 5]
def baseStart_1706541 : Nat := 118140960795 + 1706541 * 2 ^ 59
def prefixEnd_1706541 : Nat := 4983230072969 + 3 ^ 40 * 1706541 * 2
def baseEnd_1706541 : Nat := 194727953245447307597615

theorem tailTrace_1706541 : CollatzResearch.WordTrace tailWord_1706541 prefixEnd_1706541 194727953245447307597615 := by
  unfold tailWord_1706541
  simp only [CollatzResearch.WordTrace]
  refine ⟨62242663710500885844071477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41495109140333923896047651 62242663710500885844071477)
  ·
    refine ⟨5835249722859458047881701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62242663710500885844071477 5835249722859458047881701)
    ·
      refine ⟨1094109323036148383977819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5835249722859458047881701 1094109323036148383977819)
      ·
        refine ⟨1641163984554222575966729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1094109323036148383977819 1641163984554222575966729)
        ·
          refine ⟨1230872988415666931975047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1641163984554222575966729 1230872988415666931975047)
          ·
            refine ⟨1846309482623500397962571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1230872988415666931975047 1846309482623500397962571)
            ·
              refine ⟨2769464223935250596943857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1846309482623500397962571 2769464223935250596943857)
              ·
                refine ⟨2077098167951437947707893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2769464223935250596943857 2077098167951437947707893)
                ·
                  refine ⟨194727953245447307597615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2077098167951437947707893 194727953245447307597615)
                  ·
                    rfl

theorem cell22_1706541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_1706541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706541 prefixEnd_1706541 := by exact prefixLift 1706541
  have htrace : WordTrace (prefixWord ++ tailWord_1706541) baseStart_1706541 baseEnd_1706541 := by
    simpa [prefixWord, tailWord_1706541, baseEnd_1706541] using wordTrace_append hprefix tailTrace_1706541
  have hstable : (prefixWord ++ tailWord_1706541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706541).length < 2 ^ (prefixWord ++ tailWord_1706541).sum := by decide
  have hdescent : baseEnd_1706541 < baseStart_1706541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706567 : List Nat := [1, 1, 4, 1, 4, 2, 3, 1, 2, 3]
def baseStart_1706567 : Nat := 118140960795 + 1706567 * 2 ^ 59
def prefixEnd_1706567 : Nat := 4983230072969 + 3 ^ 40 * 1706567 * 2
def baseEnd_1706567 : Nat := 584192760067686521642765

theorem tailTrace_1706567 : CollatzResearch.WordTrace tailWord_1706567 prefixEnd_1706567 584192760067686521642765 := by
  unfold tailWord_1706567
  simp only [CollatzResearch.WordTrace]
  refine ⟨62243612008406692284517955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41495741338937794856345303 62243612008406692284517955)
  ·
    refine ⟨93365418012610038426776933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62243612008406692284517955 93365418012610038426776933)
    ·
      refine ⟨17506015877364382205020675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93365418012610038426776933 17506015877364382205020675)
      ·
        refine ⟨26259023816046573307531013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17506015877364382205020675 26259023816046573307531013)
        ·
          refine ⟨4923566965508732495162065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26259023816046573307531013 4923566965508732495162065)
          ·
            refine ⟨3692675224131549371371549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4923566965508732495162065 3692675224131549371371549)
            ·
              refine ⟨1384753209049331014264331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3692675224131549371371549 1384753209049331014264331)
              ·
                refine ⟨2077129813573996521396497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1384753209049331014264331 2077129813573996521396497)
                ·
                  refine ⟨1557847360180497391047373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2077129813573996521396497 1557847360180497391047373)
                  ·
                    refine ⟨584192760067686521642765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1557847360180497391047373 584192760067686521642765)
                    ·
                      rfl

theorem cell22_1706567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_1706567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706567 prefixEnd_1706567 := by exact prefixLift 1706567
  have htrace : WordTrace (prefixWord ++ tailWord_1706567) baseStart_1706567 baseEnd_1706567 := by
    simpa [prefixWord, tailWord_1706567, baseEnd_1706567] using wordTrace_append hprefix tailTrace_1706567
  have hstable : (prefixWord ++ tailWord_1706567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706567).length < 2 ^ (prefixWord ++ tailWord_1706567).sum := by decide
  have hdescent : baseEnd_1706567 < baseStart_1706567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706580 : List Nat := [2, 4, 1, 1, 1, 5, 2, 6]
def baseStart_1706580 : Nat := 118140960795 + 1706580 * 2 ^ 59
def prefixEnd_1706580 : Nat := 4983230072969 + 3 ^ 40 * 1706580 * 2
def baseEnd_1706580 : Nat := 64910801137039869007525

theorem tailTrace_1706580 : CollatzResearch.WordTrace tailWord_1706580 prefixEnd_1706580 64910801137039869007525 := by
  unfold tailWord_1706580
  simp only [CollatzResearch.WordTrace]
  refine ⟨31122043078679797752370597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41496057438239730336494129 31122043078679797752370597)
  ·
    refine ⟨5835383077252462078569487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31122043078679797752370597 5835383077252462078569487)
    ·
      refine ⟨8753074615878693117854231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5835383077252462078569487 8753074615878693117854231)
      ·
        refine ⟨13129611923818039676781347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8753074615878693117854231 13129611923818039676781347)
        ·
          refine ⟨19694417885727059515172021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13129611923818039676781347 19694417885727059515172021)
          ·
            refine ⟨1846351676786911829547377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19694417885727059515172021 1846351676786911829547377)
            ·
              refine ⟨1384763757590183872160533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1846351676786911829547377 1384763757590183872160533)
              ·
                refine ⟨64910801137039869007525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1384763757590183872160533 64910801137039869007525)
                ·
                  rfl

theorem cell22_1706580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 6].length) (baseStart_1706580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706580 prefixEnd_1706580 := by exact prefixLift 1706580
  have htrace : WordTrace (prefixWord ++ tailWord_1706580) baseStart_1706580 baseEnd_1706580 := by
    simpa [prefixWord, tailWord_1706580, baseEnd_1706580] using wordTrace_append hprefix tailTrace_1706580
  have hstable : (prefixWord ++ tailWord_1706580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706580).length < 2 ^ (prefixWord ++ tailWord_1706580).sum := by decide
  have hdescent : baseEnd_1706580 < baseStart_1706580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706663 : List Nat := [1, 1, 6, 3, 1, 2, 2, 2, 1, 3]
def baseStart_1706663 : Nat := 118140960795 + 1706663 * 2 ^ 59
def prefixEnd_1706663 : Nat := 4983230072969 + 3 ^ 40 * 1706663 * 2
def baseEnd_1706663 : Nat := 584225622829574271242471

theorem tailTrace_1706663 : CollatzResearch.WordTrace tailWord_1706663 prefixEnd_1706663 584225622829574271242471 := by
  unfold tailWord_1706663
  simp only [CollatzResearch.WordTrace]
  refine ⟨62247113416058900680012643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41498075610705933786675095 62247113416058900680012643)
  ·
    refine ⟨93370670124088351020018965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62247113416058900680012643 93370670124088351020018965)
    ·
      refine ⟨4376750162066641454063389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 93370670124088351020018965 4376750162066641454063389)
      ·
        refine ⟨1641281310774990545273771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4376750162066641454063389 1641281310774990545273771)
        ·
          refine ⟨2461921966162485817910657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1641281310774990545273771 2461921966162485817910657)
          ·
            refine ⟨1846441474621864363432993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2461921966162485817910657 1846441474621864363432993)
            ·
              refine ⟨1384831105966398272574745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1846441474621864363432993 1384831105966398272574745)
              ·
                refine ⟨1038623329474798704431059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1384831105966398272574745 1038623329474798704431059)
                ·
                  refine ⟨1557934994212198056646589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1038623329474798704431059 1557934994212198056646589)
                  ·
                    refine ⟨584225622829574271242471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1557934994212198056646589 584225622829574271242471)
                    ·
                      rfl

theorem cell22_1706663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_1706663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706663 prefixEnd_1706663 := by exact prefixLift 1706663
  have htrace : WordTrace (prefixWord ++ tailWord_1706663) baseStart_1706663 baseEnd_1706663 := by
    simpa [prefixWord, tailWord_1706663, baseEnd_1706663] using wordTrace_append hprefix tailTrace_1706663
  have hstable : (prefixWord ++ tailWord_1706663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706663).length < 2 ^ (prefixWord ++ tailWord_1706663).sum := by decide
  have hdescent : baseEnd_1706663 < baseStart_1706663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706685 : List Nat := [1, 4, 1, 2, 1, 4, 2, 1, 1, 5]
def baseStart_1706685 : Nat := 118140960795 + 1706685 * 2 ^ 59
def prefixEnd_1706685 : Nat := 4983230072969 + 3 ^ 40 * 1706685 * 2
def baseEnd_1706685 : Nat := 584233153879173547192403

theorem tailTrace_1706685 : CollatzResearch.WordTrace tailWord_1706685 prefixEnd_1706685 584233153879173547192403 := by
  unfold tailWord_1706685
  simp only [CollatzResearch.WordTrace]
  refine ⟨62247915821979198437313509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41498610547986132291542339 62247915821979198437313509)
  ·
    refine ⟨11671484216621099706996283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62247915821979198437313509 11671484216621099706996283)
    ·
      refine ⟨17507226324931649560494425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11671484216621099706996283 17507226324931649560494425)
      ·
        refine ⟨13130419743698737170370819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17507226324931649560494425 13130419743698737170370819)
        ·
          refine ⟨19695629615548105755556229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13130419743698737170370819 19695629615548105755556229)
          ·
            refine ⟨3692930552915269829166793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19695629615548105755556229 3692930552915269829166793)
            ·
              refine ⟨2769697914686452371875095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3692930552915269829166793 2769697914686452371875095)
              ·
                refine ⟨4154546872029678557812643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2769697914686452371875095 4154546872029678557812643)
                ·
                  refine ⟨6231820308044517836718965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4154546872029678557812643 6231820308044517836718965)
                  ·
                    refine ⟨584233153879173547192403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6231820308044517836718965 584233153879173547192403)
                    ·
                      rfl

theorem cell22_1706685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_1706685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706685 prefixEnd_1706685 := by exact prefixLift 1706685
  have htrace : WordTrace (prefixWord ++ tailWord_1706685) baseStart_1706685 baseEnd_1706685 := by
    simpa [prefixWord, tailWord_1706685, baseEnd_1706685] using wordTrace_append hprefix tailTrace_1706685
  have hstable : (prefixWord ++ tailWord_1706685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706685).length < 2 ^ (prefixWord ++ tailWord_1706685).sum := by decide
  have hdescent : baseEnd_1706685 < baseStart_1706685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706700 : List Nat := [2, 2, 1, 5, 1, 2, 1, 1, 1, 6]
def baseStart_1706700 : Nat := 118140960795 + 1706700 * 2 ^ 59
def prefixEnd_1706700 : Nat := 4983230072969 + 3 ^ 40 * 1706700 * 2
def baseEnd_1706700 : Nat := 584238288685718508067357

theorem tailTrace_1706700 : CollatzResearch.WordTrace tailWord_1706700 prefixEnd_1706700 584238288685718508067357 := by
  unfold tailWord_1706700
  simp only [CollatzResearch.WordTrace]
  refine ⟨31124231458462427999554777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41498975277949903999406369 31124231458462427999554777)
  ·
    refine ⟨23343173593846820999666083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31124231458462427999554777 23343173593846820999666083)
    ·
      refine ⟨35014760390770231499499125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23343173593846820999666083 35014760390770231499499125)
      ·
        refine ⟨3282633786634709203078043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35014760390770231499499125 3282633786634709203078043)
        ·
          refine ⟨4923950679952063804617065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3282633786634709203078043 4923950679952063804617065)
          ·
            refine ⟨3692963009964047853462799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4923950679952063804617065 3692963009964047853462799)
            ·
              refine ⟨5539444514946071780194199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3692963009964047853462799 5539444514946071780194199)
              ·
                refine ⟨8309166772419107670291299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5539444514946071780194199 8309166772419107670291299)
                ·
                  refine ⟨12463750158628661505436949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8309166772419107670291299 12463750158628661505436949)
                  ·
                    refine ⟨584238288685718508067357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12463750158628661505436949 584238288685718508067357)
                    ·
                      rfl

theorem cell22_1706700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_1706700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706700 prefixEnd_1706700 := by exact prefixLift 1706700
  have htrace : WordTrace (prefixWord ++ tailWord_1706700) baseStart_1706700 baseEnd_1706700 := by
    simpa [prefixWord, tailWord_1706700, baseEnd_1706700] using wordTrace_append hprefix tailTrace_1706700
  have hstable : (prefixWord ++ tailWord_1706700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706700).length < 2 ^ (prefixWord ++ tailWord_1706700).sum := by decide
  have hdescent : baseEnd_1706700 < baseStart_1706700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706706 : List Nat := [3, 2, 2, 2, 4, 1, 2, 1, 1, 4]
def baseStart_1706706 : Nat := 118140960795 + 1706706 * 2 ^ 59
def prefixEnd_1706706 : Nat := 4983230072969 + 3 ^ 40 * 1706706 * 2
def baseEnd_1706706 : Nat := 584240342608336492417339

theorem tailTrace_1706706 : CollatzResearch.WordTrace tailWord_1706706 prefixEnd_1706706 584240342608336492417339 := by
  unfold tailWord_1706706
  simp only [CollatzResearch.WordTrace]
  refine ⟨15562170438725779755956993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41499121169935412682551981 15562170438725779755956993)
  ·
    refine ⟨11671627829044334816967745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15562170438725779755956993 11671627829044334816967745)
    ·
      refine ⟨8753720871783251112725809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11671627829044334816967745 8753720871783251112725809)
      ·
        refine ⟨6565290653837438334544357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8753720871783251112725809 6565290653837438334544357)
        ·
          refine ⟨1230991997594519687727067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6565290653837438334544357 1230991997594519687727067)
          ·
            refine ⟨1846487996391779531590601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1230991997594519687727067 1846487996391779531590601)
            ·
              refine ⟨1384865997293834648692951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1846487996391779531590601 1384865997293834648692951)
              ·
                refine ⟨2077298995940751973039427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1384865997293834648692951 2077298995940751973039427)
                ·
                  refine ⟨3115948493911127959559141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2077298995940751973039427 3115948493911127959559141)
                  ·
                    refine ⟨584240342608336492417339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3115948493911127959559141 584240342608336492417339)
                    ·
                      rfl

theorem cell22_1706706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_1706706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706706 prefixEnd_1706706 := by exact prefixLift 1706706
  have htrace : WordTrace (prefixWord ++ tailWord_1706706) baseStart_1706706 baseEnd_1706706 := by
    simpa [prefixWord, tailWord_1706706, baseEnd_1706706] using wordTrace_append hprefix tailTrace_1706706
  have hstable : (prefixWord ++ tailWord_1706706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706706).length < 2 ^ (prefixWord ++ tailWord_1706706).sum := by decide
  have hdescent : baseEnd_1706706 < baseStart_1706706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706781 : List Nat := [1, 4, 2, 4, 1, 2, 1, 1, 3, 3]
def baseStart_1706781 : Nat := 118140960795 + 1706781 * 2 ^ 59
def prefixEnd_1706781 : Nat := 4983230072969 + 3 ^ 40 * 1706781 * 2
def baseEnd_1706781 : Nat := 584266016641061296792109

theorem tailTrace_1706781 : CollatzResearch.WordTrace tailWord_1706781 prefixEnd_1706781 584266016641061296792109 := by
  unfold tailWord_1706781
  simp only [CollatzResearch.WordTrace]
  refine ⟨62251417229631406832808197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41500944819754271221872131 62251417229631406832808197)
  ·
    refine ⟨11672140730555888781151537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62251417229631406832808197 11672140730555888781151537)
    ·
      refine ⟨8754105547916916585863653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11672140730555888781151537 8754105547916916585863653)
      ·
        refine ⟨1641394790234421859849435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8754105547916916585863653 1641394790234421859849435)
        ·
          refine ⟨2462092185351632789774153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1641394790234421859849435 2462092185351632789774153)
          ·
            refine ⟨1846569139013724592330615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2462092185351632789774153 1846569139013724592330615)
            ·
              refine ⟨2769853708520586888495923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1846569139013724592330615 2769853708520586888495923)
              ·
                refine ⟨4154780562780880332743885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2769853708520586888495923 4154780562780880332743885)
                ·
                  refine ⟨1558042711042830124778957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4154780562780880332743885 1558042711042830124778957)
                  ·
                    refine ⟨584266016641061296792109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1558042711042830124778957 584266016641061296792109)
                    ·
                      rfl

theorem cell22_1706781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_1706781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706781 prefixEnd_1706781 := by exact prefixLift 1706781
  have htrace : WordTrace (prefixWord ++ tailWord_1706781) baseStart_1706781 baseEnd_1706781 := by
    simpa [prefixWord, tailWord_1706781, baseEnd_1706781] using wordTrace_append hprefix tailTrace_1706781
  have hstable : (prefixWord ++ tailWord_1706781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706781).length < 2 ^ (prefixWord ++ tailWord_1706781).sum := by decide
  have hdescent : baseEnd_1706781 < baseStart_1706781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706794 : List Nat := [3, 1, 4, 3, 1, 1, 1, 3, 5]
def baseStart_1706794 : Nat := 118140960795 + 1706794 * 2 ^ 59
def prefixEnd_1706794 : Nat := 4983230072969 + 3 ^ 40 * 1706794 * 2
def baseEnd_1706794 : Nat := 194756822268911198739023

theorem tailTrace_1706794 : CollatzResearch.WordTrace tailWord_1706794 prefixEnd_1706794 194756822268911198739023 := by
  unfold tailWord_1706794
  simp only [CollatzResearch.WordTrace]
  refine ⟨15562972844646077513257859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41501260919056206702020957 15562972844646077513257859)
  ·
    refine ⟨23344459266969116269886789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15562972844646077513257859 23344459266969116269886789)
    ·
      refine ⟨4377086112556709300603773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23344459266969116269886789 4377086112556709300603773)
      ·
        refine ⟨1641407292208765987726415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4377086112556709300603773 1641407292208765987726415)
        ·
          refine ⟨2462110938313148981589623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1641407292208765987726415 2462110938313148981589623)
          ·
            refine ⟨3693166407469723472384435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2462110938313148981589623 3693166407469723472384435)
            ·
              refine ⟨5539749611204585208576653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3693166407469723472384435 5539749611204585208576653)
              ·
                refine ⟨2077406104201719453216245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5539749611204585208576653 2077406104201719453216245)
                ·
                  refine ⟨194756822268911198739023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2077406104201719453216245 194756822268911198739023)
                  ·
                    rfl

theorem cell22_1706794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 5].length) (baseStart_1706794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706794 prefixEnd_1706794 := by exact prefixLift 1706794
  have htrace : WordTrace (prefixWord ++ tailWord_1706794) baseStart_1706794 baseEnd_1706794 := by
    simpa [prefixWord, tailWord_1706794, baseEnd_1706794] using wordTrace_append hprefix tailTrace_1706794
  have hstable : (prefixWord ++ tailWord_1706794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706794).length < 2 ^ (prefixWord ++ tailWord_1706794).sum := by decide
  have hdescent : baseEnd_1706794 < baseStart_1706794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706833 : List Nat := [1, 2, 2, 1, 16]
def baseStart_1706833 : Nat := 118140960795 + 1706833 * 2 ^ 59
def prefixEnd_1706833 : Nat := 4983230072969 + 3 ^ 40 * 1706833 * 2
def baseEnd_1706833 : Nat := 2404460153513376520543

theorem tailTrace_1706833 : CollatzResearch.WordTrace tailWord_1706833 prefixEnd_1706833 2404460153513376520543 := by
  unfold tailWord_1706833
  simp only [CollatzResearch.WordTrace]
  refine ⟨62253313825443019713701153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41502209216962013142467435 62253313825443019713701153)
  ·
    refine ⟨46689985369082264785275865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62253313825443019713701153 46689985369082264785275865)
    ·
      refine ⟨35017489026811698588956899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46689985369082264785275865 35017489026811698588956899)
      ·
        refine ⟨52526233540217547883435349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35017489026811698588956899 52526233540217547883435349)
        ·
          refine ⟨2404460153513376520543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 52526233540217547883435349 2404460153513376520543)
          ·
            rfl

theorem cell22_1706833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 16].length) (baseStart_1706833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706833 prefixEnd_1706833 := by exact prefixLift 1706833
  have htrace : WordTrace (prefixWord ++ tailWord_1706833) baseStart_1706833 baseEnd_1706833 := by
    simpa [prefixWord, tailWord_1706833, baseEnd_1706833] using wordTrace_append hprefix tailTrace_1706833
  have hstable : (prefixWord ++ tailWord_1706833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706833).length < 2 ^ (prefixWord ++ tailWord_1706833).sum := by decide
  have hdescent : baseEnd_1706833 < baseStart_1706833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706839 : List Nat := [1, 1, 3, 2, 4, 1, 4, 2, 4]
def baseStart_1706839 : Nat := 118140960795 + 1706839 * 2 ^ 59
def prefixEnd_1706839 : Nat := 4983230072969 + 3 ^ 40 * 1706839 * 2
def baseEnd_1706839 : Nat := 194761957075456159613977

theorem tailTrace_1706839 : CollatzResearch.WordTrace tailWord_1706839 prefixEnd_1706839 194761957075456159613977 := by
  unfold tailWord_1706839
  simp only [CollatzResearch.WordTrace]
  refine ⟨62253532663421282738419571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41502355108947521825613047 62253532663421282738419571)
  ·
    refine ⟨93380298995131924107629357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62253532663421282738419571 93380298995131924107629357)
    ·
      refine ⟨35017612123174471540361009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93380298995131924107629357 35017612123174471540361009)
      ·
        refine ⟨26263209092380853655270757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35017612123174471540361009 26263209092380853655270757)
        ·
          refine ⟨4924351704821410060363267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26263209092380853655270757 4924351704821410060363267)
          ·
            refine ⟨7386527557232115090544901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4924351704821410060363267 7386527557232115090544901)
            ·
              refine ⟨1384973916981021579477169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7386527557232115090544901 1384973916981021579477169)
              ·
                refine ⟨1038730437735766184607877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1384973916981021579477169 1038730437735766184607877)
                ·
                  refine ⟨194761957075456159613977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1038730437735766184607877 194761957075456159613977)
                  ·
                    rfl

theorem cell22_1706839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 4].length) (baseStart_1706839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706839 prefixEnd_1706839 := by exact prefixLift 1706839
  have htrace : WordTrace (prefixWord ++ tailWord_1706839) baseStart_1706839 baseEnd_1706839 := by
    simpa [prefixWord, tailWord_1706839, baseEnd_1706839] using wordTrace_append hprefix tailTrace_1706839
  have hstable : (prefixWord ++ tailWord_1706839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706839).length < 2 ^ (prefixWord ++ tailWord_1706839).sum := by decide
  have hdescent : baseEnd_1706839 < baseStart_1706839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706869 : List Nat := [1, 3, 4, 1, 1, 4, 1, 1, 2, 4]
def baseStart_1706869 : Nat := 118140960795 + 1706869 * 2 ^ 59
def prefixEnd_1706869 : Nat := 4983230072969 + 3 ^ 40 * 1706869 * 2
def baseEnd_1706869 : Nat := 584296140839458400591839

theorem tailTrace_1706869 : CollatzResearch.WordTrace tailWord_1706869 prefixEnd_1706869 584296140839458400591839 := by
  unfold tailWord_1706869
  simp only [CollatzResearch.WordTrace]
  refine ⟨62254626853312597862011661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41503084568875065241341107 62254626853312597862011661)
  ·
    refine ⟨23345485069992224198254373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62254626853312597862011661 23345485069992224198254373)
    ·
      refine ⟨4377278450623542037172695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23345485069992224198254373 4377278450623542037172695)
      ·
        refine ⟨6565917675935313055759043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4377278450623542037172695 6565917675935313055759043)
        ·
          refine ⟨9848876513902969583638565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6565917675935313055759043 9848876513902969583638565)
          ·
            refine ⟨1846664346356806796932231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9848876513902969583638565 1846664346356806796932231)
            ·
              refine ⟨2769996519535210195398347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1846664346356806796932231 2769996519535210195398347)
              ·
                refine ⟨4154994779302815293097521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2769996519535210195398347 4154994779302815293097521)
                ·
                  refine ⟨3116246084477111469823141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4154994779302815293097521 3116246084477111469823141)
                  ·
                    refine ⟨584296140839458400591839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3116246084477111469823141 584296140839458400591839)
                    ·
                      rfl

theorem cell22_1706869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_1706869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1706869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1706869 prefixEnd_1706869 := by exact prefixLift 1706869
  have htrace : WordTrace (prefixWord ++ tailWord_1706869) baseStart_1706869 baseEnd_1706869 := by
    simpa [prefixWord, tailWord_1706869, baseEnd_1706869] using wordTrace_append hprefix tailTrace_1706869
  have hstable : (prefixWord ++ tailWord_1706869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706869).length < 2 ^ (prefixWord ++ tailWord_1706869).sum := by decide
  have hdescent : baseEnd_1706869 < baseStart_1706869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707017 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 7, 3]
def baseStart_1707017 : Nat := 118140960795 + 1707017 * 2 ^ 59
def prefixEnd_1707017 : Nat := 4983230072969 + 3 ^ 40 * 1707017 * 2
def baseEnd_1707017 : Nat := 584346804264035347891385

theorem tailTrace_1707017 : CollatzResearch.WordTrace tailWord_1707017 prefixEnd_1707017 584346804264035347891385 := by
  unfold tailWord_1707017
  simp only [CollatzResearch.WordTrace]
  refine ⟨62260024856776419138399305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41506683237850946092266203 62260024856776419138399305)
  ·
    refine ⟨46695018642582314353799479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62260024856776419138399305 46695018642582314353799479)
    ·
      refine ⟨70042527963873471530699219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46695018642582314353799479 70042527963873471530699219)
      ·
        refine ⟨105063791945810207296048829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70042527963873471530699219 105063791945810207296048829)
        ·
          refine ⟨39398921979678827736018311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105063791945810207296048829 39398921979678827736018311)
          ·
            refine ⟨59098382969518241604027467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39398921979678827736018311 59098382969518241604027467)
            ·
              refine ⟨88647574454277362406041201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59098382969518241604027467 88647574454277362406041201)
              ·
                refine ⟨66485680840708021804530901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88647574454277362406041201 66485680840708021804530901)
                ·
                  refine ⟨1558258144704094261043693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 66485680840708021804530901 1558258144704094261043693)
                  ·
                    refine ⟨584346804264035347891385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1558258144704094261043693 584346804264035347891385)
                    ·
                      rfl

theorem cell22_1707017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 3].length) (baseStart_1707017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707017 prefixEnd_1707017 := by exact prefixLift 1707017
  have htrace : WordTrace (prefixWord ++ tailWord_1707017) baseStart_1707017 baseEnd_1707017 := by
    simpa [prefixWord, tailWord_1707017, baseEnd_1707017] using wordTrace_append hprefix tailTrace_1707017
  have hstable : (prefixWord ++ tailWord_1707017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707017).length < 2 ^ (prefixWord ++ tailWord_1707017).sum := by decide
  have hdescent : baseEnd_1707017 < baseStart_1707017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707034 : List Nat := [3, 1, 1, 3, 1, 2, 3, 2, 3, 3]
def baseStart_1707034 : Nat := 118140960795 + 1707034 * 2 ^ 59
def prefixEnd_1707034 : Nat := 4983230072969 + 3 ^ 40 * 1707034 * 2
def baseEnd_1707034 : Nat := 584352623711452970216333

theorem tailTrace_1707034 : CollatzResearch.WordTrace tailWord_1707034 prefixEnd_1707034 584352623711452970216333 := by
  unfold tailWord_1707034
  simp only [CollatzResearch.WordTrace]
  refine ⟨15565161224428707760442039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41507096598476554027845437 15565161224428707760442039)
  ·
    refine ⟨23347741836643061640663059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15565161224428707760442039 23347741836643061640663059)
    ·
      refine ⟨35021612754964592460994589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23347741836643061640663059 35021612754964592460994589)
      ·
        refine ⟨13133104783111722172872971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35021612754964592460994589 13133104783111722172872971)
        ·
          refine ⟨19699657174667583259309457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13133104783111722172872971 19699657174667583259309457)
          ·
            refine ⟨14774742881000687444482093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19699657174667583259309457 14774742881000687444482093)
            ·
              refine ⟨5540528580375257791680785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14774742881000687444482093 5540528580375257791680785)
              ·
                refine ⟨4155396435281443343760589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5540528580375257791680785 4155396435281443343760589)
                ·
                  refine ⟨1558273663230541253910221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4155396435281443343760589 1558273663230541253910221)
                  ·
                    refine ⟨584352623711452970216333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1558273663230541253910221 584352623711452970216333)
                    ·
                      rfl

theorem cell22_1707034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 3, 3].length) (baseStart_1707034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707034 prefixEnd_1707034 := by exact prefixLift 1707034
  have htrace : WordTrace (prefixWord ++ tailWord_1707034) baseStart_1707034 baseEnd_1707034 := by
    simpa [prefixWord, tailWord_1707034, baseEnd_1707034] using wordTrace_append hprefix tailTrace_1707034
  have hstable : (prefixWord ++ tailWord_1707034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707034).length < 2 ^ (prefixWord ++ tailWord_1707034).sum := by decide
  have hdescent : baseEnd_1707034 < baseStart_1707034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707051 : List Nat := [1, 1, 1, 1, 2, 1, 8, 3, 1, 3]
def baseStart_1707051 : Nat := 118140960795 + 1707051 * 2 ^ 59
def prefixEnd_1707051 : Nat := 4983230072969 + 3 ^ 40 * 1707051 * 2
def baseEnd_1707051 : Nat := 584358443158870592541281

theorem tailTrace_1707051 : CollatzResearch.WordTrace tailWord_1707051 prefixEnd_1707051 584358443158870592541281 := by
  unfold tailWord_1707051
  simp only [CollatzResearch.WordTrace]
  refine ⟨62261264938653242945137007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41507509959102161963424671 62261264938653242945137007)
  ·
    refine ⟨93391897407979864417705511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62261264938653242945137007 93391897407979864417705511)
    ·
      refine ⟨140087846111969796626558267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93391897407979864417705511 140087846111969796626558267)
      ·
        refine ⟨210131769167954694939837401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140087846111969796626558267 210131769167954694939837401)
        ·
          refine ⟨157598826875966021204878051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210131769167954694939837401 157598826875966021204878051)
          ·
            refine ⟨236398240313949031807317077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157598826875966021204878051 236398240313949031807317077)
            ·
              refine ⟨2770291878679090216491997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 236398240313949031807317077 2770291878679090216491997)
              ·
                refine ⟨1038859454504658831184499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2770291878679090216491997 1038859454504658831184499)
                ·
                  refine ⟨1558289181756988246776749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1038859454504658831184499 1558289181756988246776749)
                  ·
                    refine ⟨584358443158870592541281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1558289181756988246776749 584358443158870592541281)
                    ·
                      rfl

theorem cell22_1707051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 1, 3].length) (baseStart_1707051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707051 prefixEnd_1707051 := by exact prefixLift 1707051
  have htrace : WordTrace (prefixWord ++ tailWord_1707051) baseStart_1707051 baseEnd_1707051 := by
    simpa [prefixWord, tailWord_1707051, baseEnd_1707051] using wordTrace_append hprefix tailTrace_1707051
  have hstable : (prefixWord ++ tailWord_1707051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707051).length < 2 ^ (prefixWord ++ tailWord_1707051).sum := by decide
  have hdescent : baseEnd_1707051 < baseStart_1707051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707064 : List Nat := [2, 1, 2, 1, 5, 1, 3, 2, 5]
def baseStart_1707064 : Nat := 118140960795 + 1707064 * 2 ^ 59
def prefixEnd_1707064 : Nat := 4983230072969 + 3 ^ 40 * 1707064 * 2
def baseEnd_1707064 : Nat := 194787631108180963988747

theorem tailTrace_1707064 : CollatzResearch.WordTrace tailWord_1707064 prefixEnd_1707064 194787631108180963988747 := by
  unfold tailWord_1707064
  simp only [CollatzResearch.WordTrace]
  refine ⟨31130869543803073082680123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41507826058404097443573497 31130869543803073082680123)
  ·
    refine ⟨46696304315704609624020185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31130869543803073082680123 46696304315704609624020185)
    ·
      refine ⟨35022228236778457218015139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46696304315704609624020185 35022228236778457218015139)
      ·
        refine ⟨52533342355167685827022709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35022228236778457218015139 52533342355167685827022709)
        ·
          refine ⟨4925000845796970546283379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52533342355167685827022709 4925000845796970546283379)
          ·
            refine ⟨7387501268695455819425069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4925000845796970546283379 7387501268695455819425069)
            ·
              refine ⟨2770312975760795932284401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7387501268695455819425069 2770312975760795932284401)
              ·
                refine ⟨2077734731820596949213301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2770312975760795932284401 2077734731820596949213301)
                ·
                  refine ⟨194787631108180963988747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2077734731820596949213301 194787631108180963988747)
                  ·
                    rfl

theorem cell22_1707064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 5].length) (baseStart_1707064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707064 prefixEnd_1707064 := by exact prefixLift 1707064
  have htrace : WordTrace (prefixWord ++ tailWord_1707064) baseStart_1707064 baseEnd_1707064 := by
    simpa [prefixWord, tailWord_1707064, baseEnd_1707064] using wordTrace_append hprefix tailTrace_1707064
  have hstable : (prefixWord ++ tailWord_1707064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707064).length < 2 ^ (prefixWord ++ tailWord_1707064).sum := by decide
  have hdescent : baseEnd_1707064 < baseStart_1707064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707077 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 5, 4]
def baseStart_1707077 : Nat := 118140960795 + 1707077 * 2 ^ 59
def prefixEnd_1707077 : Nat := 4983230072969 + 3 ^ 40 * 1707077 * 2
def baseEnd_1707077 : Nat := 584367343490215191391201

theorem tailTrace_1707077 : CollatzResearch.WordTrace tailWord_1707077 prefixEnd_1707077 584367343490215191391201 := by
  unfold tailWord_1707077
  simp only [CollatzResearch.WordTrace]
  refine ⟨62262213236559049385583485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41508142157706032923722323 62262213236559049385583485)
  ·
    refine ⟨23348329963709643519593807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62262213236559049385583485 23348329963709643519593807)
    ·
      refine ⟨35022494945564465279390711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23348329963709643519593807 35022494945564465279390711)
      ·
        refine ⟨52533742418346697919086067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35022494945564465279390711 52533742418346697919086067)
        ·
          refine ⟨78800613627520046878629101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52533742418346697919086067 78800613627520046878629101)
          ·
            refine ⟨29550230110320017579485913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78800613627520046878629101 29550230110320017579485913)
            ·
              refine ⟨22162672582740013184614435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29550230110320017579485913 22162672582740013184614435)
              ·
                refine ⟨33244008874110019776921653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22162672582740013184614435 33244008874110019776921653)
                ·
                  refine ⟨3116625831947814354086405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33244008874110019776921653 3116625831947814354086405)
                  ·
                    refine ⟨584367343490215191391201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3116625831947814354086405 584367343490215191391201)
                    ·
                      rfl

theorem cell22_1707077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_1707077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707077 prefixEnd_1707077 := by exact prefixLift 1707077
  have htrace : WordTrace (prefixWord ++ tailWord_1707077) baseStart_1707077 baseEnd_1707077 := by
    simpa [prefixWord, tailWord_1707077, baseEnd_1707077] using wordTrace_append hprefix tailTrace_1707077
  have hstable : (prefixWord ++ tailWord_1707077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707077).length < 2 ^ (prefixWord ++ tailWord_1707077).sum := by decide
  have hdescent : baseEnd_1707077 < baseStart_1707077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707102 : List Nat := [4, 4, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_1707102 : Nat := 118140960795 + 1707102 * 2 ^ 59
def prefixEnd_1707102 : Nat := 4983230072969 + 3 ^ 40 * 1707102 * 2
def baseEnd_1707102 : Nat := 584375901501123459516125

theorem tailTrace_1707102 : CollatzResearch.WordTrace tailWord_1707102 prefixEnd_1707102 584375901501123459516125 := by
  unfold tailWord_1707102
  simp only [CollatzResearch.WordTrace]
  refine ⟨7782890632683559831905445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41508750040978985770162373 7782890632683559831905445)
  ·
    refine ⟨1459291993628167468482271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7782890632683559831905445 1459291993628167468482271)
    ·
      refine ⟨2188937990442251202723407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1459291993628167468482271 2188937990442251202723407)
      ·
        refine ⟨3283406985663376804085111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2188937990442251202723407 3283406985663376804085111)
        ·
          refine ⟨4925110478495065206127667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3283406985663376804085111 4925110478495065206127667)
          ·
            refine ⟨7387665717742597809191501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4925110478495065206127667 7387665717742597809191501)
            ·
              refine ⟨2770374644153474178446813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7387665717742597809191501 2770374644153474178446813)
              ·
                refine ⟨1038890491557552816917555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2770374644153474178446813 1038890491557552816917555)
                ·
                  refine ⟨1558335737336329225376333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1038890491557552816917555 1558335737336329225376333)
                  ·
                    refine ⟨584375901501123459516125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1558335737336329225376333 584375901501123459516125)
                    ·
                      rfl

theorem cell22_1707102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_1707102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707102 prefixEnd_1707102 := by exact prefixLift 1707102
  have htrace : WordTrace (prefixWord ++ tailWord_1707102) baseStart_1707102 baseEnd_1707102 := by
    simpa [prefixWord, tailWord_1707102, baseEnd_1707102] using wordTrace_append hprefix tailTrace_1707102
  have hstable : (prefixWord ++ tailWord_1707102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707102).length < 2 ^ (prefixWord ++ tailWord_1707102).sum := by decide
  have hdescent : baseEnd_1707102 < baseStart_1707102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707107 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 3, 5]
def baseStart_1707107 : Nat := 118140960795 + 1707107 * 2 ^ 59
def prefixEnd_1707107 : Nat := 4983230072969 + 3 ^ 40 * 1707107 * 2
def baseEnd_1707107 : Nat := 584377613103305113141109

theorem tailTrace_1707107 : CollatzResearch.WordTrace tailWord_1707107 prefixEnd_1707107 584377613103305113141109 := by
  unfold tailWord_1707107
  simp only [CollatzResearch.WordTrace]
  refine ⟨62263307426450364509175575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41508871617633576339450383 62263307426450364509175575)
  ·
    refine ⟨93394961139675546763763363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62263307426450364509175575 93394961139675546763763363)
    ·
      refine ⟨140092441709513320145645045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93394961139675546763763363 140092441709513320145645045)
      ·
        refine ⟨13133666410266873763654223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140092441709513320145645045 13133666410266873763654223)
        ·
          refine ⟨19700499615400310645481335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13133666410266873763654223 19700499615400310645481335)
          ·
            refine ⟨29550749423100465968222003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19700499615400310645481335 29550749423100465968222003)
            ·
              refine ⟨44326124134650698952333005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29550749423100465968222003 44326124134650698952333005)
              ·
                refine ⟨16622296550494012107124877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44326124134650698952333005 16622296550494012107124877)
                ·
                  refine ⟨6233361206435254540171829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16622296550494012107124877 6233361206435254540171829)
                  ·
                    refine ⟨584377613103305113141109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6233361206435254540171829 584377613103305113141109)
                    ·
                      rfl

theorem cell22_1707107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 5].length) (baseStart_1707107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707107 prefixEnd_1707107 := by exact prefixLift 1707107
  have htrace : WordTrace (prefixWord ++ tailWord_1707107) baseStart_1707107 baseEnd_1707107 := by
    simpa [prefixWord, tailWord_1707107, baseEnd_1707107] using wordTrace_append hprefix tailTrace_1707107
  have hstable : (prefixWord ++ tailWord_1707107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707107).length < 2 ^ (prefixWord ++ tailWord_1707107).sum := by decide
  have hdescent : baseEnd_1707107 < baseStart_1707107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707154 : List Nat := [3, 2, 3, 1, 1, 2, 2, 8]
def baseStart_1707154 : Nat := 118140960795 + 1707154 * 2 ^ 59
def prefixEnd_1707154 : Nat := 4983230072969 + 3 ^ 40 * 1707154 * 2
def baseEnd_1707154 : Nat := 64932633573756961912885

theorem tailTrace_1707154 : CollatzResearch.WordTrace tailWord_1707154 prefixEnd_1707154 64932633573756961912885 := by
  unfold tailWord_1707154
  simp only [CollatzResearch.WordTrace]
  refine ⟨15566255414320022884034129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41510014438186727690757677 15566255414320022884034129)
  ·
    refine ⟨11674691560740017163025597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15566255414320022884034129 11674691560740017163025597)
    ·
      refine ⟨4378009335277506436134599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11674691560740017163025597 4378009335277506436134599)
      ·
        refine ⟨6567014002916259654201899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4378009335277506436134599 6567014002916259654201899)
        ·
          refine ⟨9850521004374389481302849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6567014002916259654201899 9850521004374389481302849)
          ·
            refine ⟨7387890753280792110977137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9850521004374389481302849 7387890753280792110977137)
            ·
              refine ⟨5540918064960594083232853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7387890753280792110977137 5540918064960594083232853)
              ·
                refine ⟨64932633573756961912885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5540918064960594083232853 64932633573756961912885)
                ·
                  rfl

theorem cell22_1707154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 8].length) (baseStart_1707154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707154 prefixEnd_1707154 := by exact prefixLift 1707154
  have htrace : WordTrace (prefixWord ++ tailWord_1707154) baseStart_1707154 baseEnd_1707154 := by
    simpa [prefixWord, tailWord_1707154, baseEnd_1707154] using wordTrace_append hprefix tailTrace_1707154
  have hstable : (prefixWord ++ tailWord_1707154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707154).length < 2 ^ (prefixWord ++ tailWord_1707154).sum := by decide
  have hdescent : baseEnd_1707154 < baseStart_1707154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707199 : List Nat := [1, 1, 2, 2, 2, 2, 4, 3, 5]
def baseStart_1707199 : Nat := 118140960795 + 1707199 * 2 ^ 59
def prefixEnd_1707199 : Nat := 4983230072969 + 3 ^ 40 * 1707199 * 2
def baseEnd_1707199 : Nat := 194803035527815846613609

theorem tailTrace_1707199 : CollatzResearch.WordTrace tailWord_1707199 prefixEnd_1707199 194803035527815846613609 := by
  unfold tailWord_1707199
  simp only [CollatzResearch.WordTrace]
  refine ⟨62266662942117064221524651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41511108628078042814349767 62266662942117064221524651)
  ·
    refine ⟨93399994413175596332286977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62266662942117064221524651 93399994413175596332286977)
    ·
      refine ⟨70049995809881697249215233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93399994413175596332286977 70049995809881697249215233)
      ·
        refine ⟨52537496857411272936911425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70049995809881697249215233 52537496857411272936911425)
        ·
          refine ⟨39403122643058454702683569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52537496857411272936911425 39403122643058454702683569)
          ·
            refine ⟨29552341982293841027012677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39403122643058454702683569 29552341982293841027012677)
            ·
              refine ⟨5541064121680095192564877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29552341982293841027012677 5541064121680095192564877)
              ·
                refine ⟨2077899045630035697211829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5541064121680095192564877 2077899045630035697211829)
                ·
                  refine ⟨194803035527815846613609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2077899045630035697211829 194803035527815846613609)
                  ·
                    rfl

theorem cell22_1707199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 5].length) (baseStart_1707199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707199 prefixEnd_1707199 := by exact prefixLift 1707199
  have htrace : WordTrace (prefixWord ++ tailWord_1707199) baseStart_1707199 baseEnd_1707199 := by
    simpa [prefixWord, tailWord_1707199, baseEnd_1707199] using wordTrace_append hprefix tailTrace_1707199
  have hstable : (prefixWord ++ tailWord_1707199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707199).length < 2 ^ (prefixWord ++ tailWord_1707199).sum := by decide
  have hdescent : baseEnd_1707199 < baseStart_1707199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707244 : List Nat := [2, 2, 1, 1, 2, 4, 1, 3, 6]
def baseStart_1707244 : Nat := 118140960795 + 1707244 * 2 ^ 59
def prefixEnd_1707244 : Nat := 4983230072969 + 3 ^ 40 * 1707244 * 2
def baseEnd_1707244 : Nat := 194808170334360807488563

theorem tailTrace_1707244 : CollatzResearch.WordTrace tailWord_1707244 prefixEnd_1707244 194808170334360807488563 := by
  unfold tailWord_1707244
  simp only [CollatzResearch.WordTrace]
  refine ⟨31134152113477018453456393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41512202817969357937941857 31134152113477018453456393)
  ·
    refine ⟨23350614085107763840092295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31134152113477018453456393 23350614085107763840092295)
    ·
      refine ⟨35025921127661645760138443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23350614085107763840092295 35025921127661645760138443)
      ·
        refine ⟨52538881691492468640207665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35025921127661645760138443 52538881691492468640207665)
        ·
          refine ⟨39404161268619351480155749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52538881691492468640207665 39404161268619351480155749)
          ·
            refine ⟨7388280237866128402529203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39404161268619351480155749 7388280237866128402529203)
            ·
              refine ⟨11082420356799192603793805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7388280237866128402529203 11082420356799192603793805)
              ·
                refine ⟨4155907633799697226422677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11082420356799192603793805 4155907633799697226422677)
                ·
                  refine ⟨194808170334360807488563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4155907633799697226422677 194808170334360807488563)
                  ·
                    rfl

theorem cell22_1707244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_1707244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707244 prefixEnd_1707244 := by exact prefixLift 1707244
  have htrace : WordTrace (prefixWord ++ tailWord_1707244) baseStart_1707244 baseEnd_1707244 := by
    simpa [prefixWord, tailWord_1707244, baseEnd_1707244] using wordTrace_append hprefix tailTrace_1707244
  have hstable : (prefixWord ++ tailWord_1707244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707244).length < 2 ^ (prefixWord ++ tailWord_1707244).sum := by decide
  have hdescent : baseEnd_1707244 < baseStart_1707244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707276 : List Nat := [2, 2, 1, 2, 2, 3, 1, 2, 4, 3]
def baseStart_1707276 : Nat := 118140960795 + 1707276 * 2 ^ 59
def prefixEnd_1707276 : Nat := 4983230072969 + 3 ^ 40 * 1707276 * 2
def baseEnd_1707276 : Nat := 584435465257045005665591

theorem tailTrace_1707276 : CollatzResearch.WordTrace tailWord_1707276 prefixEnd_1707276 584435465257045005665591 := by
  unfold tailWord_1707276
  simp only [CollatzResearch.WordTrace]
  refine ⟨31134735681419053186038841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41512980908558737581385121 31134735681419053186038841)
  ·
    refine ⟨23351051761064289889529131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31134735681419053186038841 23351051761064289889529131)
    ·
      refine ⟨35026577641596434834293697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23351051761064289889529131 35026577641596434834293697)
      ·
        refine ⟨26269933231197326125720273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35026577641596434834293697 26269933231197326125720273)
        ·
          refine ⟨19702449923397994594290205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26269933231197326125720273 19702449923397994594290205)
          ·
            refine ⟨7388418721274247972858827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19702449923397994594290205 7388418721274247972858827)
            ·
              refine ⟨11082628081911371959288241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7388418721274247972858827 11082628081911371959288241)
              ·
                refine ⟨8311971061433528969466181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11082628081911371959288241 8311971061433528969466181)
                ·
                  refine ⟨1558494574018786681774909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8311971061433528969466181 1558494574018786681774909)
                  ·
                    refine ⟨584435465257045005665591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1558494574018786681774909 584435465257045005665591)
                    ·
                      rfl

theorem cell22_1707276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 4, 3].length) (baseStart_1707276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707276 prefixEnd_1707276 := by exact prefixLift 1707276
  have htrace : WordTrace (prefixWord ++ tailWord_1707276) baseStart_1707276 baseEnd_1707276 := by
    simpa [prefixWord, tailWord_1707276, baseEnd_1707276] using wordTrace_append hprefix tailTrace_1707276
  have hstable : (prefixWord ++ tailWord_1707276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707276).length < 2 ^ (prefixWord ++ tailWord_1707276).sum := by decide
  have hdescent : baseEnd_1707276 < baseStart_1707276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707278 : List Nat := [4, 1, 1, 2, 1, 3, 3, 3, 4]
def baseStart_1707278 : Nat := 118140960795 + 1707278 * 2 ^ 59
def prefixEnd_1707278 : Nat := 4983230072969 + 3 ^ 40 * 1707278 * 2
def baseEnd_1707278 : Nat := 194812049965972555705195

theorem tailTrace_1707278 : CollatzResearch.WordTrace tailWord_1707278 prefixEnd_1707278 194812049965972555705195 := by
  unfold tailWord_1707278
  simp only [CollatzResearch.WordTrace]
  refine ⟨7783693038603857589206311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41513029539220573809100325 7783693038603857589206311)
  ·
    refine ⟨11675539557905786383809467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7783693038603857589206311 11675539557905786383809467)
    ·
      refine ⟨17513309336858679575714201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11675539557905786383809467 17513309336858679575714201)
      ·
        refine ⟨13134982002644009681785651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17513309336858679575714201 13134982002644009681785651)
        ·
          refine ⟨19702473003966014522678477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13134982002644009681785651 19702473003966014522678477)
          ·
            refine ⟨7388427376487255446004429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19702473003966014522678477 7388427376487255446004429)
            ·
              refine ⟨2770660266182720792251661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7388427376487255446004429 2770660266182720792251661)
              ·
                refine ⟨1038997599818520297094373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2770660266182720792251661 1038997599818520297094373)
                ·
                  refine ⟨194812049965972555705195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1038997599818520297094373 194812049965972555705195)
                  ·
                    rfl

theorem cell22_1707278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_1707278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707278 prefixEnd_1707278 := by exact prefixLift 1707278
  have htrace : WordTrace (prefixWord ++ tailWord_1707278) baseStart_1707278 baseEnd_1707278 := by
    simpa [prefixWord, tailWord_1707278, baseEnd_1707278] using wordTrace_append hprefix tailTrace_1707278
  have hstable : (prefixWord ++ tailWord_1707278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707278).length < 2 ^ (prefixWord ++ tailWord_1707278).sum := by decide
  have hdescent : baseEnd_1707278 < baseStart_1707278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707293 : List Nat := [1, 4, 2, 3, 1, 1, 2, 1, 4, 3]
def baseStart_1707293 : Nat := 118140960795 + 1707293 * 2 ^ 59
def prefixEnd_1707293 : Nat := 4983230072969 + 3 ^ 40 * 1707293 * 2
def baseEnd_1707293 : Nat := 584441284704462627990539

theorem tailTrace_1707293 : CollatzResearch.WordTrace tailWord_1707293 prefixEnd_1707293 584441284704462627990539 := by
  unfold tailWord_1707293
  simp only [CollatzResearch.WordTrace]
  refine ⟨62270091403776518275446533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41513394269184345516964355 62270091403776518275446533)
  ·
    refine ⟨11675642138208097176646225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62270091403776518275446533 11675642138208097176646225)
    ·
      refine ⟨8756731603656072882484669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11675642138208097176646225 8756731603656072882484669)
      ·
        refine ⟨3283774351371027330931751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8756731603656072882484669 3283774351371027330931751)
        ·
          refine ⟨4925661527056540996397627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3283774351371027330931751 4925661527056540996397627)
          ·
            refine ⟨7388492290584811494596441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4925661527056540996397627 7388492290584811494596441)
            ·
              refine ⟨5541369217938608620947331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7388492290584811494596441 5541369217938608620947331)
              ·
                refine ⟨8312053826907912931420997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5541369217938608620947331 8312053826907912931420997)
                ·
                  refine ⟨1558510092545233674641437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8312053826907912931420997 1558510092545233674641437)
                  ·
                    refine ⟨584441284704462627990539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1558510092545233674641437 584441284704462627990539)
                    ·
                      rfl

theorem cell22_1707293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_1707293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707293 prefixEnd_1707293 := by exact prefixLift 1707293
  have htrace : WordTrace (prefixWord ++ tailWord_1707293) baseStart_1707293 baseEnd_1707293 := by
    simpa [prefixWord, tailWord_1707293, baseEnd_1707293] using wordTrace_append hprefix tailTrace_1707293
  have hstable : (prefixWord ++ tailWord_1707293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707293).length < 2 ^ (prefixWord ++ tailWord_1707293).sum := by decide
  have hdescent : baseEnd_1707293 < baseStart_1707293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707295 : List Nat := [1, 1, 2, 4, 4, 1, 3, 2, 4]
def baseStart_1707295 : Nat := 118140960795 + 1707295 * 2 ^ 59
def prefixEnd_1707295 : Nat := 4983230072969 + 3 ^ 40 * 1707295 * 2
def baseEnd_1707295 : Nat := 194813989781778429813511

theorem tailTrace_1707295 : CollatzResearch.WordTrace tailWord_1707295 prefixEnd_1707295 194813989781778429813511 := by
  unfold tailWord_1707295
  simp only [CollatzResearch.WordTrace]
  refine ⟨62270164349769272617019339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41513442899846181744679559 62270164349769272617019339)
  ·
    refine ⟨93405246524653908925529009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62270164349769272617019339 93405246524653908925529009)
    ·
      refine ⟨70053934893490431694146757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93405246524653908925529009 70053934893490431694146757)
      ·
        refine ⟨13135112792529455942652517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70053934893490431694146757 13135112792529455942652517)
        ·
          refine ⟨2462833648599272989247347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13135112792529455942652517 2462833648599272989247347)
          ·
            refine ⟨3694250472898909483871021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2462833648599272989247347 3694250472898909483871021)
            ·
              refine ⟨1385343927337091056451633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3694250472898909483871021 1385343927337091056451633)
              ·
                refine ⟨1039007945502818292338725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1385343927337091056451633 1039007945502818292338725)
                ·
                  refine ⟨194813989781778429813511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1039007945502818292338725 194813989781778429813511)
                  ·
                    rfl

theorem cell22_1707295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 4].length) (baseStart_1707295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707295 prefixEnd_1707295 := by exact prefixLift 1707295
  have htrace : WordTrace (prefixWord ++ tailWord_1707295) baseStart_1707295 baseEnd_1707295 := by
    simpa [prefixWord, tailWord_1707295, baseEnd_1707295] using wordTrace_append hprefix tailTrace_1707295
  have hstable : (prefixWord ++ tailWord_1707295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707295).length < 2 ^ (prefixWord ++ tailWord_1707295).sum := by decide
  have hdescent : baseEnd_1707295 < baseStart_1707295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707306 : List Nat := [3, 1, 4, 2, 1, 1, 1, 9]
def baseStart_1707306 : Nat := 118140960795 + 1707306 * 2 ^ 59
def prefixEnd_1707306 : Nat := 4983230072969 + 3 ^ 40 * 1707306 * 2
def baseEnd_1707306 : Nat := 64938414985570547490611

theorem tailTrace_1707306 : CollatzResearch.WordTrace tailWord_1707306 prefixEnd_1707306 64938414985570547490611 := by
  unfold tailWord_1707306
  simp only [CollatzResearch.WordTrace]
  refine ⟨15567641388182355373917443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41513710368486280997113181 15567641388182355373917443)
  ·
    refine ⟨23351462082273533060876165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15567641388182355373917443 23351462082273533060876165)
    ·
      refine ⟨4378399140426287448914281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23351462082273533060876165 4378399140426287448914281)
      ·
        refine ⟨3283799355319715586685711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4378399140426287448914281 3283799355319715586685711)
        ·
          refine ⟨4925699032979573380028567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3283799355319715586685711 4925699032979573380028567)
          ·
            refine ⟨7388548549469360070042851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4925699032979573380028567 7388548549469360070042851)
            ·
              refine ⟨11082822824204040105064277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7388548549469360070042851 11082822824204040105064277)
              ·
                refine ⟨64938414985570547490611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11082822824204040105064277 64938414985570547490611)
                ·
                  rfl

theorem cell22_1707306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 9].length) (baseStart_1707306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707306 prefixEnd_1707306 := by exact prefixLift 1707306
  have htrace : WordTrace (prefixWord ++ tailWord_1707306) baseStart_1707306 baseEnd_1707306 := by
    simpa [prefixWord, tailWord_1707306, baseEnd_1707306] using wordTrace_append hprefix tailTrace_1707306
  have hstable : (prefixWord ++ tailWord_1707306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707306).length < 2 ^ (prefixWord ++ tailWord_1707306).sum := by decide
  have hdescent : baseEnd_1707306 < baseStart_1707306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707325 : List Nat := [1, 4, 1, 5, 1, 1, 2, 1, 2, 4]
def baseStart_1707325 : Nat := 118140960795 + 1707325 * 2 ^ 59
def prefixEnd_1707325 : Nat := 4983230072969 + 3 ^ 40 * 1707325 * 2
def baseEnd_1707325 : Nat := 584452238958425211190441

theorem tailTrace_1707325 : CollatzResearch.WordTrace tailWord_1707325 prefixEnd_1707325 584452238958425211190441 := by
  unfold tailWord_1707325
  simp only [CollatzResearch.WordTrace]
  refine ⟨62271258539660587740611429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41514172359773725160407619 62271258539660587740611429)
  ·
    refine ⟨11675860976186360201364643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62271258539660587740611429 11675860976186360201364643)
    ·
      refine ⟨17513791464279540302046965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11675860976186360201364643 17513791464279540302046965)
      ·
        refine ⟨1641917949776206903316903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17513791464279540302046965 1641917949776206903316903)
        ·
          refine ⟨2462876924664310354975355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1641917949776206903316903 2462876924664310354975355)
          ·
            refine ⟨3694315386996465532463033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2462876924664310354975355 3694315386996465532463033)
            ·
              refine ⟨2770736540247349149347275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3694315386996465532463033 2770736540247349149347275)
              ·
                refine ⟨4156104810371023724020913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2770736540247349149347275 4156104810371023724020913)
                ·
                  refine ⟨3117078607778267793015685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4156104810371023724020913 3117078607778267793015685)
                  ·
                    refine ⟨584452238958425211190441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3117078607778267793015685 584452238958425211190441)
                    ·
                      rfl

theorem cell22_1707325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_1707325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707325 prefixEnd_1707325 := by exact prefixLift 1707325
  have htrace : WordTrace (prefixWord ++ tailWord_1707325) baseStart_1707325 baseEnd_1707325 := by
    simpa [prefixWord, tailWord_1707325, baseEnd_1707325] using wordTrace_append hprefix tailTrace_1707325
  have hstable : (prefixWord ++ tailWord_1707325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707325).length < 2 ^ (prefixWord ++ tailWord_1707325).sum := by decide
  have hdescent : baseEnd_1707325 < baseStart_1707325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707351 : List Nat := [1, 1, 3, 2, 3, 2, 1, 4, 5]
def baseStart_1707351 : Nat := 118140960795 + 1707351 * 2 ^ 59
def prefixEnd_1707351 : Nat := 4983230072969 + 3 ^ 40 * 1707351 * 2
def baseEnd_1707351 : Nat := 194820379763256603346787

theorem tailTrace_1707351 : CollatzResearch.WordTrace tailWord_1707351 prefixEnd_1707351 194820379763256603346787 := by
  unfold tailWord_1707351
  simp only [CollatzResearch.WordTrace]
  refine ⟨62272206837566394181057907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41514804558377596120705271 62272206837566394181057907)
  ·
    refine ⟨93408310256349591271586861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62272206837566394181057907 93408310256349591271586861)
    ·
      refine ⟨35028116346131096726845073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93408310256349591271586861 35028116346131096726845073)
      ·
        refine ⟨26271087259598322545133805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35028116346131096726845073 26271087259598322545133805)
        ·
          refine ⟨9851657722349370954425177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26271087259598322545133805 9851657722349370954425177)
          ·
            refine ⟨7388743291762028215818883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9851657722349370954425177 7388743291762028215818883)
            ·
              refine ⟨11083114937643042323728325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7388743291762028215818883 11083114937643042323728325)
              ·
                refine ⟨2078084050808070435699061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11083114937643042323728325 2078084050808070435699061)
                ·
                  refine ⟨194820379763256603346787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2078084050808070435699061 194820379763256603346787)
                  ·
                    rfl

theorem cell22_1707351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 5].length) (baseStart_1707351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707351 prefixEnd_1707351 := by exact prefixLift 1707351
  have htrace : WordTrace (prefixWord ++ tailWord_1707351) baseStart_1707351 baseEnd_1707351 := by
    simpa [prefixWord, tailWord_1707351, baseEnd_1707351] using wordTrace_append hprefix tailTrace_1707351
  have hstable : (prefixWord ++ tailWord_1707351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707351).length < 2 ^ (prefixWord ++ tailWord_1707351).sum := by decide
  have hdescent : baseEnd_1707351 < baseStart_1707351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707357 : List Nat := [1, 4, 5, 1, 1, 2, 1, 7]
def baseStart_1707357 : Nat := 118140960795 + 1707357 * 2 ^ 59
def prefixEnd_1707357 : Nat := 4983230072969 + 3 ^ 40 * 1707357 * 2
def baseEnd_1707357 : Nat := 64940354801376421598927

theorem tailTrace_1707357 : CollatzResearch.WordTrace tailWord_1707357 prefixEnd_1707357 64940354801376421598927 := by
  unfold tailWord_1707357
  simp only [CollatzResearch.WordTrace]
  refine ⟨62272425675544657205776325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41514950450363104803850883 62272425675544657205776325)
  ·
    refine ⟨11676079814164623226083061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62272425675544657205776325 11676079814164623226083061)
    ·
      refine ⟨1094632482577933427445287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11676079814164623226083061 1094632482577933427445287)
      ·
        refine ⟨1641948723866900141167931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1094632482577933427445287 1641948723866900141167931)
        ·
          refine ⟨2462923085800350211751897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1641948723866900141167931 2462923085800350211751897)
          ·
            refine ⟨1847192314350262658813923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2462923085800350211751897 1847192314350262658813923)
            ·
              refine ⟨2770788471525393988220885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1847192314350262658813923 2770788471525393988220885)
              ·
                refine ⟨64940354801376421598927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2770788471525393988220885 64940354801376421598927)
                ·
                  rfl

theorem cell22_1707357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 7].length) (baseStart_1707357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707357 prefixEnd_1707357 := by exact prefixLift 1707357
  have htrace : WordTrace (prefixWord ++ tailWord_1707357) baseStart_1707357 baseEnd_1707357 := by
    simpa [prefixWord, tailWord_1707357, baseEnd_1707357] using wordTrace_append hprefix tailTrace_1707357
  have hstable : (prefixWord ++ tailWord_1707357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707357).length < 2 ^ (prefixWord ++ tailWord_1707357).sum := by decide
  have hdescent : baseEnd_1707357 < baseStart_1707357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707413 : List Nat := [1, 3, 2, 1, 1, 2, 4, 4, 4]
def baseStart_1707413 : Nat := 118140960795 + 1707413 * 2 ^ 59
def prefixEnd_1707413 : Nat := 4983230072969 + 3 ^ 40 * 1707413 * 2
def baseEnd_1707413 : Nat := 194827454385607438330057

theorem tailTrace_1707413 : CollatzResearch.WordTrace tailWord_1707413 prefixEnd_1707413 194827454385607438330057 := by
  unfold tailWord_1707413
  simp only [CollatzResearch.WordTrace]
  refine ⟨62274468163341778769814893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41516312108894519179876595 62274468163341778769814893)
  ·
    refine ⟨23352925561253167038680585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62274468163341778769814893 23352925561253167038680585)
    ·
      refine ⟨17514694170939875279010439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23352925561253167038680585 17514694170939875279010439)
      ·
        refine ⟨26272041256409812918515659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17514694170939875279010439 26272041256409812918515659)
        ·
          refine ⟨39408061884614719377773489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26272041256409812918515659 39408061884614719377773489)
          ·
            refine ⟨29556046413461039533330117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39408061884614719377773489 29556046413461039533330117)
            ·
              refine ⟨5541758702523944912499397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29556046413461039533330117 5541758702523944912499397)
              ·
                refine ⟨1039079756723239671093637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5541758702523944912499397 1039079756723239671093637)
                ·
                  refine ⟨194827454385607438330057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1039079756723239671093637 194827454385607438330057)
                  ·
                    rfl

theorem cell22_1707413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 4].length) (baseStart_1707413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707413 prefixEnd_1707413 := by exact prefixLift 1707413
  have htrace : WordTrace (prefixWord ++ tailWord_1707413) baseStart_1707413 baseEnd_1707413 := by
    simpa [prefixWord, tailWord_1707413, baseEnd_1707413] using wordTrace_append hprefix tailTrace_1707413
  have hstable : (prefixWord ++ tailWord_1707413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707413).length < 2 ^ (prefixWord ++ tailWord_1707413).sum := by decide
  have hdescent : baseEnd_1707413 < baseStart_1707413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707432 : List Nat := [2, 1, 6, 1, 2, 1, 2, 2, 1, 4]
def baseStart_1707432 : Nat := 118140960795 + 1707432 * 2 ^ 59
def prefixEnd_1707432 : Nat := 4983230072969 + 3 ^ 40 * 1707432 * 2
def baseEnd_1707432 : Nat := 584488867245112598765113

theorem tailTrace_1707432 : CollatzResearch.WordTrace tailWord_1707432 prefixEnd_1707432 584488867245112598765113 := by
  unfold tailWord_1707432
  simp only [CollatzResearch.WordTrace]
  refine ⟨31137580575136472507378275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41516774100181963343171033 31137580575136472507378275)
  ·
    refine ⟨46706370862704708761067413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31137580575136472507378275 46706370862704708761067413)
    ·
      refine ⟨2189361134189283223175035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46706370862704708761067413 2189361134189283223175035)
      ·
        refine ⟨3284041701283924834762553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2189361134189283223175035 3284041701283924834762553)
        ·
          refine ⟨2463031275962943626071915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3284041701283924834762553 2463031275962943626071915)
          ·
            refine ⟨3694546913944415439107873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2463031275962943626071915 3694546913944415439107873)
            ·
              refine ⟨2770910185458311579330905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3694546913944415439107873 2770910185458311579330905)
              ·
                refine ⟨2078182639093733684498179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2770910185458311579330905 2078182639093733684498179)
                ·
                  refine ⟨3117273958640600526747269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2078182639093733684498179 3117273958640600526747269)
                  ·
                    refine ⟨584488867245112598765113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3117273958640600526747269 584488867245112598765113)
                    ·
                      rfl

theorem cell22_1707432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_1707432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707432 prefixEnd_1707432 := by exact prefixLift 1707432
  have htrace : WordTrace (prefixWord ++ tailWord_1707432) baseStart_1707432 baseEnd_1707432 := by
    simpa [prefixWord, tailWord_1707432, baseEnd_1707432] using wordTrace_append hprefix tailTrace_1707432
  have hstable : (prefixWord ++ tailWord_1707432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707432).length < 2 ^ (prefixWord ++ tailWord_1707432).sum := by decide
  have hdescent : baseEnd_1707432 < baseStart_1707432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707441 : List Nat := [1, 2, 2, 4, 1, 1, 3, 8]
def baseStart_1707441 : Nat := 118140960795 + 1707441 * 2 ^ 59
def prefixEnd_1707441 : Nat := 4983230072969 + 3 ^ 40 * 1707441 * 2
def baseEnd_1707441 : Nat := 64943549792115508365565

theorem tailTrace_1707441 : CollatzResearch.WordTrace tailWord_1707441 prefixEnd_1707441 64943549792115508365565 := by
  unfold tailWord_1707441
  simp only [CollatzResearch.WordTrace]
  refine ⟨62275489407240339551834177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41516992938160226367889451 62275489407240339551834177)
  ·
    refine ⟨46706617055430254663875633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62275489407240339551834177 46706617055430254663875633)
    ·
      refine ⟨35029962791572690997906725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46706617055430254663875633 35029962791572690997906725)
      ·
        refine ⟨6568118023419879562107511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35029962791572690997906725 6568118023419879562107511)
        ·
          refine ⟨9852177035129819343161267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6568118023419879562107511 9852177035129819343161267)
          ·
            refine ⟨14778265552694729014741901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9852177035129819343161267 14778265552694729014741901)
            ·
              refine ⟨5541849582260523380528213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14778265552694729014741901 5541849582260523380528213)
              ·
                refine ⟨64943549792115508365565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5541849582260523380528213 64943549792115508365565)
                ·
                  rfl

theorem cell22_1707441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 8].length) (baseStart_1707441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707441 prefixEnd_1707441 := by exact prefixLift 1707441
  have htrace : WordTrace (prefixWord ++ tailWord_1707441) baseStart_1707441 baseEnd_1707441 := by
    simpa [prefixWord, tailWord_1707441, baseEnd_1707441] using wordTrace_append hprefix tailTrace_1707441
  have hstable : (prefixWord ++ tailWord_1707441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707441).length < 2 ^ (prefixWord ++ tailWord_1707441).sum := by decide
  have hdescent : baseEnd_1707441 < baseStart_1707441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707460 : List Nat := [2, 3, 3, 2, 1, 2, 1, 2, 2, 4]
def baseStart_1707460 : Nat := 118140960795 + 1707460 * 2 ^ 59
def prefixEnd_1707460 : Nat := 4983230072969 + 3 ^ 40 * 1707460 * 2
def baseEnd_1707460 : Nat := 584498452217329859065027

theorem tailTrace_1707460 : CollatzResearch.WordTrace tailWord_1707460 prefixEnd_1707460 584498452217329859065027 := by
  unfold tailWord_1707460
  simp only [CollatzResearch.WordTrace]
  refine ⟨31138091197085752898387917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41517454929447670531183889 31138091197085752898387917)
  ·
    refine ⟨11676784198907157336895469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31138091197085752898387917 11676784198907157336895469)
    ·
      refine ⟨4378794074590184001335801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11676784198907157336895469 4378794074590184001335801)
      ·
        refine ⟨3284095555942638001001851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4378794074590184001335801 3284095555942638001001851)
        ·
          refine ⟨4926143333913957001502777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3284095555942638001001851 4926143333913957001502777)
          ·
            refine ⟨3694607500435467751127083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4926143333913957001502777 3694607500435467751127083)
            ·
              refine ⟨5541911250653201626690625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3694607500435467751127083 5541911250653201626690625)
              ·
                refine ⟨4156433437989901220017969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5541911250653201626690625 4156433437989901220017969)
                ·
                  refine ⟨3117325078492425915013477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4156433437989901220017969 3117325078492425915013477)
                  ·
                    refine ⟨584498452217329859065027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3117325078492425915013477 584498452217329859065027)
                    ·
                      rfl

theorem cell22_1707460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_1707460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707460 prefixEnd_1707460 := by exact prefixLift 1707460
  have htrace : WordTrace (prefixWord ++ tailWord_1707460) baseStart_1707460 baseEnd_1707460 := by
    simpa [prefixWord, tailWord_1707460, baseEnd_1707460] using wordTrace_append hprefix tailTrace_1707460
  have hstable : (prefixWord ++ tailWord_1707460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707460).length < 2 ^ (prefixWord ++ tailWord_1707460).sum := by decide
  have hdescent : baseEnd_1707460 < baseStart_1707460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707524 : List Nat := [2, 3, 2, 3, 2, 1, 1, 4, 1, 3]
def baseStart_1707524 : Nat := 118140960795 + 1707524 * 2 ^ 59
def prefixEnd_1707524 : Nat := 4983230072969 + 3 ^ 40 * 1707524 * 2
def baseEnd_1707524 : Nat := 584520360725255025464831

theorem tailTrace_1707524 : CollatzResearch.WordTrace tailWord_1707524 prefixEnd_1707524 584520360725255025464831 := by
  unfold tailWord_1707524
  simp only [CollatzResearch.WordTrace]
  refine ⟨31139258332969822363552813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41519011110626429818070417 31139258332969822363552813)
  ·
    refine ⟨11677221874863683386332305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31139258332969822363552813 11677221874863683386332305)
    ·
      refine ⟨8757916406147762539749229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11677221874863683386332305 8757916406147762539749229)
      ·
        refine ⟨3284218652305410952405961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8757916406147762539749229 3284218652305410952405961)
        ·
          refine ⟨2463163989229058214304471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3284218652305410952405961 2463163989229058214304471)
          ·
            refine ⟨3694745983843587321456707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2463163989229058214304471 3694745983843587321456707)
            ·
              refine ⟨5542118975765380982185061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3694745983843587321456707 5542118975765380982185061)
              ·
                refine ⟨1039147307956008934159699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5542118975765380982185061 1039147307956008934159699)
                ·
                  refine ⟨1558720961934013401239549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1039147307956008934159699 1558720961934013401239549)
                  ·
                    refine ⟨584520360725255025464831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1558720961934013401239549 584520360725255025464831)
                    ·
                      rfl

theorem cell22_1707524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_1707524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707524 prefixEnd_1707524 := by exact prefixLift 1707524
  have htrace : WordTrace (prefixWord ++ tailWord_1707524) baseStart_1707524 baseEnd_1707524 := by
    simpa [prefixWord, tailWord_1707524, baseEnd_1707524] using wordTrace_append hprefix tailTrace_1707524
  have hstable : (prefixWord ++ tailWord_1707524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707524).length < 2 ^ (prefixWord ++ tailWord_1707524).sum := by decide
  have hdescent : baseEnd_1707524 < baseStart_1707524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707526 : List Nat := [6, 2, 1, 1, 3, 1, 1, 7]
def baseStart_1707526 : Nat := 118140960795 + 1707526 * 2 ^ 59
def prefixEnd_1707526 : Nat := 4983230072969 + 3 ^ 40 * 1707526 * 2
def baseEnd_1707526 : Nat := 64946782818458631879425

theorem tailTrace_1707526 : CollatzResearch.WordTrace tailWord_1707526 prefixEnd_1707526 64946782818458631879425 := by
  unfold tailWord_1707526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1946205925372887470896201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41519059741288266045785621 1946205925372887470896201)
  ·
    refine ⟨1459654444029665603172151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1946205925372887470896201 1459654444029665603172151)
    ·
      refine ⟨2189481666044498404758227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1459654444029665603172151 2189481666044498404758227)
      ·
        refine ⟨3284222499066747607137341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2189481666044498404758227 3284222499066747607137341)
        ·
          refine ⟨1231583437150030352676503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3284222499066747607137341 1231583437150030352676503)
          ·
            refine ⟨1847375155725045529014755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1231583437150030352676503 1847375155725045529014755)
            ·
              refine ⟨2771062733587568293522133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1847375155725045529014755 2771062733587568293522133)
              ·
                refine ⟨64946782818458631879425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2771062733587568293522133 64946782818458631879425)
                ·
                  rfl

theorem cell22_1707526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_1707526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707526 prefixEnd_1707526 := by exact prefixLift 1707526
  have htrace : WordTrace (prefixWord ++ tailWord_1707526) baseStart_1707526 baseEnd_1707526 := by
    simpa [prefixWord, tailWord_1707526, baseEnd_1707526] using wordTrace_append hprefix tailTrace_1707526
  have hstable : (prefixWord ++ tailWord_1707526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707526).length < 2 ^ (prefixWord ++ tailWord_1707526).sum := by decide
  have hdescent : baseEnd_1707526 < baseStart_1707526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707548 : List Nat := [2, 2, 3, 1, 2, 1, 3, 2, 6]
def baseStart_1707548 : Nat := 118140960795 + 1707548 * 2 ^ 59
def prefixEnd_1707548 : Nat := 4983230072969 + 3 ^ 40 * 1707548 * 2
def baseEnd_1707548 : Nat := 194842858805242320954919

theorem tailTrace_1707548 : CollatzResearch.WordTrace tailWord_1707548 prefixEnd_1707548 194842858805242320954919 := by
  unfold tailWord_1707548
  simp only [CollatzResearch.WordTrace]
  refine ⟨31139696008926348412989649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41519594678568464550652865 31139696008926348412989649)
  ·
    refine ⟨23354772006694761309742237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31139696008926348412989649 23354772006694761309742237)
    ·
      refine ⟨8758039502510535491153339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23354772006694761309742237 8758039502510535491153339)
      ·
        refine ⟨13137059253765803236730009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8758039502510535491153339 13137059253765803236730009)
        ·
          refine ⟨9852794440324352427547507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13137059253765803236730009 9852794440324352427547507)
          ·
            refine ⟨14779191660486528641321261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9852794440324352427547507 14779191660486528641321261)
            ·
              refine ⟨5542196872682448240495473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14779191660486528641321261 5542196872682448240495473)
              ·
                refine ⟨4156647654511836180371605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5542196872682448240495473 4156647654511836180371605)
                ·
                  refine ⟨194842858805242320954919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4156647654511836180371605 194842858805242320954919)
                  ·
                    rfl

theorem cell22_1707548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_1707548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707548 prefixEnd_1707548 := by exact prefixLift 1707548
  have htrace : WordTrace (prefixWord ++ tailWord_1707548) baseStart_1707548 baseEnd_1707548 := by
    simpa [prefixWord, tailWord_1707548, baseEnd_1707548] using wordTrace_append hprefix tailTrace_1707548
  have hstable : (prefixWord ++ tailWord_1707548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707548).length < 2 ^ (prefixWord ++ tailWord_1707548).sum := by decide
  have hdescent : baseEnd_1707548 < baseStart_1707548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707578 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 4, 4]
def baseStart_1707578 : Nat := 118140960795 + 1707578 * 2 ^ 59
def prefixEnd_1707578 : Nat := 4983230072969 + 3 ^ 40 * 1707578 * 2
def baseEnd_1707578 : Nat := 584538846028816884614665

theorem tailTrace_1707578 : CollatzResearch.WordTrace tailWord_1707578 prefixEnd_1707578 584538846028816884614665 := by
  unfold tailWord_1707578
  simp only [CollatzResearch.WordTrace]
  refine ⟨15570121551936002987392847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41520324138496007966380925 15570121551936002987392847)
  ·
    refine ⟨23355182327904004481089271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15570121551936002987392847 23355182327904004481089271)
    ·
      refine ⟨35032773491856006721633907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23355182327904004481089271 35032773491856006721633907)
      ·
        refine ⟨52549160237784010082450861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35032773491856006721633907 52549160237784010082450861)
        ·
          refine ⟨19705935089169003780919073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52549160237784010082450861 19705935089169003780919073)
          ·
            refine ⟨14779451316876752835689305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19705935089169003780919073 14779451316876752835689305)
            ·
              refine ⟨11084588487657564626766979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14779451316876752835689305 11084588487657564626766979)
              ·
                refine ⟨16626882731486346940150469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11084588487657564626766979 16626882731486346940150469)
                ·
                  refine ⟨3117540512153690051278213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16626882731486346940150469 3117540512153690051278213)
                  ·
                    refine ⟨584538846028816884614665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3117540512153690051278213 584538846028816884614665)
                    ·
                      rfl

theorem cell22_1707578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_1707578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707578 prefixEnd_1707578 := by exact prefixLift 1707578
  have htrace : WordTrace (prefixWord ++ tailWord_1707578) baseStart_1707578 baseEnd_1707578 := by
    simpa [prefixWord, tailWord_1707578, baseEnd_1707578] using wordTrace_append hprefix tailTrace_1707578
  have hstable : (prefixWord ++ tailWord_1707578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707578).length < 2 ^ (prefixWord ++ tailWord_1707578).sum := by decide
  have hdescent : baseEnd_1707578 < baseStart_1707578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707653 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 1, 7]
def baseStart_1707653 : Nat := 118140960795 + 1707653 * 2 ^ 59
def prefixEnd_1707653 : Nat := 4983230072969 + 3 ^ 40 * 1707653 * 2
def baseEnd_1707653 : Nat := 584564520061541688989435

theorem tailTrace_1707653 : CollatzResearch.WordTrace tailWord_1707653 prefixEnd_1707653 584564520061541688989435 := by
  unfold tailWord_1707653
  simp only [CollatzResearch.WordTrace]
  refine ⟨62283221682472299758551613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41522147788314866505701075 62283221682472299758551613)
  ·
    refine ⟨23356208130927112409456855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62283221682472299758551613 23356208130927112409456855)
    ·
      refine ⟨35034312196390668614185283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23356208130927112409456855 35034312196390668614185283)
      ·
        refine ⟨52551468294586002921277925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35034312196390668614185283 52551468294586002921277925)
        ·
          refine ⟨9853400305234875547739611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52551468294586002921277925 9853400305234875547739611)
          ·
            refine ⟨14780100457852313321609417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9853400305234875547739611 14780100457852313321609417)
            ·
              refine ⟨11085075343389234991207063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14780100457852313321609417 11085075343389234991207063)
              ·
                refine ⟨16627613015083852486810595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11085075343389234991207063 16627613015083852486810595)
                ·
                  refine ⟨24941419522625778730215893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16627613015083852486810595 24941419522625778730215893)
                  ·
                    refine ⟨584564520061541688989435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24941419522625778730215893 584564520061541688989435)
                    ·
                      rfl

theorem cell22_1707653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_1707653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707653 prefixEnd_1707653 := by exact prefixLift 1707653
  have htrace : WordTrace (prefixWord ++ tailWord_1707653) baseStart_1707653 baseEnd_1707653 := by
    simpa [prefixWord, tailWord_1707653, baseEnd_1707653] using wordTrace_append hprefix tailTrace_1707653
  have hstable : (prefixWord ++ tailWord_1707653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707653).length < 2 ^ (prefixWord ++ tailWord_1707653).sum := by decide
  have hdescent : baseEnd_1707653 < baseStart_1707653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707655 : List Nat := [1, 1, 4, 2, 1, 4, 1, 3, 5]
def baseStart_1707655 : Nat := 118140960795 + 1707655 * 2 ^ 59
def prefixEnd_1707655 : Nat := 4983230072969 + 3 ^ 40 * 1707655 * 2
def baseEnd_1707655 : Nat := 194855068234138116813143

theorem tailTrace_1707655 : CollatzResearch.WordTrace tailWord_1707655 prefixEnd_1707655 194855068234138116813143 := by
  unfold tailWord_1707655
  simp only [CollatzResearch.WordTrace]
  refine ⟨62283294628465054100124419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41522196418976702733416279 62283294628465054100124419)
  ·
    refine ⟨93424941942697581150186629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62283294628465054100124419 93424941942697581150186629)
    ·
      refine ⟨17517176614255796465659993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93424941942697581150186629 17517176614255796465659993)
      ·
        refine ⟨13137882460691847349244995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17517176614255796465659993 13137882460691847349244995)
        ·
          refine ⟨19706823691037771023867493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13137882460691847349244995 19706823691037771023867493)
          ·
            refine ⟨3695029442069582066975155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19706823691037771023867493 3695029442069582066975155)
            ·
              refine ⟨5542544163104373100462733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3695029442069582066975155 5542544163104373100462733)
              ·
                refine ⟨2078454061164139912673525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5542544163104373100462733 2078454061164139912673525)
                ·
                  refine ⟨194855068234138116813143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2078454061164139912673525 194855068234138116813143)
                  ·
                    rfl

theorem cell22_1707655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 5].length) (baseStart_1707655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707655 prefixEnd_1707655 := by exact prefixLift 1707655
  have htrace : WordTrace (prefixWord ++ tailWord_1707655) baseStart_1707655 baseEnd_1707655 := by
    simpa [prefixWord, tailWord_1707655, baseEnd_1707655] using wordTrace_append hprefix tailTrace_1707655
  have hstable : (prefixWord ++ tailWord_1707655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707655).length < 2 ^ (prefixWord ++ tailWord_1707655).sum := by decide
  have hdescent : baseEnd_1707655 < baseStart_1707655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707685 : List Nat := [1, 3, 1, 2, 1, 2, 2, 5, 1, 4]
def baseStart_1707685 : Nat := 118140960795 + 1707685 * 2 ^ 59
def prefixEnd_1707685 : Nat := 4983230072969 + 3 ^ 40 * 1707685 * 2
def baseEnd_1707685 : Nat := 584575474315504272189337

theorem tailTrace_1707685 : CollatzResearch.WordTrace tailWord_1707685 prefixEnd_1707685 584575474315504272189337 := by
  unfold tailWord_1707685
  simp only [CollatzResearch.WordTrace]
  refine ⟨62284388818356369223716509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41522925878904246149144339 62284388818356369223716509)
  ·
    refine ⟨23356645806883638458893691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62284388818356369223716509 23356645806883638458893691)
    ·
      refine ⟨35034968710325457688340537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23356645806883638458893691 35034968710325457688340537)
      ·
        refine ⟨26276226532744093266255403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35034968710325457688340537 26276226532744093266255403)
        ·
          refine ⟨39414339799116139899383105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26276226532744093266255403 39414339799116139899383105)
          ·
            refine ⟨29560754849337104924537329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39414339799116139899383105 29560754849337104924537329)
            ·
              refine ⟨22170566137002828693402997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29560754849337104924537329 22170566137002828693402997)
              ·
                refine ⟨2078490575344015190006531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22170566137002828693402997 2078490575344015190006531)
                ·
                  refine ⟨3117735863016022785009797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2078490575344015190006531 3117735863016022785009797)
                  ·
                    refine ⟨584575474315504272189337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3117735863016022785009797 584575474315504272189337)
                    ·
                      rfl

theorem cell22_1707685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_1707685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707685 prefixEnd_1707685 := by exact prefixLift 1707685
  have htrace : WordTrace (prefixWord ++ tailWord_1707685) baseStart_1707685 baseEnd_1707685 := by
    simpa [prefixWord, tailWord_1707685, baseEnd_1707685] using wordTrace_append hprefix tailTrace_1707685
  have hstable : (prefixWord ++ tailWord_1707685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707685).length < 2 ^ (prefixWord ++ tailWord_1707685).sum := by decide
  have hdescent : baseEnd_1707685 < baseStart_1707685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707732 : List Nat := [2, 4, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_1707732 : Nat := 118140960795 + 1707732 * 2 ^ 59
def prefixEnd_1707732 : Nat := 4983230072969 + 3 ^ 40 * 1707732 * 2
def baseEnd_1707732 : Nat := 584591563376011816264193

theorem tailTrace_1707732 : CollatzResearch.WordTrace tailWord_1707732 prefixEnd_1707732 584591563376011816264193 := by
  unfold tailWord_1707732
  simp only [CollatzResearch.WordTrace]
  refine ⟨31143051524593048125338725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41524068699457397500451633 31143051524593048125338725)
  ·
    refine ⟨5839322160861196523501011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31143051524593048125338725 5839322160861196523501011)
    ·
      refine ⟨8758983241291794785251517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5839322160861196523501011 8758983241291794785251517)
      ·
        refine ⟨3284618715484423044469319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8758983241291794785251517 3284618715484423044469319)
        ·
          refine ⟨4926928073226634566703979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3284618715484423044469319 4926928073226634566703979)
          ·
            refine ⟨7390392109839951850055969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4926928073226634566703979 7390392109839951850055969)
            ·
              refine ⟨5542794082379963887541977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7390392109839951850055969 5542794082379963887541977)
              ·
                refine ⟨4157095561784972915656483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5542794082379963887541977 4157095561784972915656483)
                ·
                  refine ⟨6235643342677459373484725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4157095561784972915656483 6235643342677459373484725)
                  ·
                    refine ⟨584591563376011816264193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6235643342677459373484725 584591563376011816264193)
                    ·
                      rfl

theorem cell22_1707732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_1707732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707732 prefixEnd_1707732 := by exact prefixLift 1707732
  have htrace : WordTrace (prefixWord ++ tailWord_1707732) baseStart_1707732 baseEnd_1707732 := by
    simpa [prefixWord, tailWord_1707732, baseEnd_1707732] using wordTrace_append hprefix tailTrace_1707732
  have hstable : (prefixWord ++ tailWord_1707732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707732).length < 2 ^ (prefixWord ++ tailWord_1707732).sum := by decide
  have hdescent : baseEnd_1707732 < baseStart_1707732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707745 : List Nat := [1, 2, 3, 1, 5, 1, 9]
def baseStart_1707745 : Nat := 118140960795 + 1707745 * 2 ^ 59
def prefixEnd_1707745 : Nat := 4983230072969 + 3 ^ 40 * 1707745 * 2
def baseEnd_1707745 : Nat := 21651704205247559840339

theorem tailTrace_1707745 : CollatzResearch.WordTrace tailWord_1707745 prefixEnd_1707745 21651704205247559840339 := by
  unfold tailWord_1707745
  simp only [CollatzResearch.WordTrace]
  refine ⟨62286577198138999470900689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41524384798759332980600459 62286577198138999470900689)
  ·
    refine ⟨46714932898604249603175517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62286577198138999470900689 46714932898604249603175517)
    ·
      refine ⟨17518099836976593601190819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46714932898604249603175517 17518099836976593601190819)
      ·
        refine ⟨26277149755464890401786229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17518099836976593601190819 26277149755464890401786229)
        ·
          refine ⟨2463482789574833475167459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26277149755464890401786229 2463482789574833475167459)
          ·
            refine ⟨3695224184362250212751189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2463482789574833475167459 3695224184362250212751189)
            ·
              refine ⟨21651704205247559840339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3695224184362250212751189 21651704205247559840339)
              ·
                rfl

theorem cell22_1707745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 9].length) (baseStart_1707745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707745 prefixEnd_1707745 := by exact prefixLift 1707745
  have htrace : WordTrace (prefixWord ++ tailWord_1707745) baseStart_1707745 baseEnd_1707745 := by
    simpa [prefixWord, tailWord_1707745, baseEnd_1707745] using wordTrace_append hprefix tailTrace_1707745
  have hstable : (prefixWord ++ tailWord_1707745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707745).length < 2 ^ (prefixWord ++ tailWord_1707745).sum := by decide
  have hdescent : baseEnd_1707745 < baseStart_1707745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707764 : List Nat := [2, 6, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_1707764 : Nat := 118140960795 + 1707764 * 2 ^ 59
def prefixEnd_1707764 : Nat := 4983230072969 + 3 ^ 40 * 1707764 * 2
def baseEnd_1707764 : Nat := 584602517629974399464095

theorem tailTrace_1707764 : CollatzResearch.WordTrace tailWord_1707764 prefixEnd_1707764 584602517629974399464095 := by
  unfold tailWord_1707764
  simp only [CollatzResearch.WordTrace]
  refine ⟨31143635092535082857921173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41524846790046777143894897 31143635092535082857921173)
  ·
    refine ⟨1459857894962582008965055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31143635092535082857921173 1459857894962582008965055)
    ·
      refine ⟨2189786842443873013447583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1459857894962582008965055 2189786842443873013447583)
      ·
        refine ⟨3284680263665809520171375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2189786842443873013447583 3284680263665809520171375)
        ·
          refine ⟨4927020395498714280257063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3284680263665809520171375 4927020395498714280257063)
          ·
            refine ⟨7390530593248071420385595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4927020395498714280257063 7390530593248071420385595)
            ·
              refine ⟨11085795889872107130578393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7390530593248071420385595 11085795889872107130578393)
              ·
                refine ⟨8314346917404080347933795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11085795889872107130578393 8314346917404080347933795)
                ·
                  refine ⟨12471520376106120521900693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8314346917404080347933795 12471520376106120521900693)
                  ·
                    refine ⟨584602517629974399464095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12471520376106120521900693 584602517629974399464095)
                    ·
                      rfl

theorem cell22_1707764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_1707764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707764 prefixEnd_1707764 := by exact prefixLift 1707764
  have htrace : WordTrace (prefixWord ++ tailWord_1707764) baseStart_1707764 baseEnd_1707764 := by
    simpa [prefixWord, tailWord_1707764, baseEnd_1707764] using wordTrace_append hprefix tailTrace_1707764
  have hstable : (prefixWord ++ tailWord_1707764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707764).length < 2 ^ (prefixWord ++ tailWord_1707764).sum := by decide
  have hdescent : baseEnd_1707764 < baseStart_1707764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707766 : List Nat := [5, 1, 1, 1, 1, 4, 3, 1, 2, 3]
def baseStart_1707766 : Nat := 118140960795 + 1707766 * 2 ^ 59
def prefixEnd_1707766 : Nat := 4983230072969 + 3 ^ 40 * 1707766 * 2
def baseEnd_1707766 : Nat := 584603202270847060914089

theorem tailTrace_1707766 : CollatzResearch.WordTrace tailWord_1707766 prefixEnd_1707766 584603202270847060914089 := by
  unfold tailWord_1707766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3892958945691432503588447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41524895420708613371610101 3892958945691432503588447)
  ·
    refine ⟨5839438418537148755382671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3892958945691432503588447 5839438418537148755382671)
    ·
      refine ⟨8759157627805723133074007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5839438418537148755382671 8759157627805723133074007)
      ·
        refine ⟨13138736441708584699611011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8759157627805723133074007 13138736441708584699611011)
        ·
          refine ⟨19708104662562877049416517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13138736441708584699611011 19708104662562877049416517)
          ·
            refine ⟨3695269624230539446765597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19708104662562877049416517 3695269624230539446765597)
            ·
              refine ⟨1385726109086452292537099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3695269624230539446765597 1385726109086452292537099)
              ·
                refine ⟨2078589163629678438805649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1385726109086452292537099 2078589163629678438805649)
                ·
                  refine ⟨1558941872722258829104237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2078589163629678438805649 1558941872722258829104237)
                  ·
                    refine ⟨584603202270847060914089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1558941872722258829104237 584603202270847060914089)
                    ·
                      rfl

theorem cell22_1707766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_1707766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707766 prefixEnd_1707766 := by exact prefixLift 1707766
  have htrace : WordTrace (prefixWord ++ tailWord_1707766) baseStart_1707766 baseEnd_1707766 := by
    simpa [prefixWord, tailWord_1707766, baseEnd_1707766] using wordTrace_append hprefix tailTrace_1707766
  have hstable : (prefixWord ++ tailWord_1707766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707766).length < 2 ^ (prefixWord ++ tailWord_1707766).sum := by decide
  have hdescent : baseEnd_1707766 < baseStart_1707766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707777 : List Nat := [1, 2, 4, 1, 1, 1, 4, 2, 3, 3]
def baseStart_1707777 : Nat := 118140960795 + 1707777 * 2 ^ 59
def prefixEnd_1707777 : Nat := 4983230072969 + 3 ^ 40 * 1707777 * 2
def baseEnd_1707777 : Nat := 584606967795646698889055

theorem tailTrace_1707777 : CollatzResearch.WordTrace tailWord_1707777 prefixEnd_1707777 584606967795646698889055 := by
  unfold tailWord_1707777
  simp only [CollatzResearch.WordTrace]
  refine ⟨62287744334023068936065585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41525162889348712624043723 62287744334023068936065585)
  ·
    refine ⟨46715808250517301702049189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62287744334023068936065585 46715808250517301702049189)
    ·
      refine ⟨8759214046971994069134223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46715808250517301702049189 8759214046971994069134223)
      ·
        refine ⟨13138821070457991103701335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8759214046971994069134223 13138821070457991103701335)
        ·
          refine ⟨19708231605686986655552003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13138821070457991103701335 19708231605686986655552003)
          ·
            refine ⟨29562347408530479983328005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19708231605686986655552003 29562347408530479983328005)
            ·
              refine ⟨5542940139099464996874001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29562347408530479983328005 5542940139099464996874001)
              ·
                refine ⟨4157205104324598747655501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5542940139099464996874001 4157205104324598747655501)
                ·
                  refine ⟨1558951914121724530370813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4157205104324598747655501 1558951914121724530370813)
                  ·
                    refine ⟨584606967795646698889055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1558951914121724530370813 584606967795646698889055)
                    ·
                      rfl

theorem cell22_1707777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_1707777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707777 prefixEnd_1707777 := by exact prefixLift 1707777
  have htrace : WordTrace (prefixWord ++ tailWord_1707777) baseStart_1707777 baseEnd_1707777 := by
    simpa [prefixWord, tailWord_1707777, baseEnd_1707777] using wordTrace_append hprefix tailTrace_1707777
  have hstable : (prefixWord ++ tailWord_1707777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707777).length < 2 ^ (prefixWord ++ tailWord_1707777).sum := by decide
  have hdescent : baseEnd_1707777 < baseStart_1707777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707790 : List Nat := [4, 1, 1, 2, 1, 1, 3, 2, 7]
def baseStart_1707790 : Nat := 118140960795 + 1707790 * 2 ^ 59
def prefixEnd_1707790 : Nat := 4983230072969 + 3 ^ 40 * 1707790 * 2
def baseEnd_1707790 : Nat := 194870472653772999438005

theorem tailTrace_1707790 : CollatzResearch.WordTrace tailWord_1707790 prefixEnd_1707790 194870472653772999438005 := by
  unfold tailWord_1707790
  simp only [CollatzResearch.WordTrace]
  refine ⟨7786027310371996519536103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41525478988650648104192549 7786027310371996519536103)
  ·
    refine ⟨11679040965557994779304155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7786027310371996519536103 11679040965557994779304155)
    ·
      refine ⟨17518561448336992168956233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11679040965557994779304155 17518561448336992168956233)
      ·
        refine ⟨13138921086252744126717175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17518561448336992168956233 13138921086252744126717175)
        ·
          refine ⟨19708381629379116190075763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13138921086252744126717175 19708381629379116190075763)
          ·
            refine ⟨29562572444068674285113645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19708381629379116190075763 29562572444068674285113645)
            ·
              refine ⟨11085964666525752856917617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29562572444068674285113645 11085964666525752856917617)
              ·
                refine ⟨8314473499894314642688213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11085964666525752856917617 8314473499894314642688213)
                ·
                  refine ⟨194870472653772999438005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8314473499894314642688213 194870472653772999438005)
                  ·
                    rfl

theorem cell22_1707790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_1707790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707790 prefixEnd_1707790 := by exact prefixLift 1707790
  have htrace : WordTrace (prefixWord ++ tailWord_1707790) baseStart_1707790 baseEnd_1707790 := by
    simpa [prefixWord, tailWord_1707790, baseEnd_1707790] using wordTrace_append hprefix tailTrace_1707790
  have hstable : (prefixWord ++ tailWord_1707790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707790).length < 2 ^ (prefixWord ++ tailWord_1707790).sum := by decide
  have hdescent : baseEnd_1707790 < baseStart_1707790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707796 : List Nat := [2, 4, 4, 1, 1, 2, 8]
def baseStart_1707796 : Nat := 118140960795 + 1707796 * 2 ^ 59
def prefixEnd_1707796 : Nat := 4983230072969 + 3 ^ 40 * 1707796 * 2
def baseEnd_1707796 : Nat := 21652350810516184543111

theorem tailTrace_1707796 : CollatzResearch.WordTrace tailWord_1707796 prefixEnd_1707796 21652350810516184543111 := by
  unfold tailWord_1707796
  simp only [CollatzResearch.WordTrace]
  refine ⟨31144218660477117590503621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41525624880636156787338161 31144218660477117590503621)
  ·
    refine ⟨5839540998839459548219429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31144218660477117590503621 5839540998839459548219429)
    ·
      refine ⟨1094913937282398665291143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5839540998839459548219429 1094913937282398665291143)
      ·
        refine ⟨1642370905923597997936715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1094913937282398665291143 1642370905923597997936715)
        ·
          refine ⟨2463556358885396996905073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1642370905923597997936715 2463556358885396996905073)
          ·
            refine ⟨1847667269164047747678805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2463556358885396996905073 1847667269164047747678805)
            ·
              refine ⟨21652350810516184543111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1847667269164047747678805 21652350810516184543111)
              ·
                rfl

theorem cell22_1707796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 8].length) (baseStart_1707796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707796 prefixEnd_1707796 := by exact prefixLift 1707796
  have htrace : WordTrace (prefixWord ++ tailWord_1707796) baseStart_1707796 baseEnd_1707796 := by
    simpa [prefixWord, tailWord_1707796, baseEnd_1707796] using wordTrace_append hprefix tailTrace_1707796
  have hstable : (prefixWord ++ tailWord_1707796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707796).length < 2 ^ (prefixWord ++ tailWord_1707796).sum := by decide
  have hdescent : baseEnd_1707796 < baseStart_1707796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707884 : List Nat := [2, 2, 1, 1, 4, 2, 2, 3, 2, 3]
def baseStart_1707884 : Nat := 118140960795 + 1707884 * 2 ^ 59
def prefixEnd_1707884 : Nat := 4983230072969 + 3 ^ 40 * 1707884 * 2
def baseEnd_1707884 : Nat := 584643596082334086463727

theorem tailTrace_1707884 : CollatzResearch.WordTrace tailWord_1707884 prefixEnd_1707884 584643596082334086463727 := by
  unfold tailWord_1707884
  simp only [CollatzResearch.WordTrace]
  refine ⟨31145823472317713105105353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41527764629756950806807137 31145823472317713105105353)
  ·
    refine ⟨23359367604238284828829015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31145823472317713105105353 23359367604238284828829015)
    ·
      refine ⟨35039051406357427243243523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23359367604238284828829015 35039051406357427243243523)
      ·
        refine ⟨52558577109536140864865285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35039051406357427243243523 52558577109536140864865285)
        ·
          refine ⟨9854733208038026412162241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52558577109536140864865285 9854733208038026412162241)
          ·
            refine ⟨7391049906028519809121681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9854733208038026412162241 7391049906028519809121681)
            ·
              refine ⟨5543287429521389856841261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7391049906028519809121681 5543287429521389856841261)
              ·
                refine ⟨2078732786070521196315473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5543287429521389856841261 2078732786070521196315473)
                ·
                  refine ⟨1559049589552890897236605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2078732786070521196315473 1559049589552890897236605)
                  ·
                    refine ⟨584643596082334086463727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1559049589552890897236605 584643596082334086463727)
                    ·
                      rfl

theorem cell22_1707884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 3].length) (baseStart_1707884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707884 prefixEnd_1707884 := by exact prefixLift 1707884
  have htrace : WordTrace (prefixWord ++ tailWord_1707884) baseStart_1707884 baseEnd_1707884 := by
    simpa [prefixWord, tailWord_1707884, baseEnd_1707884] using wordTrace_append hprefix tailTrace_1707884
  have hstable : (prefixWord ++ tailWord_1707884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707884).length < 2 ^ (prefixWord ++ tailWord_1707884).sum := by decide
  have hdescent : baseEnd_1707884 < baseStart_1707884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707897 : List Nat := [1, 2, 1, 3, 2, 2, 5, 6]
def baseStart_1707897 : Nat := 118140960795 + 1707897 * 2 ^ 59
def prefixEnd_1707897 : Nat := 4983230072969 + 3 ^ 40 * 1707897 * 2
def baseEnd_1707897 : Nat := 64960894027556265098743

theorem tailTrace_1707897 : CollatzResearch.WordTrace tailWord_1707897 prefixEnd_1707897 64960894027556265098743 := by
  unfold tailWord_1707897
  simp only [CollatzResearch.WordTrace]
  refine ⟨62292121093588329430433945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41528080729058886286955963 62292121093588329430433945)
  ·
    refine ⟨46719090820191247072825459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62292121093588329430433945 46719090820191247072825459)
    ·
      refine ⟨70078636230286870609238189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46719090820191247072825459 70078636230286870609238189)
      ·
        refine ⟨26279488586357576478464321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70078636230286870609238189 26279488586357576478464321)
        ·
          refine ⟨19709616439768182358848241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26279488586357576478464321 19709616439768182358848241)
          ·
            refine ⟨14782212329826136769136181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19709616439768182358848241 14782212329826136769136181)
            ·
              refine ⟨1385832405921200322106517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14782212329826136769136181 1385832405921200322106517)
              ·
                refine ⟨64960894027556265098743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1385832405921200322106517 64960894027556265098743)
                ·
                  rfl

theorem cell22_1707897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 6].length) (baseStart_1707897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707897 prefixEnd_1707897 := by exact prefixLift 1707897
  have htrace : WordTrace (prefixWord ++ tailWord_1707897) baseStart_1707897 baseEnd_1707897 := by
    simpa [prefixWord, tailWord_1707897, baseEnd_1707897] using wordTrace_append hprefix tailTrace_1707897
  have hstable : (prefixWord ++ tailWord_1707897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707897).length < 2 ^ (prefixWord ++ tailWord_1707897).sum := by decide
  have hdescent : baseEnd_1707897 < baseStart_1707897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707905 : List Nat := [1, 2, 4, 4, 2, 1, 2, 1, 1, 4]
def baseStart_1707905 : Nat := 118140960795 + 1707905 * 2 ^ 59
def prefixEnd_1707905 : Nat := 4983230072969 + 3 ^ 40 * 1707905 * 2
def baseEnd_1707905 : Nat := 584650784811497031688663

theorem tailTrace_1707905 : CollatzResearch.WordTrace tailWord_1707905 prefixEnd_1707905 584650784811497031688663 := by
  unfold tailWord_1707905
  simp only [CollatzResearch.WordTrace]
  refine ⟨62292412877559346796725169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41528275251706231197816779 62292412877559346796725169)
  ·
    refine ⟨46719309658169510097543877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62292412877559346796725169 46719309658169510097543877)
    ·
      refine ⟨8759870560906783143289477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46719309658169510097543877 8759870560906783143289477)
      ·
        refine ⟨1642475730170021839366777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8759870560906783143289477 1642475730170021839366777)
        ·
          refine ⟨1231856797627516379525083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1642475730170021839366777 1231856797627516379525083)
          ·
            refine ⟨1847785196441274569287625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1231856797627516379525083 1847785196441274569287625)
            ·
              refine ⟨1385838897330955926965719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1847785196441274569287625 1385838897330955926965719)
              ·
                refine ⟨2078758345996433890448579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1385838897330955926965719 2078758345996433890448579)
                ·
                  refine ⟨3118137518994650835672869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2078758345996433890448579 3118137518994650835672869)
                  ·
                    refine ⟨584650784811497031688663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3118137518994650835672869 584650784811497031688663)
                    ·
                      rfl

theorem cell22_1707905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_1707905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707905 prefixEnd_1707905 := by exact prefixLift 1707905
  have htrace : WordTrace (prefixWord ++ tailWord_1707905) baseStart_1707905 baseEnd_1707905 := by
    simpa [prefixWord, tailWord_1707905, baseEnd_1707905] using wordTrace_append hprefix tailTrace_1707905
  have hstable : (prefixWord ++ tailWord_1707905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707905).length < 2 ^ (prefixWord ++ tailWord_1707905).sum := by decide
  have hdescent : baseEnd_1707905 < baseStart_1707905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707993 : List Nat := [1, 2, 1, 2, 7, 1, 2, 1, 5]
def baseStart_1707993 : Nat := 118140960795 + 1707993 * 2 ^ 59
def prefixEnd_1707993 : Nat := 4983230072969 + 3 ^ 40 * 1707993 * 2
def baseEnd_1707993 : Nat := 194893636336631378496131

theorem tailTrace_1707993 : CollatzResearch.WordTrace tailWord_1707993 prefixEnd_1707993 194893636336631378496131 := by
  unfold tailWord_1707993
  simp only [CollatzResearch.WordTrace]
  refine ⟨62295622501240537825928633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41530415000827025217285755 62295622501240537825928633)
  ·
    refine ⟨46721716875930403369446475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62295622501240537825928633 46721716875930403369446475)
    ·
      refine ⟨70082575313895605054169713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46721716875930403369446475 70082575313895605054169713)
      ·
        refine ⟨52561931485421703790627285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70082575313895605054169713 52561931485421703790627285)
        ·
          refine ⟨1231920269189571182592827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 52561931485421703790627285 1231920269189571182592827)
          ·
            refine ⟨1847880403784356773889241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1231920269189571182592827 1847880403784356773889241)
            ·
              refine ⟨1385910302838267580416931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1847880403784356773889241 1385910302838267580416931)
              ·
                refine ⟨2078865454257401370625397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1385910302838267580416931 2078865454257401370625397)
                ·
                  refine ⟨194893636336631378496131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2078865454257401370625397 194893636336631378496131)
                  ·
                    rfl

theorem cell22_1707993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 5].length) (baseStart_1707993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1707993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1707993 prefixEnd_1707993 := by exact prefixLift 1707993
  have htrace : WordTrace (prefixWord ++ tailWord_1707993) baseStart_1707993 baseEnd_1707993 := by
    simpa [prefixWord, tailWord_1707993, baseEnd_1707993] using wordTrace_append hprefix tailTrace_1707993
  have hstable : (prefixWord ++ tailWord_1707993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707993).length < 2 ^ (prefixWord ++ tailWord_1707993).sum := by decide
  have hdescent : baseEnd_1707993 < baseStart_1707993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708068 : List Nat := [2, 3, 1, 4, 2, 2, 1, 1, 2, 4]
def baseStart_1708068 : Nat := 118140960795 + 1708068 * 2 ^ 59
def prefixEnd_1708068 : Nat := 4983230072969 + 3 ^ 40 * 1708068 * 2
def baseEnd_1708068 : Nat := 584706583042618939863163

theorem tailTrace_1708068 : CollatzResearch.WordTrace tailWord_1708068 prefixEnd_1708068 584706583042618939863163 := by
  unfold tailWord_1708068
  simp only [CollatzResearch.WordTrace]
  refine ⟨31149178987984412817454429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41532238650645883756605905 31149178987984412817454429)
  ·
    refine ⟨11680942120494154806545411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31149178987984412817454429 11680942120494154806545411)
    ·
      refine ⟨17521413180741232209818117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11680942120494154806545411 17521413180741232209818117)
      ·
        refine ⟨3285264971388981039340897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17521413180741232209818117 3285264971388981039340897)
        ·
          refine ⟨2463948728541735779505673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3285264971388981039340897 2463948728541735779505673)
          ·
            refine ⟨1847961546406301834629255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2463948728541735779505673 1847961546406301834629255)
            ·
              refine ⟨2771942319609452751943883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1847961546406301834629255 2771942319609452751943883)
              ·
                refine ⟨4157913479414179127915825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2771942319609452751943883 4157913479414179127915825)
                ·
                  refine ⟨3118435109560634345936869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4157913479414179127915825 3118435109560634345936869)
                  ·
                    refine ⟨584706583042618939863163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3118435109560634345936869 584706583042618939863163)
                    ·
                      rfl

theorem cell22_1708068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_1708068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1708068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1708068 prefixEnd_1708068 := by exact prefixLift 1708068
  have htrace : WordTrace (prefixWord ++ tailWord_1708068) baseStart_1708068 baseEnd_1708068 := by
    simpa [prefixWord, tailWord_1708068, baseEnd_1708068] using wordTrace_append hprefix tailTrace_1708068
  have hstable : (prefixWord ++ tailWord_1708068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708068).length < 2 ^ (prefixWord ++ tailWord_1708068).sum := by decide
  have hdescent : baseEnd_1708068 < baseStart_1708068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708141 : List Nat := [1, 5, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_1708141 : Nat := 118140960795 + 1708141 * 2 ^ 59
def prefixEnd_1708141 : Nat := 4983230072969 + 3 ^ 40 * 1708141 * 2
def baseEnd_1708141 : Nat := 584731572434471082787939

theorem tailTrace_1708141 : CollatzResearch.WordTrace tailWord_1708141 prefixEnd_1708141 584731572434471082787939 := by
  unfold tailWord_1708141
  simp only [CollatzResearch.WordTrace]
  refine ⟨62301020504704359102316277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41534013669802906068210851 62301020504704359102316277)
  ·
    refine ⟨5840720672316033665842151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62301020504704359102316277 5840720672316033665842151)
    ·
      refine ⟨8761081008474050498763227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5840720672316033665842151 8761081008474050498763227)
      ·
        refine ⟨13141621512711075748144841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8761081008474050498763227 13141621512711075748144841)
        ·
          refine ⟨9856216134533306811108631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13141621512711075748144841 9856216134533306811108631)
          ·
            refine ⟨14784324201799960216662947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9856216134533306811108631 14784324201799960216662947)
            ·
              refine ⟨22176486302699940324994421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14784324201799960216662947 22176486302699940324994421)
              ·
                refine ⟨2079045590878119405468227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22176486302699940324994421 2079045590878119405468227)
                ·
                  refine ⟨3118568386317179108202341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2079045590878119405468227 3118568386317179108202341)
                  ·
                    refine ⟨584731572434471082787939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3118568386317179108202341 584731572434471082787939)
                    ·
                      rfl

theorem cell22_1708141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_1708141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1708141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1708141 prefixEnd_1708141 := by exact prefixLift 1708141
  have htrace : WordTrace (prefixWord ++ tailWord_1708141) baseStart_1708141 baseEnd_1708141 := by
    simpa [prefixWord, tailWord_1708141, baseEnd_1708141] using wordTrace_append hprefix tailTrace_1708141
  have hstable : (prefixWord ++ tailWord_1708141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708141).length < 2 ^ (prefixWord ++ tailWord_1708141).sum := by decide
  have hdescent : baseEnd_1708141 < baseStart_1708141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708156 : List Nat := [2, 2, 2, 1, 1, 6, 1, 1, 6]
def baseStart_1708156 : Nat := 118140960795 + 1708156 * 2 ^ 59
def prefixEnd_1708156 : Nat := 4983230072969 + 3 ^ 40 * 1708156 * 2
def baseEnd_1708156 : Nat := 194912235747005347887631

theorem tailTrace_1708156 : CollatzResearch.WordTrace tailWord_1708156 prefixEnd_1708156 194912235747005347887631 := by
  unfold tailWord_1708156
  simp only [CollatzResearch.WordTrace]
  refine ⟨31150783799825008332056161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41534378399766677776074881 31150783799825008332056161)
  ·
    refine ⟨23363087849868756249042121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31150783799825008332056161 23363087849868756249042121)
    ·
      refine ⟨17522315887401567186781591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23363087849868756249042121 17522315887401567186781591)
      ·
        refine ⟨26283473831102350780172387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17522315887401567186781591 26283473831102350780172387)
        ·
          refine ⟨39425210746653526170258581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26283473831102350780172387 39425210746653526170258581)
          ·
            refine ⟨1848056753749384039230871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39425210746653526170258581 1848056753749384039230871)
            ·
              refine ⟨2772085130624076058846307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1848056753749384039230871 2772085130624076058846307)
              ·
                refine ⟨4158127695936114088269461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2772085130624076058846307 4158127695936114088269461)
                ·
                  refine ⟨194912235747005347887631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4158127695936114088269461 194912235747005347887631)
                  ·
                    rfl

theorem cell22_1708156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 6].length) (baseStart_1708156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1708156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1708156 prefixEnd_1708156 := by exact prefixLift 1708156
  have htrace : WordTrace (prefixWord ++ tailWord_1708156) baseStart_1708156 baseEnd_1708156 := by
    simpa [prefixWord, tailWord_1708156, baseEnd_1708156] using wordTrace_append hprefix tailTrace_1708156
  have hstable : (prefixWord ++ tailWord_1708156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708156).length < 2 ^ (prefixWord ++ tailWord_1708156).sum := by decide
  have hdescent : baseEnd_1708156 < baseStart_1708156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708169 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 4, 4]
def baseStart_1708169 : Nat := 118140960795 + 1708169 * 2 ^ 59
def prefixEnd_1708169 : Nat := 4983230072969 + 3 ^ 40 * 1708169 * 2
def baseEnd_1708169 : Nat := 584741157406688343087853

theorem tailTrace_1708169 : CollatzResearch.WordTrace tailWord_1708169 prefixEnd_1708169 584741157406688343087853 := by
  unfold tailWord_1708169
  simp only [CollatzResearch.WordTrace]
  refine ⟨62302041748602919884335561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41534694499068613256223707 62302041748602919884335561)
  ·
    refine ⟨46726531311452189913251671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62302041748602919884335561 46726531311452189913251671)
    ·
      refine ⟨70089796967178284869877507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46726531311452189913251671 70089796967178284869877507)
      ·
        refine ⟨105134695450767427304816261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70089796967178284869877507 105134695450767427304816261)
        ·
          refine ⟨19712755397018892619653049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105134695450767427304816261 19712755397018892619653049)
          ·
            refine ⟨14784566547764169464739787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19712755397018892619653049 14784566547764169464739787)
            ·
              refine ⟨22176849821646254197109681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14784566547764169464739787 22176849821646254197109681)
              ·
                refine ⟨16632637366234690647832261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22176849821646254197109681 16632637366234690647832261)
                ·
                  refine ⟨3118619506169004496468549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16632637366234690647832261 3118619506169004496468549)
                  ·
                    refine ⟨584741157406688343087853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3118619506169004496468549 584741157406688343087853)
                    ·
                      rfl

theorem cell22_1708169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 4].length) (baseStart_1708169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1708169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1708169 prefixEnd_1708169 := by exact prefixLift 1708169
  have htrace : WordTrace (prefixWord ++ tailWord_1708169) baseStart_1708169 baseEnd_1708169 := by
    simpa [prefixWord, tailWord_1708169, baseEnd_1708169] using wordTrace_append hprefix tailTrace_1708169
  have hstable : (prefixWord ++ tailWord_1708169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708169).length < 2 ^ (prefixWord ++ tailWord_1708169).sum := by decide
  have hdescent : baseEnd_1708169 < baseStart_1708169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708205 : List Nat := [1, 5, 2, 1, 2, 2, 2, 2, 2, 3]
def baseStart_1708205 : Nat := 118140960795 + 1708205 * 2 ^ 59
def prefixEnd_1708205 : Nat := 4983230072969 + 3 ^ 40 * 1708205 * 2
def baseEnd_1708205 : Nat := 584753480942396249187743

theorem tailTrace_1708205 : CollatzResearch.WordTrace tailWord_1708205 prefixEnd_1708205 584753480942396249187743 := by
  unfold tailWord_1708205
  simp only [CollatzResearch.WordTrace]
  refine ⟨62303354776472498032646069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41535569850981665355097379 62303354776472498032646069)
  ·
    refine ⟨5840939510294296690560569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62303354776472498032646069 5840939510294296690560569)
    ·
      refine ⟨4380704632720722517920427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5840939510294296690560569 4380704632720722517920427)
      ·
        refine ⟨6571056949081083776880641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4380704632720722517920427 6571056949081083776880641)
        ·
          refine ⟨4928292711810812832660481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6571056949081083776880641 4928292711810812832660481)
          ·
            refine ⟨3696219533858109624495361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4928292711810812832660481 3696219533858109624495361)
            ·
              refine ⟨2772164650393582218371521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3696219533858109624495361 2772164650393582218371521)
              ·
                refine ⟨2079123487795186663778641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2772164650393582218371521 2079123487795186663778641)
                ·
                  refine ⟨1559342615846389997833981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2079123487795186663778641 1559342615846389997833981)
                  ·
                    refine ⟨584753480942396249187743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1559342615846389997833981 584753480942396249187743)
                    ·
                      rfl

theorem cell22_1708205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_1708205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1708205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1708205 prefixEnd_1708205 := by exact prefixLift 1708205
  have htrace : WordTrace (prefixWord ++ tailWord_1708205) baseStart_1708205 baseEnd_1708205 := by
    simpa [prefixWord, tailWord_1708205, baseEnd_1708205] using wordTrace_append hprefix tailTrace_1708205
  have hstable : (prefixWord ++ tailWord_1708205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708205).length < 2 ^ (prefixWord ++ tailWord_1708205).sum := by decide
  have hdescent : baseEnd_1708205 < baseStart_1708205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708216 : List Nat := [2, 1, 2, 1, 2, 1, 4, 3, 3, 3]
def baseStart_1708216 : Nat := 118140960795 + 1708216 * 2 ^ 59
def prefixEnd_1708216 : Nat := 4983230072969 + 3 ^ 40 * 1708216 * 2
def baseEnd_1708216 : Nat := 584757246467195887162709

theorem tailTrace_1708216 : CollatzResearch.WordTrace tailWord_1708216 prefixEnd_1708216 584757246467195887162709 := by
  unfold tailWord_1708216
  simp only [CollatzResearch.WordTrace]
  refine ⟨31151877989716323455648251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41535837319621764607531001 31151877989716323455648251)
  ·
    refine ⟨46727816984574485183472377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31151877989716323455648251 46727816984574485183472377)
    ·
      refine ⟨35045862738430863887604283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46727816984574485183472377 35045862738430863887604283)
      ·
        refine ⟨52568794107646295831406425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35045862738430863887604283 52568794107646295831406425)
        ·
          refine ⟨39426595580734721873554819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52568794107646295831406425 39426595580734721873554819)
          ·
            refine ⟨59139893371102082810332229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39426595580734721873554819 59139893371102082810332229)
            ·
              refine ⟨11088730007081640526937293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59139893371102082810332229 11088730007081640526937293)
              ·
                refine ⟨4158273752655615197601485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11088730007081640526937293 4158273752655615197601485)
                ·
                  refine ⟨1559352657245855699100557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4158273752655615197601485 1559352657245855699100557)
                  ·
                    refine ⟨584757246467195887162709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1559352657245855699100557 584757246467195887162709)
                    ·
                      rfl

theorem cell22_1708216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 3, 3].length) (baseStart_1708216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1708216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1708216 prefixEnd_1708216 := by exact prefixLift 1708216
  have htrace : WordTrace (prefixWord ++ tailWord_1708216) baseStart_1708216 baseEnd_1708216 := by
    simpa [prefixWord, tailWord_1708216, baseEnd_1708216] using wordTrace_append hprefix tailTrace_1708216
  have hstable : (prefixWord ++ tailWord_1708216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708216).length < 2 ^ (prefixWord ++ tailWord_1708216).sum := by decide
  have hdescent : baseEnd_1708216 < baseStart_1708216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708261 : List Nat := [1, 3, 1, 4, 2, 1, 1, 2, 2, 5]
def baseStart_1708261 : Nat := 118140960795 + 1708261 * 2 ^ 59
def prefixEnd_1708261 : Nat := 4983230072969 + 3 ^ 40 * 1708261 * 2
def baseEnd_1708261 : Nat := 584772650886830769787571

theorem tailTrace_1708261 : CollatzResearch.WordTrace tailWord_1708261 prefixEnd_1708261 584772650886830769787571 := by
  unfold tailWord_1708261
  simp only [CollatzResearch.WordTrace]
  refine ⟨62305397264269619596684637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41536931509513079731123091 62305397264269619596684637)
  ·
    refine ⟨23364523974101107348756739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62305397264269619596684637 23364523974101107348756739)
    ·
      refine ⟨35046785961151661023135109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23364523974101107348756739 35046785961151661023135109)
      ·
        refine ⟨6571272367715936441837833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35046785961151661023135109 6571272367715936441837833)
        ·
          refine ⟨4928454275786952331378375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6571272367715936441837833 4928454275786952331378375)
          ·
            refine ⟨7392681413680428497067563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4928454275786952331378375 7392681413680428497067563)
            ·
              refine ⟨11089022120520642745601345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7392681413680428497067563 11089022120520642745601345)
              ·
                refine ⟨8316766590390482059201009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11089022120520642745601345 8316766590390482059201009)
                ·
                  refine ⟨6237574942792861544400757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8316766590390482059201009 6237574942792861544400757)
                  ·
                    refine ⟨584772650886830769787571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6237574942792861544400757 584772650886830769787571)
                    ·
                      rfl

theorem cell22_1708261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_1708261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1708261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1708261 prefixEnd_1708261 := by exact prefixLift 1708261
  have htrace : WordTrace (prefixWord ++ tailWord_1708261) baseStart_1708261 baseEnd_1708261 := by
    simpa [prefixWord, tailWord_1708261, baseEnd_1708261] using wordTrace_append hprefix tailTrace_1708261
  have hstable : (prefixWord ++ tailWord_1708261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708261).length < 2 ^ (prefixWord ++ tailWord_1708261).sum := by decide
  have hdescent : baseEnd_1708261 < baseStart_1708261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708263 : List Nat := [1, 1, 5, 3, 1, 1, 3, 2, 5]
def baseStart_1708263 : Nat := 118140960795 + 1708263 * 2 ^ 59
def prefixEnd_1708263 : Nat := 4983230072969 + 3 ^ 40 * 1708263 * 2
def baseEnd_1708263 : Nat := 194924445175901143745855

theorem tailTrace_1708263 : CollatzResearch.WordTrace tailWord_1708263 prefixEnd_1708263 194924445175901143745855 := by
  unfold tailWord_1708263
  simp only [CollatzResearch.WordTrace]
  refine ⟨62305470210262373938257443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41536980140174915958838295 62305470210262373938257443)
  ·
    refine ⟨93458205315393560907386165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62305470210262373938257443 93458205315393560907386165)
    ·
      refine ⟨8761706748318146335067453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93458205315393560907386165 8761706748318146335067453)
      ·
        refine ⟨3285640030619304875650295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8761706748318146335067453 3285640030619304875650295)
        ·
          refine ⟨4928460045928957313475443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3285640030619304875650295 4928460045928957313475443)
          ·
            refine ⟨7392690068893435970213165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4928460045928957313475443 7392690068893435970213165)
            ·
              refine ⟨2772258775835038488829937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7392690068893435970213165 2772258775835038488829937)
              ·
                refine ⟨2079194081876278866622453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2772258775835038488829937 2079194081876278866622453)
                ·
                  refine ⟨194924445175901143745855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2079194081876278866622453 194924445175901143745855)
                  ·
                    rfl

theorem cell22_1708263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 5].length) (baseStart_1708263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1708263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1708263 prefixEnd_1708263 := by exact prefixLift 1708263
  have htrace : WordTrace (prefixWord ++ tailWord_1708263) baseStart_1708263 baseEnd_1708263 := by
    simpa [prefixWord, tailWord_1708263, baseEnd_1708263] using wordTrace_append hprefix tailTrace_1708263
  have hstable : (prefixWord ++ tailWord_1708263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708263).length < 2 ^ (prefixWord ++ tailWord_1708263).sum := by decide
  have hdescent : baseEnd_1708263 < baseStart_1708263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708321 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 4, 4]
def baseStart_1708321 : Nat := 118140960795 + 1708321 * 2 ^ 59
def prefixEnd_1708321 : Nat := 4983230072969 + 3 ^ 40 * 1708321 * 2
def baseEnd_1708321 : Nat := 584793190113010613287387

theorem tailTrace_1708321 : CollatzResearch.WordTrace tailWord_1708321 prefixEnd_1708321 584793190113010613287387 := by
  unfold tailWord_1708321
  simp only [CollatzResearch.WordTrace]
  refine ⟨62307585644052249843868817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41538390429368166562579211 62307585644052249843868817)
  ·
    refine ⟨46730689233039187382901613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62307585644052249843868817 46730689233039187382901613)
    ·
      refine ⟨17524008462389695268588105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46730689233039187382901613 17524008462389695268588105)
      ·
        refine ⟨13143006346792271451441079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17524008462389695268588105 13143006346792271451441079)
        ·
          refine ⟨19714509520188407177161619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13143006346792271451441079 19714509520188407177161619)
          ·
            refine ⟨29571764280282610765742429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19714509520188407177161619 29571764280282610765742429)
            ·
              refine ⟨11089411605105979037153411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29571764280282610765742429 11089411605105979037153411)
              ·
                refine ⟨16634117407658968555730117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11089411605105979037153411 16634117407658968555730117)
                ·
                  refine ⟨3118897013936056604199397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16634117407658968555730117 3118897013936056604199397)
                  ·
                    refine ⟨584793190113010613287387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3118897013936056604199397 584793190113010613287387)
                    ·
                      rfl

theorem cell22_1708321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_1708321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1708321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1708321 prefixEnd_1708321 := by exact prefixLift 1708321
  have htrace : WordTrace (prefixWord ++ tailWord_1708321) baseStart_1708321 baseEnd_1708321 := by
    simpa [prefixWord, tailWord_1708321, baseEnd_1708321] using wordTrace_append hprefix tailTrace_1708321
  have hstable : (prefixWord ++ tailWord_1708321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708321).length < 2 ^ (prefixWord ++ tailWord_1708321).sum := by decide
  have hdescent : baseEnd_1708321 < baseStart_1708321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708323 : List Nat := [1, 1, 1, 4, 2, 2, 2, 4, 2, 3]
def baseStart_1708323 : Nat := 118140960795 + 1708323 * 2 ^ 59
def prefixEnd_1708323 : Nat := 4983230072969 + 3 ^ 40 * 1708323 * 2
def baseEnd_1708323 : Nat := 584793874753883274737381

theorem tailTrace_1708323 : CollatzResearch.WordTrace tailWord_1708323 prefixEnd_1708323 584793874753883274737381 := by
  unfold tailWord_1708323
  simp only [CollatzResearch.WordTrace]
  refine ⟨62307658590045004185441623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41538439060030002790294415 62307658590045004185441623)
  ·
    refine ⟨93461487885067506278162435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62307658590045004185441623 93461487885067506278162435)
    ·
      refine ⟨140192231827601259417243653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93461487885067506278162435 140192231827601259417243653)
      ·
        refine ⟨26286043467675236140733185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140192231827601259417243653 26286043467675236140733185)
        ·
          refine ⟨19714532600756427105549889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26286043467675236140733185 19714532600756427105549889)
          ·
            refine ⟨14785899450567320329162417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19714532600756427105549889 14785899450567320329162417)
            ·
              refine ⟨11089424587925490246871813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14785899450567320329162417 11089424587925490246871813)
              ·
                refine ⟨2079267110236029421288465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11089424587925490246871813 2079267110236029421288465)
                ·
                  refine ⟨1559450332677022065966349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2079267110236029421288465 1559450332677022065966349)
                  ·
                    refine ⟨584793874753883274737381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1559450332677022065966349 584793874753883274737381)
                    ·
                      rfl

theorem cell22_1708323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 3].length) (baseStart_1708323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1708323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1708323 prefixEnd_1708323 := by exact prefixLift 1708323
  have htrace : WordTrace (prefixWord ++ tailWord_1708323) baseStart_1708323 baseEnd_1708323 := by
    simpa [prefixWord, tailWord_1708323, baseEnd_1708323] using wordTrace_append hprefix tailTrace_1708323
  have hstable : (prefixWord ++ tailWord_1708323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708323).length < 2 ^ (prefixWord ++ tailWord_1708323).sum := by decide
  have hdescent : baseEnd_1708323 < baseStart_1708323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708325 : List Nat := [1, 3, 1, 2, 6, 1, 1, 1, 6]
def baseStart_1708325 : Nat := 118140960795 + 1708325 * 2 ^ 59
def prefixEnd_1708325 : Nat := 4983230072969 + 3 ^ 40 * 1708325 * 2
def baseEnd_1708325 : Nat := 194931519798251978729125

theorem tailTrace_1708325 : CollatzResearch.WordTrace tailWord_1708325 prefixEnd_1708325 194931519798251978729125 := by
  unfold tailWord_1708325
  simp only [CollatzResearch.WordTrace]
  refine ⟨62307731536037758527014429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41538487690691839018009619 62307731536037758527014429)
  ·
    refine ⟨23365399326014159447630411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62307731536037758527014429 23365399326014159447630411)
    ·
      refine ⟨35048098989021239171445617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23365399326014159447630411 35048098989021239171445617)
      ·
        refine ⟨26286074241765929378584213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35048098989021239171445617 26286074241765929378584213)
        ·
          refine ⟨1232159730082777939621135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26286074241765929378584213 1232159730082777939621135)
          ·
            refine ⟨1848239595124166909431703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1232159730082777939621135 1848239595124166909431703)
            ·
              refine ⟨2772359392686250364147555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1848239595124166909431703 2772359392686250364147555)
              ·
                refine ⟨4158539089029375546221333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2772359392686250364147555 4158539089029375546221333)
                ·
                  refine ⟨194931519798251978729125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4158539089029375546221333 194931519798251978729125)
                  ·
                    rfl

theorem cell22_1708325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 6].length) (baseStart_1708325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1708325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1708325 prefixEnd_1708325 := by exact prefixLift 1708325
  have htrace : WordTrace (prefixWord ++ tailWord_1708325) baseStart_1708325 baseEnd_1708325 := by
    simpa [prefixWord, tailWord_1708325, baseEnd_1708325] using wordTrace_append hprefix tailTrace_1708325
  have hstable : (prefixWord ++ tailWord_1708325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708325).length < 2 ^ (prefixWord ++ tailWord_1708325).sum := by decide
  have hdescent : baseEnd_1708325 < baseStart_1708325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708473 : List Nat := [1, 2, 1, 4, 3, 1, 2, 1, 1, 6]
def baseStart_1708473 : Nat := 118140960795 + 1708473 * 2 ^ 59
def prefixEnd_1708473 : Nat := 4983230072969 + 3 ^ 40 * 1708473 * 2
def baseEnd_1708473 : Nat := 584845222819332883486921

theorem tailTrace_1708473 : CollatzResearch.WordTrace tailWord_1708473 prefixEnd_1708473 584845222819332883486921 := by
  unfold tailWord_1708473
  simp only [CollatzResearch.WordTrace]
  refine ⟨62313129539501579803402073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41542086359667719868934715 62313129539501579803402073)
  ·
    refine ⟨46734847154626184852551555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62313129539501579803402073 46734847154626184852551555)
    ·
      refine ⟨70102270731939277278827333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46734847154626184852551555 70102270731939277278827333)
      ·
        refine ⟨13144175762238614489780125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70102270731939277278827333 13144175762238614489780125)
        ·
          refine ⟨4929065910839480433667547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13144175762238614489780125 4929065910839480433667547)
          ·
            refine ⟨7393598866259220650501321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4929065910839480433667547 7393598866259220650501321)
            ·
              refine ⟨5545199149694415487875991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7393598866259220650501321 5545199149694415487875991)
              ·
                refine ⟨8317798724541623231813987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5545199149694415487875991 8317798724541623231813987)
                ·
                  refine ⟨12476698086812434847720981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8317798724541623231813987 12476698086812434847720981)
                  ·
                    refine ⟨584845222819332883486921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12476698086812434847720981 584845222819332883486921)
                    ·
                      rfl

theorem cell22_1708473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 6].length) (baseStart_1708473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1708473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1708473 prefixEnd_1708473 := by exact prefixLift 1708473
  have htrace : WordTrace (prefixWord ++ tailWord_1708473) baseStart_1708473 baseEnd_1708473 := by
    simpa [prefixWord, tailWord_1708473, baseEnd_1708473] using wordTrace_append hprefix tailTrace_1708473
  have hstable : (prefixWord ++ tailWord_1708473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708473).length < 2 ^ (prefixWord ++ tailWord_1708473).sum := by decide
  have hdescent : baseEnd_1708473 < baseStart_1708473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708477 : List Nat := [1, 4, 1, 2, 2, 4, 1, 3, 4]
def baseStart_1708477 : Nat := 118140960795 + 1708477 * 2 ^ 59
def prefixEnd_1708477 : Nat := 4983230072969 + 3 ^ 40 * 1708477 * 2
def baseEnd_1708477 : Nat := 194948864033692735462303

theorem tailTrace_1708477 : CollatzResearch.WordTrace tailWord_1708477 prefixEnd_1708477 194948864033692735462303 := by
  unfold tailWord_1708477
  simp only [CollatzResearch.WordTrace]
  refine ⟨62313275431487088486547685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41542183620991392324365123 62313275431487088486547685)
  ·
    refine ⟨11683739143403829091227691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62313275431487088486547685 11683739143403829091227691)
    ·
      refine ⟨17525608715105743636841537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11683739143403829091227691 17525608715105743636841537)
      ·
        refine ⟨13144206536329307727631153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17525608715105743636841537 13144206536329307727631153)
        ·
          refine ⟨9858154902246980795723365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13144206536329307727631153 9858154902246980795723365)
          ·
            refine ⟨1848404044171308899198131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9858154902246980795723365 1848404044171308899198131)
            ·
              refine ⟨2772606066256963348797197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1848404044171308899198131 2772606066256963348797197)
              ·
                refine ⟨1039727274846361255798949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2772606066256963348797197 1039727274846361255798949)
                ·
                  refine ⟨194948864033692735462303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1039727274846361255798949 194948864033692735462303)
                  ·
                    rfl

theorem cell22_1708477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_1708477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1708477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1708477 prefixEnd_1708477 := by exact prefixLift 1708477
  have htrace : WordTrace (prefixWord ++ tailWord_1708477) baseStart_1708477 baseEnd_1708477 := by
    simpa [prefixWord, tailWord_1708477, baseEnd_1708477] using wordTrace_append hprefix tailTrace_1708477
  have hstable : (prefixWord ++ tailWord_1708477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708477).length < 2 ^ (prefixWord ++ tailWord_1708477).sum := by decide
  have hdescent : baseEnd_1708477 < baseStart_1708477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708488 : List Nat := [2, 1, 3, 1, 3, 4, 8]
def baseStart_1708488 : Nat := 118140960795 + 1708488 * 2 ^ 59
def prefixEnd_1708488 : Nat := 4983230072969 + 3 ^ 40 * 1708488 * 2
def baseEnd_1708488 : Nat := 21661124356513994235625

theorem tailTrace_1708488 : CollatzResearch.WordTrace tailWord_1708488 prefixEnd_1708488 21661124356513994235625 := by
  unfold tailWord_1708488
  simp only [CollatzResearch.WordTrace]
  refine ⟨31156838317223618682599059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41542451089631491576798745 31156838317223618682599059)
  ·
    refine ⟨46735257475835428023898589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31156838317223618682599059 46735257475835428023898589)
    ·
      refine ⟨17525721553438285508961971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46735257475835428023898589 17525721553438285508961971)
      ·
        refine ⟨26288582330157428263442957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17525721553438285508961971 26288582330157428263442957)
        ·
          refine ⟨9858218373809035598791109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26288582330157428263442957 9858218373809035598791109)
          ·
            refine ⟨1848415945089194174773333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9858218373809035598791109 1848415945089194174773333)
            ·
              refine ⟨21661124356513994235625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1848415945089194174773333 21661124356513994235625)
              ·
                rfl

theorem cell22_1708488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 8].length) (baseStart_1708488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1708488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1708488 prefixEnd_1708488 := by exact prefixLift 1708488
  have htrace : WordTrace (prefixWord ++ tailWord_1708488) baseStart_1708488 baseEnd_1708488 := by
    simpa [prefixWord, tailWord_1708488, baseEnd_1708488] using wordTrace_append hprefix tailTrace_1708488
  have hstable : (prefixWord ++ tailWord_1708488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708488).length < 2 ^ (prefixWord ++ tailWord_1708488).sum := by decide
  have hdescent : baseEnd_1708488 < baseStart_1708488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708563 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 5, 4]
def baseStart_1708563 : Nat := 118140960795 + 1708563 * 2 ^ 59
def prefixEnd_1708563 : Nat := 4983230072969 + 3 ^ 40 * 1708563 * 2
def baseEnd_1708563 : Nat := 584876031658602648736645

theorem tailTrace_1708563 : CollatzResearch.WordTrace tailWord_1708563 prefixEnd_1708563 584876031658602648736645 := by
  unfold tailWord_1708563
  simp only [CollatzResearch.WordTrace]
  refine ⟨62316412109175525174178343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41544274739450350116118895 62316412109175525174178343)
  ·
    refine ⟨93474618163763287761267515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62316412109175525174178343 93474618163763287761267515)
    ·
      refine ⟨140211927245644931641901273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93474618163763287761267515 140211927245644931641901273)
      ·
        refine ⟨105158945434233698731425955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140211927245644931641901273 105158945434233698731425955)
        ·
          refine ⟨157738418151350548097138933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105158945434233698731425955 157738418151350548097138933)
          ·
            refine ⟨14787976701689113884106775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157738418151350548097138933 14787976701689113884106775)
            ·
              refine ⟨22181965052533670826160163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14787976701689113884106775 22181965052533670826160163)
              ·
                refine ⟨33272947578800506239240245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22181965052533670826160163 33272947578800506239240245)
                ·
                  refine ⟨3119338835512547459928773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33272947578800506239240245 3119338835512547459928773)
                  ·
                    refine ⟨584876031658602648736645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3119338835512547459928773 584876031658602648736645)
                    ·
                      rfl

theorem cell22_1708563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 4].length) (baseStart_1708563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1708563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1708563 prefixEnd_1708563 := by exact prefixLift 1708563
  have htrace : WordTrace (prefixWord ++ tailWord_1708563) baseStart_1708563 baseEnd_1708563 := by
    simpa [prefixWord, tailWord_1708563, baseEnd_1708563] using wordTrace_append hprefix tailTrace_1708563
  have hstable : (prefixWord ++ tailWord_1708563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708563).length < 2 ^ (prefixWord ++ tailWord_1708563).sum := by decide
  have hdescent : baseEnd_1708563 < baseStart_1708563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708640 : List Nat := [2, 1, 1, 3, 2, 1, 6, 6]
def baseStart_1708640 : Nat := 118140960795 + 1708640 * 2 ^ 59
def prefixEnd_1708640 : Nat := 4983230072969 + 3 ^ 40 * 1708640 * 2
def baseEnd_1708640 : Nat := 64989154481355568284601

theorem tailTrace_1708640 : CollatzResearch.WordTrace tailWord_1708640 prefixEnd_1708640 64989154481355568284601 := by
  unfold tailWord_1708640
  simp only [CollatzResearch.WordTrace]
  refine ⟨31159610264948283662365687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41546147019931044883154249 31159610264948283662365687)
  ·
    refine ⟨46739415397422425493548531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31159610264948283662365687 46739415397422425493548531)
    ·
      refine ⟨70109123096133638240322797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46739415397422425493548531 70109123096133638240322797)
      ·
        refine ⟨26290921161050114340121049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70109123096133638240322797 26290921161050114340121049)
        ·
          refine ⟨19718190870787585755090787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26290921161050114340121049 19718190870787585755090787)
          ·
            refine ⟨29577286306181378632636181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19718190870787585755090787 29577286306181378632636181)
            ·
              refine ⟨1386435295602252123404821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29577286306181378632636181 1386435295602252123404821)
              ·
                refine ⟨64989154481355568284601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1386435295602252123404821 64989154481355568284601)
                ·
                  rfl

theorem cell22_1708640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 6].length) (baseStart_1708640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1708640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1708640 prefixEnd_1708640 := by exact prefixLift 1708640
  have htrace : WordTrace (prefixWord ++ tailWord_1708640) baseStart_1708640 baseEnd_1708640 := by
    simpa [prefixWord, tailWord_1708640, baseEnd_1708640] using wordTrace_append hprefix tailTrace_1708640
  have hstable : (prefixWord ++ tailWord_1708640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708640).length < 2 ^ (prefixWord ++ tailWord_1708640).sum := by decide
  have hdescent : baseEnd_1708640 < baseStart_1708640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708655 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 5, 3]
def baseStart_1708655 : Nat := 118140960795 + 1708655 * 2 ^ 59
def prefixEnd_1708655 : Nat := 4983230072969 + 3 ^ 40 * 1708655 * 2
def baseEnd_1708655 : Nat := 584907525138745075436363

theorem tailTrace_1708655 : CollatzResearch.WordTrace tailWord_1708655 prefixEnd_1708655 584907525138745075436363 := by
  unfold tailWord_1708655
  simp only [CollatzResearch.WordTrace]
  refine ⟨62319767624842224886527419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41546511749894816591018279 62319767624842224886527419)
  ·
    refine ⟨93479651437263337329791129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62319767624842224886527419 93479651437263337329791129)
    ·
      refine ⟨70109738577947502997343347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93479651437263337329791129 70109738577947502997343347)
      ·
        refine ⟨105164607866921254496015021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70109738577947502997343347 105164607866921254496015021)
        ·
          refine ⟨39436727950095470436005633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105164607866921254496015021 39436727950095470436005633)
          ·
            refine ⟨29577545962571602827004225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39436727950095470436005633 29577545962571602827004225)
            ·
              refine ⟨22183159471928702120253169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29577545962571602827004225 22183159471928702120253169)
              ·
                refine ⟨16637369603946526590189877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22183159471928702120253169 16637369603946526590189877)
                ·
                  refine ⟨1559753400369986867830301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16637369603946526590189877 1559753400369986867830301)
                  ·
                    refine ⟨584907525138745075436363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1559753400369986867830301 584907525138745075436363)
                    ·
                      rfl

theorem cell22_1708655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5, 3].length) (baseStart_1708655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1708655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1708655 prefixEnd_1708655 := by exact prefixLift 1708655
  have htrace : WordTrace (prefixWord ++ tailWord_1708655) baseStart_1708655 baseEnd_1708655 := by
    simpa [prefixWord, tailWord_1708655, baseEnd_1708655] using wordTrace_append hprefix tailTrace_1708655
  have hstable : (prefixWord ++ tailWord_1708655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708655).length < 2 ^ (prefixWord ++ tailWord_1708655).sum := by decide
  have hdescent : baseEnd_1708655 < baseStart_1708655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708672 : List Nat := [2, 1, 1, 2, 1, 5, 3, 1, 3, 3]
def baseStart_1708672 : Nat := 118140960795 + 1708672 * 2 ^ 59
def prefixEnd_1708672 : Nat := 4983230072969 + 3 ^ 40 * 1708672 * 2
def baseEnd_1708672 : Nat := 584913344586162697761311

theorem tailTrace_1708672 : CollatzResearch.WordTrace tailWord_1708672 prefixEnd_1708672 584913344586162697761311 := by
  unfold tailWord_1708672
  simp only [CollatzResearch.WordTrace]
  refine ⟨31160193832890318394948135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41546925110520424526597513 31160193832890318394948135)
  ·
    refine ⟨46740290749335477592422203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31160193832890318394948135 46740290749335477592422203)
    ·
      refine ⟨70110436124003216388633305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46740290749335477592422203 70110436124003216388633305)
      ·
        refine ⟨52582827093002412291474979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70110436124003216388633305 52582827093002412291474979)
        ·
          refine ⟨78874240639503618437212469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52582827093002412291474979 78874240639503618437212469)
          ·
            refine ⟨7394460059953464228488669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78874240639503618437212469 7394460059953464228488669)
            ·
              refine ⟨2772922522482549085683251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7394460059953464228488669 2772922522482549085683251)
              ·
                refine ⟨4159383783723823628524877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2772922522482549085683251 4159383783723823628524877)
                ·
                  refine ⟨1559768918896433860696829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4159383783723823628524877 1559768918896433860696829)
                  ·
                    refine ⟨584913344586162697761311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1559768918896433860696829 584913344586162697761311)
                    ·
                      rfl

theorem cell22_1708672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 3, 3].length) (baseStart_1708672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1708672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1708672 prefixEnd_1708672 := by exact prefixLift 1708672
  have htrace : WordTrace (prefixWord ++ tailWord_1708672) baseStart_1708672 baseEnd_1708672 := by
    simpa [prefixWord, tailWord_1708672, baseEnd_1708672] using wordTrace_append hprefix tailTrace_1708672
  have hstable : (prefixWord ++ tailWord_1708672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708672).length < 2 ^ (prefixWord ++ tailWord_1708672).sum := by decide
  have hdescent : baseEnd_1708672 < baseStart_1708672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708730 : List Nat := [3, 1, 1, 1, 2, 3, 2, 3, 6]
def baseStart_1708730 : Nat := 118140960795 + 1708730 * 2 ^ 59
def prefixEnd_1708730 : Nat := 4983230072969 + 3 ^ 40 * 1708730 * 2
def baseEnd_1708730 : Nat := 194977733057156626603711

theorem tailTrace_1708730 : CollatzResearch.WordTrace tailWord_1708730 prefixEnd_1708730 194977733057156626603711 := by
  unfold tailWord_1708730
  simp only [CollatzResearch.WordTrace]
  refine ⟨15580625774892628173876911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41548335399713675130338429 15580625774892628173876911)
  ·
    refine ⟨23370938662338942260815367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15580625774892628173876911 23370938662338942260815367)
    ·
      refine ⟨35056407993508413391223051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23370938662338942260815367 35056407993508413391223051)
      ·
        refine ⟨52584611990262620086834577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35056407993508413391223051 52584611990262620086834577)
        ·
          refine ⟨39438458992696965065125933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52584611990262620086834577 39438458992696965065125933)
          ·
            refine ⟨14789422122261361899422225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39438458992696965065125933 14789422122261361899422225)
            ·
              refine ⟨11092066591696021424566669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14789422122261361899422225 11092066591696021424566669)
              ·
                refine ⟨4159524971886008034212501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11092066591696021424566669 4159524971886008034212501)
                ·
                  refine ⟨194977733057156626603711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4159524971886008034212501 194977733057156626603711)
                  ·
                    rfl

theorem cell22_1708730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_1708730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1708730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1708730 prefixEnd_1708730 := by exact prefixLift 1708730
  have htrace : WordTrace (prefixWord ++ tailWord_1708730) baseStart_1708730 baseEnd_1708730 := by
    simpa [prefixWord, tailWord_1708730, baseEnd_1708730] using wordTrace_append hprefix tailTrace_1708730
  have hstable : (prefixWord ++ tailWord_1708730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708730).length < 2 ^ (prefixWord ++ tailWord_1708730).sum := by decide
  have hdescent : baseEnd_1708730 < baseStart_1708730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708762 : List Nat := [3, 1, 1, 2, 2, 2, 2, 2, 4, 3]
def baseStart_1708762 : Nat := 118140960795 + 1708762 * 2 ^ 59
def prefixEnd_1708762 : Nat := 4983230072969 + 3 ^ 40 * 1708762 * 2
def baseEnd_1708762 : Nat := 584944153425432463011035

theorem tailTrace_1708762 : CollatzResearch.WordTrace tailWord_1708762 prefixEnd_1708762 584944153425432463011035 := by
  unfold tailWord_1708762
  simp only [CollatzResearch.WordTrace]
  refine ⟨15580917558863645540168135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41549113490303054773781693 15580917558863645540168135)
  ·
    refine ⟨23371376338295468310252203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15580917558863645540168135 23371376338295468310252203)
    ·
      refine ⟨35057064507443202465378305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23371376338295468310252203 35057064507443202465378305)
      ·
        refine ⟨26292798380582401849033729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35057064507443202465378305 26292798380582401849033729)
        ·
          refine ⟨19719598785436801386775297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26292798380582401849033729 19719598785436801386775297)
          ·
            refine ⟨14789699089077601040081473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19719598785436801386775297 14789699089077601040081473)
            ·
              refine ⟨11092274316808200780061105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14789699089077601040081473 11092274316808200780061105)
              ·
                refine ⟨8319205737606150585045829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11092274316808200780061105 8319205737606150585045829)
                ·
                  refine ⟨1559851075801153234696093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8319205737606150585045829 1559851075801153234696093)
                  ·
                    refine ⟨584944153425432463011035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1559851075801153234696093 584944153425432463011035)
                    ·
                      rfl

theorem cell22_1708762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 4, 3].length) (baseStart_1708762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1708762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1708762 prefixEnd_1708762 := by exact prefixLift 1708762
  have htrace : WordTrace (prefixWord ++ tailWord_1708762) baseStart_1708762 baseEnd_1708762 := by
    simpa [prefixWord, tailWord_1708762, baseEnd_1708762] using wordTrace_append hprefix tailTrace_1708762
  have hstable : (prefixWord ++ tailWord_1708762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708762).length < 2 ^ (prefixWord ++ tailWord_1708762).sum := by decide
  have hdescent : baseEnd_1708762 < baseStart_1708762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708796 : List Nat := [2, 2, 2, 1, 3, 3, 3, 1, 2, 3]
def baseStart_1708796 : Nat := 118140960795 + 1708796 * 2 ^ 59
def prefixEnd_1708796 : Nat := 4983230072969 + 3 ^ 40 * 1708796 * 2
def baseEnd_1708796 : Nat := 584955792320267707660931

theorem tailTrace_1708796 : CollatzResearch.WordTrace tailWord_1708796 prefixEnd_1708796 584955792320267707660931 := by
  unfold tailWord_1708796
  simp only [CollatzResearch.WordTrace]
  refine ⟨31162455158665702983705121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41549940211554270644940161 31162455158665702983705121)
  ·
    refine ⟨23371841368999277237778841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31162455158665702983705121 23371841368999277237778841)
    ·
      refine ⟨17528881026749457928334131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23371841368999277237778841 17528881026749457928334131)
      ·
        refine ⟨26293321540124186892501197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17528881026749457928334131 26293321540124186892501197)
        ·
          refine ⟨9859995577546570084687949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26293321540124186892501197 9859995577546570084687949)
          ·
            refine ⟨3697498341579963781757981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9859995577546570084687949 3697498341579963781757981)
            ·
              refine ⟨1386561878092486418159243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3697498341579963781757981 1386561878092486418159243)
              ·
                refine ⟨2079842817138729627238865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1386561878092486418159243 2079842817138729627238865)
                ·
                  refine ⟨1559882112854047220429149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2079842817138729627238865 1559882112854047220429149)
                  ·
                    refine ⟨584955792320267707660931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1559882112854047220429149 584955792320267707660931)
                    ·
                      rfl

theorem cell22_1708796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_1708796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1708796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1708796 prefixEnd_1708796 := by exact prefixLift 1708796
  have htrace : WordTrace (prefixWord ++ tailWord_1708796) baseStart_1708796 baseEnd_1708796 := by
    simpa [prefixWord, tailWord_1708796, baseEnd_1708796] using wordTrace_append hprefix tailTrace_1708796
  have hstable : (prefixWord ++ tailWord_1708796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708796).length < 2 ^ (prefixWord ++ tailWord_1708796).sum := by decide
  have hdescent : baseEnd_1708796 < baseStart_1708796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708805 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 2, 6]
def baseStart_1708805 : Nat := 118140960795 + 1708805 * 2 ^ 59
def prefixEnd_1708805 : Nat := 4983230072969 + 3 ^ 40 * 1708805 * 2
def baseEnd_1708805 : Nat := 584958873204194684185903

theorem tailTrace_1708805 : CollatzResearch.WordTrace tailWord_1708805 prefixEnd_1708805 584958873204194684185903 := by
  unfold tailWord_1708805
  simp only [CollatzResearch.WordTrace]
  refine ⟨62325238574298800504487869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41550159049532533669658579 62325238574298800504487869)
  ·
    refine ⟨23371964465362050189182951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62325238574298800504487869 23371964465362050189182951)
    ·
      refine ⟨35057946698043075283774427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23371964465362050189182951 35057946698043075283774427)
      ·
        refine ⟨52586920047064612925661641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35057946698043075283774427 52586920047064612925661641)
        ·
          refine ⟨39440190035298459694246231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52586920047064612925661641 39440190035298459694246231)
          ·
            refine ⟨59160285052947689541369347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39440190035298459694246231 59160285052947689541369347)
            ·
              refine ⟨88740427579421534312054021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59160285052947689541369347 88740427579421534312054021)
              ·
                refine ⟨16638830171141537683510129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88740427579421534312054021 16638830171141537683510129)
                ·
                  refine ⟨12479122628356153262632597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16638830171141537683510129 12479122628356153262632597)
                  ·
                    refine ⟨584958873204194684185903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12479122628356153262632597 584958873204194684185903)
                    ·
                      rfl

theorem cell22_1708805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_1708805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1708805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1708805 prefixEnd_1708805 := by exact prefixLift 1708805
  have htrace : WordTrace (prefixWord ++ tailWord_1708805) baseStart_1708805 baseEnd_1708805 := by
    simpa [prefixWord, tailWord_1708805, baseEnd_1708805] using wordTrace_append hprefix tailTrace_1708805
  have hstable : (prefixWord ++ tailWord_1708805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708805).length < 2 ^ (prefixWord ++ tailWord_1708805).sum := by decide
  have hdescent : baseEnd_1708805 < baseStart_1708805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708837 : List Nat := [1, 3, 1, 2, 3, 1, 2, 4, 5]
def baseStart_1708837 : Nat := 118140960795 + 1708837 * 2 ^ 59
def prefixEnd_1708837 : Nat := 4983230072969 + 3 ^ 40 * 1708837 * 2
def baseEnd_1708837 : Nat := 194989942486052422461935

theorem tailTrace_1708837 : CollatzResearch.WordTrace tailWord_1708837 prefixEnd_1708837 194989942486052422461935 := by
  unfold tailWord_1708837
  simp only [CollatzResearch.WordTrace]
  refine ⟨62326405710182869969652765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41550937140121913313101843 62326405710182869969652765)
  ·
    refine ⟨23372402141318576238619787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62326405710182869969652765 23372402141318576238619787)
    ·
      refine ⟨35058603211977864357929681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23372402141318576238619787 35058603211977864357929681)
      ·
        refine ⟨26293952408983398268447261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35058603211977864357929681 26293952408983398268447261)
        ·
          refine ⟨9860232153368774350667723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26293952408983398268447261 9860232153368774350667723)
          ·
            refine ⟨14790348230053161526001585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9860232153368774350667723 14790348230053161526001585)
            ·
              refine ⟨11092761172539871144501189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14790348230053161526001585 11092761172539871144501189)
              ·
                refine ⟨2079892719851225839593973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11092761172539871144501189 2079892719851225839593973)
                ·
                  refine ⟨194989942486052422461935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2079892719851225839593973 194989942486052422461935)
                  ·
                    rfl

theorem cell22_1708837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 5].length) (baseStart_1708837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1708837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1708837 prefixEnd_1708837 := by exact prefixLift 1708837
  have htrace : WordTrace (prefixWord ++ tailWord_1708837) baseStart_1708837 baseEnd_1708837 := by
    simpa [prefixWord, tailWord_1708837, baseEnd_1708837] using wordTrace_append hprefix tailTrace_1708837
  have hstable : (prefixWord ++ tailWord_1708837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708837).length < 2 ^ (prefixWord ++ tailWord_1708837).sum := by decide
  have hdescent : baseEnd_1708837 < baseStart_1708837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708867 : List Nat := [1, 1, 1, 3, 1, 4, 3, 1, 3, 4]
def baseStart_1708867 : Nat := 118140960795 + 1708867 * 2 ^ 59
def prefixEnd_1708867 : Nat := 4983230072969 + 3 ^ 40 * 1708867 * 2
def baseEnd_1708867 : Nat := 584980097071247189135713

theorem tailTrace_1708867 : CollatzResearch.WordTrace tailWord_1708867 prefixEnd_1708867 584980097071247189135713 := by
  unfold tailWord_1708867
  simp only [CollatzResearch.WordTrace]
  refine ⟨62327499900074185093244855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41551666600049456728829903 62327499900074185093244855)
  ·
    refine ⟨93491249850111277639867283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62327499900074185093244855 93491249850111277639867283)
    ·
      refine ⟨140236874775166916459800925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93491249850111277639867283 140236874775166916459800925)
      ·
        refine ⟨52588828040687593672425347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140236874775166916459800925 52588828040687593672425347)
        ·
          refine ⟨78883242061031390508638021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52588828040687593672425347 78883242061031390508638021)
          ·
            refine ⟨14790607886443385720369629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78883242061031390508638021 14790607886443385720369629)
            ·
              refine ⟨5546477957416269645138611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14790607886443385720369629 5546477957416269645138611)
              ·
                refine ⟨8319716936124404467707917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5546477957416269645138611 8319716936124404467707917)
                ·
                  refine ⟨3119893851046651675390469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8319716936124404467707917 3119893851046651675390469)
                  ·
                    refine ⟨584980097071247189135713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3119893851046651675390469 584980097071247189135713)
                    ·
                      rfl

theorem cell22_1708867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 4].length) (baseStart_1708867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1708867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1708867 prefixEnd_1708867 := by exact prefixLift 1708867
  have htrace : WordTrace (prefixWord ++ tailWord_1708867) baseStart_1708867 baseEnd_1708867 := by
    simpa [prefixWord, tailWord_1708867, baseEnd_1708867] using wordTrace_append hprefix tailTrace_1708867
  have hstable : (prefixWord ++ tailWord_1708867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708867).length < 2 ^ (prefixWord ++ tailWord_1708867).sum := by decide
  have hdescent : baseEnd_1708867 < baseStart_1708867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708912 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 4, 4]
def baseStart_1708912 : Nat := 118140960795 + 1708912 * 2 ^ 59
def prefixEnd_1708912 : Nat := 4983230072969 + 3 ^ 40 * 1708912 * 2
def baseEnd_1708912 : Nat := 584995501490882071760575

theorem tailTrace_1708912 : CollatzResearch.WordTrace tailWord_1708912 prefixEnd_1708912 584995501490882071760575 := by
  unfold tailWord_1708912
  simp only [CollatzResearch.WordTrace]
  refine ⟨31164570592455578889316495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41552760789940771852421993 31164570592455578889316495)
  ·
    refine ⟨46746855888683368333974743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31164570592455578889316495 46746855888683368333974743)
    ·
      refine ⟨70120283833025052500962115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46746855888683368333974743 70120283833025052500962115)
      ·
        refine ⟨105180425749537578751443173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70120283833025052500962115 105180425749537578751443173)
        ·
          refine ⟨19721329828038296015895595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105180425749537578751443173 19721329828038296015895595)
          ·
            refine ⟨29581994742057444023843393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19721329828038296015895595 29581994742057444023843393)
            ·
              refine ⟨22186496056543083017882545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29581994742057444023843393 22186496056543083017882545)
              ·
                refine ⟨16639872042407312263411909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22186496056543083017882545 16639872042407312263411909)
                ·
                  refine ⟨3119976007951371049389733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16639872042407312263411909 3119976007951371049389733)
                  ·
                    refine ⟨584995501490882071760575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3119976007951371049389733 584995501490882071760575)
                    ·
                      rfl

theorem cell22_1708912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 4, 4].length) (baseStart_1708912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1708912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1708912 prefixEnd_1708912 := by exact prefixLift 1708912
  have htrace : WordTrace (prefixWord ++ tailWord_1708912) baseStart_1708912 baseEnd_1708912 := by
    simpa [prefixWord, tailWord_1708912, baseEnd_1708912] using wordTrace_append hprefix tailTrace_1708912
  have hstable : (prefixWord ++ tailWord_1708912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708912).length < 2 ^ (prefixWord ++ tailWord_1708912).sum := by decide
  have hdescent : baseEnd_1708912 < baseStart_1708912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708950 : List Nat := [5, 3, 1, 1, 1, 1, 2, 4, 4]
def baseStart_1708950 : Nat := 118140960795 + 1708950 * 2 ^ 59
def prefixEnd_1708950 : Nat := 4983230072969 + 3 ^ 40 * 1708950 * 2
def baseEnd_1708950 : Nat := 195002836555820879770153

theorem tailTrace_1708950 : CollatzResearch.WordTrace tailWord_1708950 prefixEnd_1708950 195002836555820879770153 := by
  unfold tailWord_1708950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3895657947423343141782269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41553684772515660179010869 3895657947423343141782269)
  ·
    refine ⟨1460871730283753678168351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3895657947423343141782269 1460871730283753678168351)
    ·
      refine ⟨2191307595425630517252527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1460871730283753678168351 2191307595425630517252527)
      ·
        refine ⟨3286961393138445775878791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2191307595425630517252527 3286961393138445775878791)
        ·
          refine ⟨4930442089707668663818187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3286961393138445775878791 4930442089707668663818187)
          ·
            refine ⟨7395663134561502995727281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4930442089707668663818187 7395663134561502995727281)
            ·
              refine ⟨5546747350921127246795461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7395663134561502995727281 5546747350921127246795461)
              ·
                refine ⟨1040015128297711358774149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5546747350921127246795461 1040015128297711358774149)
                ·
                  refine ⟨195002836555820879770153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1040015128297711358774149 195002836555820879770153)
                  ·
                    rfl

theorem cell22_1708950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_1708950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1708950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1708950 prefixEnd_1708950 := by exact prefixLift 1708950
  have htrace : WordTrace (prefixWord ++ tailWord_1708950) baseStart_1708950 baseEnd_1708950 := by
    simpa [prefixWord, tailWord_1708950, baseEnd_1708950] using wordTrace_append hprefix tailTrace_1708950
  have hstable : (prefixWord ++ tailWord_1708950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708950).length < 2 ^ (prefixWord ++ tailWord_1708950).sum := by decide
  have hdescent : baseEnd_1708950 < baseStart_1708950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709023 : List Nat := [1, 1, 2, 3, 5, 2, 2, 1, 5]
def baseStart_1709023 : Nat := 118140960795 + 1709023 * 2 ^ 59
def prefixEnd_1709023 : Nat := 4983230072969 + 3 ^ 40 * 1709023 * 2
def baseEnd_1709023 : Nat := 195011166353104927411745

theorem tailTrace_1709023 : CollatzResearch.WordTrace tailWord_1709023 prefixEnd_1709023 195011166353104927411745 := by
  unfold tailWord_1709023
  simp only [CollatzResearch.WordTrace]
  refine ⟨62333189687509023735923723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41555459791672682490615815 62333189687509023735923723)
  ·
    refine ⟨93499784531263535603885585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62333189687509023735923723 93499784531263535603885585)
    ·
      refine ⟨70124838398447651702914189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93499784531263535603885585 70124838398447651702914189)
      ·
        refine ⟨26296814399417869388592821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70124838398447651702914189 26296814399417869388592821)
        ·
          refine ⟨2465326349945425255180577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26296814399417869388592821 2465326349945425255180577)
          ·
            refine ⟨1848994762459068941385433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2465326349945425255180577 1848994762459068941385433)
            ·
              refine ⟨1386746071844301706039075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1848994762459068941385433 1386746071844301706039075)
              ·
                refine ⟨2080119107766452559058613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1386746071844301706039075 2080119107766452559058613)
                ·
                  refine ⟨195011166353104927411745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2080119107766452559058613 195011166353104927411745)
                  ·
                    rfl

theorem cell22_1709023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 5].length) (baseStart_1709023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709023 prefixEnd_1709023 := by exact prefixLift 1709023
  have htrace : WordTrace (prefixWord ++ tailWord_1709023) baseStart_1709023 baseEnd_1709023 := by
    simpa [prefixWord, tailWord_1709023, baseEnd_1709023] using wordTrace_append hprefix tailTrace_1709023
  have hstable : (prefixWord ++ tailWord_1709023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709023).length < 2 ^ (prefixWord ++ tailWord_1709023).sum := by decide
  have hdescent : baseEnd_1709023 < baseStart_1709023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709049 : List Nat := [1, 2, 1, 3, 1, 3, 3, 2, 1, 5]
def baseStart_1709049 : Nat := 118140960795 + 1709049 * 2 ^ 59
def prefixEnd_1709049 : Nat := 4983230072969 + 3 ^ 40 * 1709049 * 2
def baseEnd_1709049 : Nat := 585042399390659381085155

theorem tailTrace_1709049 : CollatzResearch.WordTrace tailWord_1709049 prefixEnd_1709049 585042399390659381085155 := by
  unfold tailWord_1709049
  simp only [CollatzResearch.WordTrace]
  refine ⟨62334137985414830176370201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41556091990276553450913467 62334137985414830176370201)
  ·
    refine ⟨46750603489061122632277651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62334137985414830176370201 46750603489061122632277651)
    ·
      refine ⟨70125905233591683948416477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46750603489061122632277651 70125905233591683948416477)
      ·
        refine ⟨26297214462596881480656179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70125905233591683948416477 26297214462596881480656179)
        ·
          refine ⟨39445821693895322220984269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26297214462596881480656179 39445821693895322220984269)
          ·
            refine ⟨14792183135210745832869101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39445821693895322220984269 14792183135210745832869101)
            ·
              refine ⟨5547068675704029687325913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14792183135210745832869101 5547068675704029687325913)
              ·
                refine ⟨4160301506778022265494435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5547068675704029687325913 4160301506778022265494435)
                ·
                  refine ⟨6240452260167033398241653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4160301506778022265494435 6240452260167033398241653)
                  ·
                    refine ⟨585042399390659381085155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6240452260167033398241653 585042399390659381085155)
                    ·
                      rfl

theorem cell22_1709049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 5].length) (baseStart_1709049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709049 prefixEnd_1709049 := by exact prefixLift 1709049
  have htrace : WordTrace (prefixWord ++ tailWord_1709049) baseStart_1709049 baseEnd_1709049 := by
    simpa [prefixWord, tailWord_1709049, baseEnd_1709049] using wordTrace_append hprefix tailTrace_1709049
  have hstable : (prefixWord ++ tailWord_1709049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709049).length < 2 ^ (prefixWord ++ tailWord_1709049).sum := by decide
  have hdescent : baseEnd_1709049 < baseStart_1709049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709068 : List Nat := [2, 2, 1, 2, 3, 2, 4, 2, 4]
def baseStart_1709068 : Nat := 118140960795 + 1709068 * 2 ^ 59
def prefixEnd_1709068 : Nat := 4983230072969 + 3 ^ 40 * 1709068 * 2
def baseEnd_1709068 : Nat := 195016301159649888286699

theorem tailTrace_1709068 : CollatzResearch.WordTrace tailWord_1709068 prefixEnd_1709068 195016301159649888286699 := by
  unfold tailWord_1709068
  simp only [CollatzResearch.WordTrace]
  refine ⟨31167415486172998210655929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41556553981563997614207905 31167415486172998210655929)
  ·
    refine ⟨23375561614629748657991947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31167415486172998210655929 23375561614629748657991947)
    ·
      refine ⟨35063342421944622986987921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23375561614629748657991947 35063342421944622986987921)
      ·
        refine ⟨26297506816458467240240941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35063342421944622986987921 26297506816458467240240941)
        ·
          refine ⟨9861565056171925215090353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26297506816458467240240941 9861565056171925215090353)
          ·
            refine ⟨7396173792128943911317765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9861565056171925215090353 7396173792128943911317765)
            ·
              refine ⟨1386782586024176983372081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7396173792128943911317765 1386782586024176983372081)
              ·
                refine ⟨1040086939518132737529061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1386782586024176983372081 1040086939518132737529061)
                ·
                  refine ⟨195016301159649888286699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1040086939518132737529061 195016301159649888286699)
                  ·
                    rfl

theorem cell22_1709068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 4].length) (baseStart_1709068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709068 prefixEnd_1709068 := by exact prefixLift 1709068
  have htrace : WordTrace (prefixWord ++ tailWord_1709068) baseStart_1709068 baseEnd_1709068 := by
    simpa [prefixWord, tailWord_1709068, baseEnd_1709068] using wordTrace_append hprefix tailTrace_1709068
  have hstable : (prefixWord ++ tailWord_1709068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709068).length < 2 ^ (prefixWord ++ tailWord_1709068).sum := by decide
  have hdescent : baseEnd_1709068 < baseStart_1709068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709128 : List Nat := [2, 1, 3, 1, 1, 1, 3, 6, 1, 3]
def baseStart_1709128 : Nat := 118140960795 + 1709128 * 2 ^ 59
def prefixEnd_1709128 : Nat := 4983230072969 + 3 ^ 40 * 1709128 * 2
def baseEnd_1709128 : Nat := 585069442705129508359913

theorem tailTrace_1709128 : CollatzResearch.WordTrace tailWord_1709128 prefixEnd_1709128 585069442705129508359913 := by
  unfold tailWord_1709128
  simp only [CollatzResearch.WordTrace]
  refine ⟨31168509676064313334248019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41558012901419084445664025 31168509676064313334248019)
  ·
    refine ⟨46752764514096470001372029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31168509676064313334248019 46752764514096470001372029)
    ·
      refine ⟨17532286692786176250514511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46752764514096470001372029 17532286692786176250514511)
      ·
        refine ⟨26298430039179264375771767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17532286692786176250514511 26298430039179264375771767)
        ·
          refine ⟨39447645058768896563657651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26298430039179264375771767 39447645058768896563657651)
          ·
            refine ⟨59171467588153344845486477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39447645058768896563657651 59171467588153344845486477)
            ·
              refine ⟨22189300345557504317057429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59171467588153344845486477 22189300345557504317057429)
              ·
                refine ⟨1040123453698008014862067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22189300345557504317057429 1040123453698008014862067)
                ·
                  refine ⟨1560185180547012022293101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1040123453698008014862067 1560185180547012022293101)
                  ·
                    refine ⟨585069442705129508359913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1560185180547012022293101 585069442705129508359913)
                    ·
                      rfl

theorem cell22_1709128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_1709128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709128 prefixEnd_1709128 := by exact prefixLift 1709128
  have htrace : WordTrace (prefixWord ++ tailWord_1709128) baseStart_1709128 baseEnd_1709128 := by
    simpa [prefixWord, tailWord_1709128, baseEnd_1709128] using wordTrace_append hprefix tailTrace_1709128
  have hstable : (prefixWord ++ tailWord_1709128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709128).length < 2 ^ (prefixWord ++ tailWord_1709128).sum := by decide
  have hdescent : baseEnd_1709128 < baseStart_1709128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709162 : List Nat := [3, 1, 3, 2, 2, 3, 1, 3, 1, 3]
def baseStart_1709162 : Nat := 118140960795 + 1709162 * 2 ^ 59
def prefixEnd_1709162 : Nat := 4983230072969 + 3 ^ 40 * 1709162 * 2
def baseEnd_1709162 : Nat := 585081081599964753009809

theorem tailTrace_1709162 : CollatzResearch.WordTrace tailWord_1709162 prefixEnd_1709162 585081081599964753009809 := by
  unfold tailWord_1709162
  simp only [CollatzResearch.WordTrace]
  refine ⟨15584564858501362618808435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41558839622670300316822493 15584564858501362618808435)
  ·
    refine ⟨23376847287752043928212653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15584564858501362618808435 23376847287752043928212653)
    ·
      refine ⟨8766317732907016473079745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23376847287752043928212653 8766317732907016473079745)
      ·
        refine ⟨6574738299680262354809809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8766317732907016473079745 6574738299680262354809809)
        ·
          refine ⟨4931053724760196766107357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6574738299680262354809809 4931053724760196766107357)
          ·
            refine ⟨1849145146785073787290259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4931053724760196766107357 1849145146785073787290259)
            ·
              refine ⟨2773717720177610680935389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1849145146785073787290259 2773717720177610680935389)
              ·
                refine ⟨1040144145066604005350771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2773717720177610680935389 1040144145066604005350771)
                ·
                  refine ⟨1560216217599906008026157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1040144145066604005350771 1560216217599906008026157)
                  ·
                    refine ⟨585081081599964753009809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1560216217599906008026157 585081081599964753009809)
                    ·
                      rfl

theorem cell22_1709162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_1709162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709162 prefixEnd_1709162 := by exact prefixLift 1709162
  have htrace : WordTrace (prefixWord ++ tailWord_1709162) baseStart_1709162 baseEnd_1709162 := by
    simpa [prefixWord, tailWord_1709162, baseEnd_1709162] using wordTrace_append hprefix tailTrace_1709162
  have hstable : (prefixWord ++ tailWord_1709162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709162).length < 2 ^ (prefixWord ++ tailWord_1709162).sum := by decide
  have hdescent : baseEnd_1709162 < baseStart_1709162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709192 : List Nat := [2, 1, 3, 4, 3, 1, 2, 1, 5]
def baseStart_1709192 : Nat := 118140960795 + 1709192 * 2 ^ 59
def prefixEnd_1709192 : Nat := 4983230072969 + 3 ^ 40 * 1709192 * 2
def baseEnd_1709192 : Nat := 195030450404351558253239

theorem tailTrace_1709192 : CollatzResearch.WordTrace tailWord_1709192 prefixEnd_1709192 195030450404351558253239 := by
  unfold tailWord_1709192
  simp only [CollatzResearch.WordTrace]
  refine ⟨31169676811948382799412915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41559569082597843732550553 31169676811948382799412915)
  ·
    refine ⟨46754515217922574199119373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31169676811948382799412915 46754515217922574199119373)
    ·
      refine ⟨17532943206720965324669765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46754515217922574199119373 17532943206720965324669765)
      ·
        refine ⟨3287426851260180998375581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17532943206720965324669765 3287426851260180998375581)
        ·
          refine ⟨1232785069222567874390843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3287426851260180998375581 1232785069222567874390843)
          ·
            refine ⟨1849177603833851811586265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1232785069222567874390843 1849177603833851811586265)
            ·
              refine ⟨1386883202875388858689699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1849177603833851811586265 1386883202875388858689699)
              ·
                refine ⟨2080324804313083288034549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1386883202875388858689699 2080324804313083288034549)
                ·
                  refine ⟨195030450404351558253239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2080324804313083288034549 195030450404351558253239)
                  ·
                    rfl

theorem cell22_1709192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 5].length) (baseStart_1709192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709192 prefixEnd_1709192 := by exact prefixLift 1709192
  have htrace : WordTrace (prefixWord ++ tailWord_1709192) baseStart_1709192 baseEnd_1709192 := by
    simpa [prefixWord, tailWord_1709192, baseEnd_1709192] using wordTrace_append hprefix tailTrace_1709192
  have hstable : (prefixWord ++ tailWord_1709192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709192).length < 2 ^ (prefixWord ++ tailWord_1709192).sum := by decide
  have hdescent : baseEnd_1709192 < baseStart_1709192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709233 : List Nat := [1, 2, 2, 5, 1, 1, 2, 2, 2, 4]
def baseStart_1709233 : Nat := 118140960795 + 1709233 * 2 ^ 59
def prefixEnd_1709233 : Nat := 4983230072969 + 3 ^ 40 * 1709233 * 2
def baseEnd_1709233 : Nat := 585105386350944234484591

theorem tailTrace_1709233 : CollatzResearch.WordTrace tailWord_1709233 prefixEnd_1709233 585105386350944234484591 := by
  unfold tailWord_1709233
  simp only [CollatzResearch.WordTrace]
  refine ⟨62340849016748229601068353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41560566011165486400712235 62340849016748229601068353)
  ·
    refine ⟨46755636762561172200801265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62340849016748229601068353 46755636762561172200801265)
    ·
      refine ⟨35066727571920879150600949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46755636762561172200801265 35066727571920879150600949)
      ·
        refine ⟨3287505709867582420368839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35066727571920879150600949 3287505709867582420368839)
        ·
          refine ⟨4931258564801373630553259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3287505709867582420368839 4931258564801373630553259)
          ·
            refine ⟨7396887847202060445829889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4931258564801373630553259 7396887847202060445829889)
            ·
              refine ⟨5547665885401545334372417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7396887847202060445829889 5547665885401545334372417)
              ·
                refine ⟨4160749414051159000779313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5547665885401545334372417 4160749414051159000779313)
                ·
                  refine ⟨3120562060538369250584485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4160749414051159000779313 3120562060538369250584485)
                  ·
                    refine ⟨585105386350944234484591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3120562060538369250584485 585105386350944234484591)
                    ·
                      rfl

theorem cell22_1709233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_1709233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709233 prefixEnd_1709233 := by exact prefixLift 1709233
  have htrace : WordTrace (prefixWord ++ tailWord_1709233) baseStart_1709233 baseEnd_1709233 := by
    simpa [prefixWord, tailWord_1709233, baseEnd_1709233] using wordTrace_append hprefix tailTrace_1709233
  have hstable : (prefixWord ++ tailWord_1709233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709233).length < 2 ^ (prefixWord ++ tailWord_1709233).sum := by decide
  have hdescent : baseEnd_1709233 < baseStart_1709233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709248 : List Nat := [2, 1, 1, 2, 6, 2, 1, 7]
def baseStart_1709248 : Nat := 118140960795 + 1709248 * 2 ^ 59
def prefixEnd_1709248 : Nat := 4983230072969 + 3 ^ 40 * 1709248 * 2
def baseEnd_1709248 : Nat := 65012280128609910595505

theorem tailTrace_1709248 : CollatzResearch.WordTrace tailWord_1709248 prefixEnd_1709248 65012280128609910595505 := by
  unfold tailWord_1709248
  simp only [CollatzResearch.WordTrace]
  refine ⟨31170698055846943581432199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41560930741129258108576265 31170698055846943581432199)
  ·
    refine ⟨46756047083770415372148299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31170698055846943581432199 46756047083770415372148299)
    ·
      refine ⟨70134070625655623058222449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46756047083770415372148299 70134070625655623058222449)
      ·
        refine ⟨52600552969241717293666837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70134070625655623058222449 52600552969241717293666837)
        ·
          refine ⟨2465650920433205498140633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52600552969241717293666837 2465650920433205498140633)
          ·
            refine ⟨1849238190324904123605475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2465650920433205498140633 1849238190324904123605475)
            ·
              refine ⟨2773857285487356185408213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1849238190324904123605475 2773857285487356185408213)
              ·
                refine ⟨65012280128609910595505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2773857285487356185408213 65012280128609910595505)
                ·
                  rfl

theorem cell22_1709248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 7].length) (baseStart_1709248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709248 prefixEnd_1709248 := by exact prefixLift 1709248
  have htrace : WordTrace (prefixWord ++ tailWord_1709248) baseStart_1709248 baseEnd_1709248 := by
    simpa [prefixWord, tailWord_1709248, baseEnd_1709248] using wordTrace_append hprefix tailTrace_1709248
  have hstable : (prefixWord ++ tailWord_1709248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709248).length < 2 ^ (prefixWord ++ tailWord_1709248).sum := by decide
  have hdescent : baseEnd_1709248 < baseStart_1709248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709280 : List Nat := [2, 1, 1, 3, 1, 4, 1, 5, 1, 3]
def baseStart_1709280 : Nat := 118140960795 + 1709280 * 2 ^ 59
def prefixEnd_1709280 : Nat := 4983230072969 + 3 ^ 40 * 1709280 * 2
def baseEnd_1709280 : Nat := 585121475411451778559447

theorem tailTrace_1709280 : CollatzResearch.WordTrace tailWord_1709280 prefixEnd_1709280 585121475411451778559447 := by
  unfold tailWord_1709280
  simp only [CollatzResearch.WordTrace]
  refine ⟨31171281623788978314014647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41561708831718637752019529 31171281623788978314014647)
  ·
    refine ⟨46756922435683467471021971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31171281623788978314014647 46756922435683467471021971)
    ·
      refine ⟨70135383653525201206532957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46756922435683467471021971 70135383653525201206532957)
      ·
        refine ⟨26300768870071950452449859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70135383653525201206532957 26300768870071950452449859)
        ·
          refine ⟨39451153305107925678674789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26300768870071950452449859 39451153305107925678674789)
          ·
            refine ⟨7397091244707736064751523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39451153305107925678674789 7397091244707736064751523)
            ·
              refine ⟨11095636867061604097127285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7397091244707736064751523 11095636867061604097127285)
              ·
                refine ⟨1040215956287025384105683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11095636867061604097127285 1040215956287025384105683)
                ·
                  refine ⟨1560323934430538076158525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1040215956287025384105683 1560323934430538076158525)
                  ·
                    refine ⟨585121475411451778559447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1560323934430538076158525 585121475411451778559447)
                    ·
                      rfl

theorem cell22_1709280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 1, 3].length) (baseStart_1709280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709280 prefixEnd_1709280 := by exact prefixLift 1709280
  have htrace : WordTrace (prefixWord ++ tailWord_1709280) baseStart_1709280 baseEnd_1709280 := by
    simpa [prefixWord, tailWord_1709280, baseEnd_1709280] using wordTrace_append hprefix tailTrace_1709280
  have hstable : (prefixWord ++ tailWord_1709280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709280).length < 2 ^ (prefixWord ++ tailWord_1709280).sum := by decide
  have hdescent : baseEnd_1709280 < baseStart_1709280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709291 : List Nat := [1, 1, 1, 1, 2, 6, 1, 2, 2, 5]
def baseStart_1709291 : Nat := 118140960795 + 1709291 * 2 ^ 59
def prefixEnd_1709291 : Nat := 4983230072969 + 3 ^ 40 * 1709291 * 2
def baseEnd_1709291 : Nat := 585125240936251416534413

theorem tailTrace_1709291 : CollatzResearch.WordTrace tailWord_1709291 prefixEnd_1709291 585125240936251416534413 := by
  unfold tailWord_1709291
  simp only [CollatzResearch.WordTrace]
  refine ⟨62342964450538105506679727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41561976300358737004453151 62342964450538105506679727)
  ·
    refine ⟨93514446675807158260019591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62342964450538105506679727 93514446675807158260019591)
    ·
      refine ⟨140271670013710737390029387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93514446675807158260019591 140271670013710737390029387)
      ·
        refine ⟨210407505020566106085044081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140271670013710737390029387 210407505020566106085044081)
        ·
          refine ⟨157805628765424579563783061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210407505020566106085044081 157805628765424579563783061)
          ·
            refine ⟨7397138848379277167052331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 157805628765424579563783061 7397138848379277167052331)
            ·
              refine ⟨11095708272568915750578497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7397138848379277167052331 11095708272568915750578497)
              ·
                refine ⟨8321781204426686812933873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11095708272568915750578497 8321781204426686812933873)
                ·
                  refine ⟨6241335903320015109700405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8321781204426686812933873 6241335903320015109700405)
                  ·
                    refine ⟨585125240936251416534413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6241335903320015109700405 585125240936251416534413)
                    ·
                      rfl

theorem cell22_1709291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 5].length) (baseStart_1709291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709291 prefixEnd_1709291 := by exact prefixLift 1709291
  have htrace : WordTrace (prefixWord ++ tailWord_1709291) baseStart_1709291 baseEnd_1709291 := by
    simpa [prefixWord, tailWord_1709291, baseEnd_1709291] using wordTrace_append hprefix tailTrace_1709291
  have hstable : (prefixWord ++ tailWord_1709291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709291).length < 2 ^ (prefixWord ++ tailWord_1709291).sum := by decide
  have hdescent : baseEnd_1709291 < baseStart_1709291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709293 : List Nat := [1, 5, 1, 2, 2, 2, 1, 1, 7]
def baseStart_1709293 : Nat := 118140960795 + 1709293 * 2 ^ 59
def prefixEnd_1709293 : Nat := 4983230072969 + 3 ^ 40 * 1709293 * 2
def baseEnd_1709293 : Nat := 195041975192374692661469

theorem tailTrace_1709293 : CollatzResearch.WordTrace tailWord_1709293 prefixEnd_1709293 195041975192374692661469 := by
  unfold tailWord_1709293
  simp only [CollatzResearch.WordTrace]
  refine ⟨62343037396530859848252533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41562024931020573232168355 62343037396530859848252533)
  ·
    refine ⟨5844659755924768110773675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62343037396530859848252533 5844659755924768110773675)
    ·
      refine ⟨8766989633887152166160513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5844659755924768110773675 8766989633887152166160513)
      ·
        refine ⟨6575242225415364124620385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8766989633887152166160513 6575242225415364124620385)
        ·
          refine ⟨4931431669061523093465289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6575242225415364124620385 4931431669061523093465289)
          ·
            refine ⟨3698573751796142320098967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4931431669061523093465289 3698573751796142320098967)
            ·
              refine ⟨5547860627694213480148451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3698573751796142320098967 5547860627694213480148451)
              ·
                refine ⟨8321790941541320220222677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5547860627694213480148451 8321790941541320220222677)
                ·
                  refine ⟨195041975192374692661469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8321790941541320220222677 195041975192374692661469)
                  ·
                    rfl

theorem cell22_1709293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_1709293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709293 prefixEnd_1709293 := by exact prefixLift 1709293
  have htrace : WordTrace (prefixWord ++ tailWord_1709293) baseStart_1709293 baseEnd_1709293 := by
    simpa [prefixWord, tailWord_1709293, baseEnd_1709293] using wordTrace_append hprefix tailTrace_1709293
  have hstable : (prefixWord ++ tailWord_1709293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709293).length < 2 ^ (prefixWord ++ tailWord_1709293).sum := by decide
  have hdescent : baseEnd_1709293 < baseStart_1709293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709321 : List Nat := [1, 2, 1, 1, 3, 3, 1, 4, 6]
def baseStart_1709321 : Nat := 118140960795 + 1709321 * 2 ^ 59
def prefixEnd_1709321 : Nat := 4983230072969 + 3 ^ 40 * 1709321 * 2
def baseEnd_1709321 : Nat := 195045170183113779428107

theorem tailTrace_1709321 : CollatzResearch.WordTrace tailWord_1709321 prefixEnd_1709321 195045170183113779428107 := by
  unfold tailWord_1709321
  simp only [CollatzResearch.WordTrace]
  refine ⟨62344058640429420630271817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41562705760286280420181211 62344058640429420630271817)
  ·
    refine ⟨46758043980322065472703863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62344058640429420630271817 46758043980322065472703863)
    ·
      refine ⟨70137065970483098209055795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46758043980322065472703863 70137065970483098209055795)
      ·
        refine ⟨105205598955724647313583693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70137065970483098209055795 105205598955724647313583693)
        ·
          refine ⟨39452099608396742742593885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105205598955724647313583693 39452099608396742742593885)
          ·
            refine ⟨14794537353148778528472707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39452099608396742742593885 14794537353148778528472707)
            ·
              refine ⟨22191806029723167792709061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14794537353148778528472707 22191806029723167792709061)
              ·
                refine ⟨4160963630573093961132949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22191806029723167792709061 4160963630573093961132949)
                ·
                  refine ⟨195045170183113779428107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4160963630573093961132949 195045170183113779428107)
                  ·
                    rfl

theorem cell22_1709321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 6].length) (baseStart_1709321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709321 prefixEnd_1709321 := by exact prefixLift 1709321
  have htrace : WordTrace (prefixWord ++ tailWord_1709321) baseStart_1709321 baseEnd_1709321 := by
    simpa [prefixWord, tailWord_1709321, baseEnd_1709321] using wordTrace_append hprefix tailTrace_1709321
  have hstable : (prefixWord ++ tailWord_1709321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709321).length < 2 ^ (prefixWord ++ tailWord_1709321).sum := by decide
  have hdescent : baseEnd_1709321 < baseStart_1709321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709323 : List Nat := [1, 1, 1, 1, 5, 3, 1, 4, 1, 4]
def baseStart_1709323 : Nat := 118140960795 + 1709323 * 2 ^ 59
def prefixEnd_1709323 : Nat := 4983230072969 + 3 ^ 40 * 1709323 * 2
def baseEnd_1709323 : Nat := 585136195190213999734315

theorem tailTrace_1709323 : CollatzResearch.WordTrace tailWord_1709323 prefixEnd_1709323 585136195190213999734315 := by
  unfold tailWord_1709323
  simp only [CollatzResearch.WordTrace]
  refine ⟨62344131586422174971844623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41562754390948116647896415 62344131586422174971844623)
  ·
    refine ⟨93516197379633262457766935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62344131586422174971844623 93516197379633262457766935)
    ·
      refine ⟨140274296069449893686650403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93516197379633262457766935 140274296069449893686650403)
      ·
        refine ⟨210411444104174840529975605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140274296069449893686650403 210411444104174840529975605)
        ·
          refine ⟨19726072884766391299685213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 210411444104174840529975605 19726072884766391299685213)
          ·
            refine ⟨7397277331787396737381955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19726072884766391299685213 7397277331787396737381955)
            ·
              refine ⟨11095915997681095106072933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7397277331787396737381955 11095915997681095106072933)
              ·
                refine ⟨2080484249565205332388675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11095915997681095106072933 2080484249565205332388675)
                ·
                  refine ⟨3120726374347807998583013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2080484249565205332388675 3120726374347807998583013)
                  ·
                    refine ⟨585136195190213999734315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3120726374347807998583013 585136195190213999734315)
                    ·
                      rfl

theorem cell22_1709323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 4].length) (baseStart_1709323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709323 prefixEnd_1709323 := by exact prefixLift 1709323
  have htrace : WordTrace (prefixWord ++ tailWord_1709323) baseStart_1709323 baseEnd_1709323 := by
    simpa [prefixWord, tailWord_1709323, baseEnd_1709323] using wordTrace_append hprefix tailTrace_1709323
  have hstable : (prefixWord ++ tailWord_1709323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709323).length < 2 ^ (prefixWord ++ tailWord_1709323).sum := by decide
  have hdescent : baseEnd_1709323 < baseStart_1709323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709370 : List Nat := [3, 1, 1, 1, 4, 1, 3, 3, 2, 3]
def baseStart_1709370 : Nat := 118140960795 + 1709370 * 2 ^ 59
def prefixEnd_1709370 : Nat := 4983230072969 + 3 ^ 40 * 1709370 * 2
def baseEnd_1709370 : Nat := 585152284250721543809171

theorem tailTrace_1709370 : CollatzResearch.WordTrace tailWord_1709370 prefixEnd_1709370 585152284250721543809171 := by
  unfold tailWord_1709370
  simp only [CollatzResearch.WordTrace]
  refine ⟨15586461454312975499701391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41563897211501267999203709 15586461454312975499701391)
  ·
    refine ⟨23379692181469463249552087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15586461454312975499701391 23379692181469463249552087)
    ·
      refine ⟨35069538272204194874328131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23379692181469463249552087 35069538272204194874328131)
      ·
        refine ⟨52604307408306292311492197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35069538272204194874328131 52604307408306292311492197)
        ·
          refine ⟨9863307639057429808404787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52604307408306292311492197 9863307639057429808404787)
          ·
            refine ⟨14794961458586144712607181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9863307639057429808404787 14794961458586144712607181)
            ·
              refine ⟨5548110546969804267227693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14794961458586144712607181 5548110546969804267227693)
              ·
                refine ⟨2080541455113676600210385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5548110546969804267227693 2080541455113676600210385)
                ·
                  refine ⟨1560406091335257450157789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2080541455113676600210385 1560406091335257450157789)
                  ·
                    refine ⟨585152284250721543809171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1560406091335257450157789 585152284250721543809171)
                    ·
                      rfl

theorem cell22_1709370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 2, 3].length) (baseStart_1709370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709370 prefixEnd_1709370 := by exact prefixLift 1709370
  have htrace : WordTrace (prefixWord ++ tailWord_1709370) baseStart_1709370 baseEnd_1709370 := by
    simpa [prefixWord, tailWord_1709370, baseEnd_1709370] using wordTrace_append hprefix tailTrace_1709370
  have hstable : (prefixWord ++ tailWord_1709370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709370).length < 2 ^ (prefixWord ++ tailWord_1709370).sum := by decide
  have hdescent : baseEnd_1709370 < baseStart_1709370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709381 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 2, 7]
def baseStart_1709381 : Nat := 118140960795 + 1709381 * 2 ^ 59
def prefixEnd_1709381 : Nat := 4983230072969 + 3 ^ 40 * 1709381 * 2
def baseEnd_1709381 : Nat := 585156049775521181784137

theorem tailTrace_1709381 : CollatzResearch.WordTrace tailWord_1709381 prefixEnd_1709381 585156049775521181784137 := by
  unfold tailWord_1709381
  simp only [CollatzResearch.WordTrace]
  refine ⟨62346247020212050877455997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41564164680141367251637331 62346247020212050877455997)
  ·
    refine ⟨23379842632579519079045999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62346247020212050877455997 23379842632579519079045999)
    ·
      refine ⟨35069763948869278618568999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23379842632579519079045999 35069763948869278618568999)
      ·
        refine ⟨52604645923303917927853499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35069763948869278618568999 52604645923303917927853499)
        ·
          refine ⟨78906968884955876891780249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52604645923303917927853499 78906968884955876891780249)
          ·
            refine ⟨59180226663716907668835187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78906968884955876891780249 59180226663716907668835187)
            ·
              refine ⟨88770339995575361503252781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59180226663716907668835187 88770339995575361503252781)
              ·
                refine ⟨33288877498340760563719793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88770339995575361503252781 33288877498340760563719793)
                ·
                  refine ⟨24966658123755570422789845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33288877498340760563719793 24966658123755570422789845)
                  ·
                    refine ⟨585156049775521181784137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24966658123755570422789845 585156049775521181784137)
                    ·
                      rfl

theorem cell22_1709381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_1709381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709381 prefixEnd_1709381 := by exact prefixLift 1709381
  have htrace : WordTrace (prefixWord ++ tailWord_1709381) baseStart_1709381 baseEnd_1709381 := by
    simpa [prefixWord, tailWord_1709381, baseEnd_1709381] using wordTrace_append hprefix tailTrace_1709381
  have hstable : (prefixWord ++ tailWord_1709381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709381).length < 2 ^ (prefixWord ++ tailWord_1709381).sum := by decide
  have hdescent : baseEnd_1709381 < baseStart_1709381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709449 : List Nat := [1, 2, 1, 1, 7, 1, 2, 3, 1, 3]
def baseStart_1709449 : Nat := 118140960795 + 1709449 * 2 ^ 59
def prefixEnd_1709449 : Nat := 4983230072969 + 3 ^ 40 * 1709449 * 2
def baseEnd_1709449 : Nat := 585179327565191671083929

theorem tailTrace_1709449 : CollatzResearch.WordTrace tailWord_1709449 prefixEnd_1709449 585179327565191671083929 := by
  unfold tailWord_1709449
  simp only [CollatzResearch.WordTrace]
  refine ⟨62348727183965698490931401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41565818122643798993954267 62348727183965698490931401)
  ·
    refine ⟨46761545387974273868198551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62348727183965698490931401 46761545387974273868198551)
    ·
      refine ⟨70142318081961410802297827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46761545387974273868198551 70142318081961410802297827)
      ·
        refine ⟨105213477122942116203446741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70142318081961410802297827 105213477122942116203446741)
        ·
          refine ⟨2465940870068955848518283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 105213477122942116203446741 2465940870068955848518283)
          ·
            refine ⟨3698911305103433772777425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2465940870068955848518283 3698911305103433772777425)
            ·
              refine ⟨2774183478827575329583069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3698911305103433772777425 2774183478827575329583069)
              ·
                refine ⟨1040318804560340748593651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2774183478827575329583069 1040318804560340748593651)
                ·
                  refine ⟨1560478206840511122890477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1040318804560340748593651 1560478206840511122890477)
                  ·
                    refine ⟨585179327565191671083929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1560478206840511122890477 585179327565191671083929)
                    ·
                      rfl

theorem cell22_1709449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 1, 3].length) (baseStart_1709449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709449 prefixEnd_1709449 := by exact prefixLift 1709449
  have htrace : WordTrace (prefixWord ++ tailWord_1709449) baseStart_1709449 baseEnd_1709449 := by
    simpa [prefixWord, tailWord_1709449, baseEnd_1709449] using wordTrace_append hprefix tailTrace_1709449
  have hstable : (prefixWord ++ tailWord_1709449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709449).length < 2 ^ (prefixWord ++ tailWord_1709449).sum := by decide
  have hdescent : baseEnd_1709449 < baseStart_1709449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709460 : List Nat := [2, 4, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_1709460 : Nat := 118140960795 + 1709460 * 2 ^ 59
def prefixEnd_1709460 : Nat := 4983230072969 + 3 ^ 40 * 1709460 * 2
def baseEnd_1709460 : Nat := 585183093089991309058895

theorem tailTrace_1709460 : CollatzResearch.WordTrace tailWord_1709460 prefixEnd_1709460 585183093089991309058895 := by
  unfold tailWord_1709460
  simp only [CollatzResearch.WordTrace]
  refine ⟨31174564193462923684790917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41566085591283898246387889 31174564193462923684790917)
  ·
    refine ⟨5845230786274298190898297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31174564193462923684790917 5845230786274298190898297)
    ·
      refine ⟨4383923089705723643173723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5845230786274298190898297 4383923089705723643173723)
      ·
        refine ⟨6575884634558585464760585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4383923089705723643173723 6575884634558585464760585)
        ·
          refine ⟨4931913475918939098570439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6575884634558585464760585 4931913475918939098570439)
          ·
            refine ⟨7397870213878408647855659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4931913475918939098570439 7397870213878408647855659)
            ·
              refine ⟨11096805320817612971783489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7397870213878408647855659 11096805320817612971783489)
              ·
                refine ⟨8322603990613209728837617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11096805320817612971783489 8322603990613209728837617)
                ·
                  refine ⟨6241952992959907296628213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8322603990613209728837617 6241952992959907296628213)
                  ·
                    refine ⟨585183093089991309058895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6241952992959907296628213 585183093089991309058895)
                    ·
                      rfl

theorem cell22_1709460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_1709460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709460 prefixEnd_1709460 := by exact prefixLift 1709460
  have htrace : WordTrace (prefixWord ++ tailWord_1709460) baseStart_1709460 baseEnd_1709460 := by
    simpa [prefixWord, tailWord_1709460, baseEnd_1709460] using wordTrace_append hprefix tailTrace_1709460
  have hstable : (prefixWord ++ tailWord_1709460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709460).length < 2 ^ (prefixWord ++ tailWord_1709460).sum := by decide
  have hdescent : baseEnd_1709460 < baseStart_1709460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709488 : List Nat := [2, 1, 1, 1, 2, 1, 1, 7, 1, 5]
def baseStart_1709488 : Nat := 118140960795 + 1709488 * 2 ^ 59
def prefixEnd_1709488 : Nat := 4983230072969 + 3 ^ 40 * 1709488 * 2
def baseEnd_1709488 : Nat := 585192678062208569358809

theorem tailTrace_1709488 : CollatzResearch.WordTrace tailWord_1709488 prefixEnd_1709488 585192678062208569358809 := by
  unfold tailWord_1709488
  simp only [CollatzResearch.WordTrace]
  refine ⟨31175074815412204075800559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41566766420549605434400745 31175074815412204075800559)
  ·
    refine ⟨46762612223118306113700839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31175074815412204075800559 46762612223118306113700839)
    ·
      refine ⟨70143918334677459170551259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46762612223118306113700839 70143918334677459170551259)
      ·
        refine ⟨105215877502016188755826889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70143918334677459170551259 105215877502016188755826889)
        ·
          refine ⟨78911908126512141566870167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105215877502016188755826889 78911908126512141566870167)
          ·
            refine ⟨118367862189768212350305251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78911908126512141566870167 118367862189768212350305251)
            ·
              refine ⟨177551793284652318525457877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118367862189768212350305251 177551793284652318525457877)
              ·
                refine ⟨4161370155109038715440419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 177551793284652318525457877 4161370155109038715440419)
                ·
                  refine ⟨6242055232663558073160629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4161370155109038715440419 6242055232663558073160629)
                  ·
                    refine ⟨585192678062208569358809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6242055232663558073160629 585192678062208569358809)
                    ·
                      rfl

theorem cell22_1709488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 1, 5].length) (baseStart_1709488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709488 prefixEnd_1709488 := by exact prefixLift 1709488
  have htrace : WordTrace (prefixWord ++ tailWord_1709488) baseStart_1709488 baseEnd_1709488 := by
    simpa [prefixWord, tailWord_1709488, baseEnd_1709488] using wordTrace_append hprefix tailTrace_1709488
  have hstable : (prefixWord ++ tailWord_1709488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709488).length < 2 ^ (prefixWord ++ tailWord_1709488).sum := by decide
  have hdescent : baseEnd_1709488 < baseStart_1709488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709503 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 6, 4]
def baseStart_1709503 : Nat := 118140960795 + 1709503 * 2 ^ 59
def prefixEnd_1709503 : Nat := 4983230072969 + 3 ^ 40 * 1709503 * 2
def baseEnd_1709503 : Nat := 585197812868753530233763

theorem tailTrace_1709503 : CollatzResearch.WordTrace tailWord_1709503 prefixEnd_1709503 585197812868753530233763 := by
  unfold tailWord_1709503
  simp only [CollatzResearch.WordTrace]
  refine ⟨62350696725770065713397163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41567131150513377142264775 62350696725770065713397163)
  ·
    refine ⟨93526045088655098570095745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62350696725770065713397163 93526045088655098570095745)
    ·
      refine ⟨70144533816491323927571809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93526045088655098570095745 70144533816491323927571809)
      ·
        refine ⟨52608400362368492945678857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70144533816491323927571809 52608400362368492945678857)
        ·
          refine ⟨39456300271776369709259143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52608400362368492945678857 39456300271776369709259143)
          ·
            refine ⟨59184450407664554563888715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39456300271776369709259143 59184450407664554563888715)
            ·
              refine ⟨88776675611496831845833073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59184450407664554563888715 88776675611496831845833073)
              ·
                refine ⟨66582506708622623884374805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88776675611496831845833073 66582506708622623884374805)
                ·
                  refine ⟨3121055001966685494580069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66582506708622623884374805 3121055001966685494580069)
                  ·
                    refine ⟨585197812868753530233763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3121055001966685494580069 585197812868753530233763)
                    ·
                      rfl

theorem cell22_1709503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 4].length) (baseStart_1709503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709503 prefixEnd_1709503 := by exact prefixLift 1709503
  have htrace : WordTrace (prefixWord ++ tailWord_1709503) baseStart_1709503 baseEnd_1709503 := by
    simpa [prefixWord, tailWord_1709503, baseEnd_1709503] using wordTrace_append hprefix tailTrace_1709503
  have hstable : (prefixWord ++ tailWord_1709503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709503).length < 2 ^ (prefixWord ++ tailWord_1709503).sum := by decide
  have hdescent : baseEnd_1709503 < baseStart_1709503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709518 : List Nat := [4, 1, 1, 1, 2, 1, 12]
def baseStart_1709518 : Nat := 118140960795 + 1709518 * 2 ^ 59
def prefixEnd_1709518 : Nat := 4983230072969 + 3 ^ 40 * 1709518 * 2
def baseEnd_1709518 : Nat := 21674183247233277448471

theorem tailTrace_1709518 : CollatzResearch.WordTrace tailWord_1709518 prefixEnd_1709518 21674183247233277448471 := by
  unfold tailWord_1709518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7793905477589465409399151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41567495880477148850128805 7793905477589465409399151)
  ·
    refine ⟨11690858216384198114098727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7793905477589465409399151 11690858216384198114098727)
    ·
      refine ⟨17536287324576297171148091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11690858216384198114098727 17536287324576297171148091)
      ·
        refine ⟨26304430986864445756722137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17536287324576297171148091 26304430986864445756722137)
        ·
          refine ⟨19728323240148334317541603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26304430986864445756722137 19728323240148334317541603)
          ·
            refine ⟨29592484860222501476312405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19728323240148334317541603 29592484860222501476312405)
            ·
              refine ⟨21674183247233277448471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 29592484860222501476312405 21674183247233277448471)
              ·
                rfl

theorem cell22_1709518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 12].length) (baseStart_1709518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709518 prefixEnd_1709518 := by exact prefixLift 1709518
  have htrace : WordTrace (prefixWord ++ tailWord_1709518) baseStart_1709518 baseEnd_1709518 := by
    simpa [prefixWord, tailWord_1709518, baseEnd_1709518] using wordTrace_append hprefix tailTrace_1709518
  have hstable : (prefixWord ++ tailWord_1709518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709518).length < 2 ^ (prefixWord ++ tailWord_1709518).sum := by decide
  have hdescent : baseEnd_1709518 < baseStart_1709518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709524 : List Nat := [2, 4, 1, 2, 4, 1, 1, 1, 6]
def baseStart_1709524 : Nat := 118140960795 + 1709524 * 2 ^ 59
def prefixEnd_1709524 : Nat := 4983230072969 + 3 ^ 40 * 1709524 * 2
def baseEnd_1709524 : Nat := 195068333865972158486233

theorem tailTrace_1709524 : CollatzResearch.WordTrace tailWord_1709524 prefixEnd_1709524 195068333865972158486233 := by
  unfold tailWord_1709524
  simp only [CollatzResearch.WordTrace]
  refine ⟨31175731329346993149955813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41567641772462657533274417 31175731329346993149955813)
  ·
    refine ⟨5845449624252561215616715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31175731329346993149955813 5845449624252561215616715)
    ·
      refine ⟨8768174436378841823425073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5845449624252561215616715 8768174436378841823425073)
      ·
        refine ⟨6576130827284131367568805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8768174436378841823425073 6576130827284131367568805)
        ·
          refine ⟨1233024530115774631419151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6576130827284131367568805 1233024530115774631419151)
          ·
            refine ⟨1849536795173661947128727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233024530115774631419151 1849536795173661947128727)
            ·
              refine ⟨2774305192760492920693091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1849536795173661947128727 2774305192760492920693091)
              ·
                refine ⟨4161457789140739381039637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2774305192760492920693091 4161457789140739381039637)
                ·
                  refine ⟨195068333865972158486233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4161457789140739381039637 195068333865972158486233)
                  ·
                    rfl

theorem cell22_1709524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_1709524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709524 prefixEnd_1709524 := by exact prefixLift 1709524
  have htrace : WordTrace (prefixWord ++ tailWord_1709524) baseStart_1709524 baseEnd_1709524 := by
    simpa [prefixWord, tailWord_1709524, baseEnd_1709524] using wordTrace_append hprefix tailTrace_1709524
  have hstable : (prefixWord ++ tailWord_1709524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709524).length < 2 ^ (prefixWord ++ tailWord_1709524).sum := by decide
  have hdescent : baseEnd_1709524 < baseStart_1709524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709539 : List Nat := [1, 1, 1, 6, 2, 1, 4, 1, 2, 3]
def baseStart_1709539 : Nat := 118140960795 + 1709539 * 2 ^ 59
def prefixEnd_1709539 : Nat := 4983230072969 + 3 ^ 40 * 1709539 * 2
def baseEnd_1709539 : Nat := 585210136404461436333653

theorem tailTrace_1709539 : CollatzResearch.WordTrace tailWord_1709539 prefixEnd_1709539 585210136404461436333653 := by
  unfold tailWord_1709539
  simp only [CollatzResearch.WordTrace]
  refine ⟨62352009753639643861707671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41568006502426429241138447 62352009753639643861707671)
  ·
    refine ⟨93528014630459465792561507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62352009753639643861707671 93528014630459465792561507)
    ·
      refine ⟨140292021945689198688842261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93528014630459465792561507 140292021945689198688842261)
      ·
        refine ⟨6576188528704181188539481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 140292021945689198688842261 6576188528704181188539481)
        ·
          refine ⟨4932141396528135891404611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6576188528704181188539481 4932141396528135891404611)
          ·
            refine ⟨7398212094792203837106917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4932141396528135891404611 7398212094792203837106917)
            ·
              refine ⟨1387164767773538219457547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7398212094792203837106917 1387164767773538219457547)
              ·
                refine ⟨2080747151660307329186321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1387164767773538219457547 2080747151660307329186321)
                ·
                  refine ⟨1560560363745230496889741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2080747151660307329186321 1560560363745230496889741)
                  ·
                    refine ⟨585210136404461436333653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1560560363745230496889741 585210136404461436333653)
                    ·
                      rfl

theorem cell22_1709539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 2, 3].length) (baseStart_1709539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709539 prefixEnd_1709539 := by exact prefixLift 1709539
  have htrace : WordTrace (prefixWord ++ tailWord_1709539) baseStart_1709539 baseEnd_1709539 := by
    simpa [prefixWord, tailWord_1709539, baseEnd_1709539] using wordTrace_append hprefix tailTrace_1709539
  have hstable : (prefixWord ++ tailWord_1709539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709539).length < 2 ^ (prefixWord ++ tailWord_1709539).sum := by decide
  have hdescent : baseEnd_1709539 < baseStart_1709539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709548 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 4, 6]
def baseStart_1709548 : Nat := 118140960795 + 1709548 * 2 ^ 59
def prefixEnd_1709548 : Nat := 4983230072969 + 3 ^ 40 * 1709548 * 2
def baseEnd_1709548 : Nat := 585213217288388412858625

theorem tailTrace_1709548 : CollatzResearch.WordTrace tailWord_1709548 prefixEnd_1709548 585213217288388412858625 := by
  unfold tailWord_1709548
  simp only [CollatzResearch.WordTrace]
  refine ⟨31176169005303519199392649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41568225340404692265856865 31176169005303519199392649)
  ·
    refine ⟨23382126753977639399544487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31176169005303519199392649 23382126753977639399544487)
    ·
      refine ⟨35073190130966459099316731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23382126753977639399544487 35073190130966459099316731)
      ·
        refine ⟨52609785196449688648975097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35073190130966459099316731 52609785196449688648975097)
        ·
          refine ⟨39457338897337266486731323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52609785196449688648975097 39457338897337266486731323)
          ·
            refine ⟨59186008346005899730096985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39457338897337266486731323 59186008346005899730096985)
            ·
              refine ⟨44389506259504424797572739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59186008346005899730096985 44389506259504424797572739)
              ·
                refine ⟨66584259389256637196359109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44389506259504424797572739 66584259389256637196359109)
                ·
                  refine ⟨12484548635485619474317333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66584259389256637196359109 12484548635485619474317333)
                  ·
                    refine ⟨585213217288388412858625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12484548635485619474317333 585213217288388412858625)
                    ·
                      rfl

theorem cell22_1709548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_1709548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709548 prefixEnd_1709548 := by exact prefixLift 1709548
  have htrace : WordTrace (prefixWord ++ tailWord_1709548) baseStart_1709548 baseEnd_1709548 := by
    simpa [prefixWord, tailWord_1709548, baseEnd_1709548] using wordTrace_append hprefix tailTrace_1709548
  have hstable : (prefixWord ++ tailWord_1709548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709548).length < 2 ^ (prefixWord ++ tailWord_1709548).sum := by decide
  have hdescent : baseEnd_1709548 < baseStart_1709548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709593 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 1, 10]
def baseStart_1709593 : Nat := 118140960795 + 1709593 * 2 ^ 59
def prefixEnd_1709593 : Nat := 4983230072969 + 3 ^ 40 * 1709593 * 2
def baseEnd_1709593 : Nat := 585228621708023295483487

theorem tailTrace_1709593 : CollatzResearch.WordTrace tailWord_1709593 prefixEnd_1709593 585228621708023295483487 := by
  unfold tailWord_1709593
  simp only [CollatzResearch.WordTrace]
  refine ⟨62353979295444011084173433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41569319530296007389448955 62353979295444011084173433)
  ·
    refine ⟨46765484471583008313130075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62353979295444011084173433 46765484471583008313130075)
    ·
      refine ⟨70148226707374512469695113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46765484471583008313130075 70148226707374512469695113)
      ·
        refine ⟨52611170030530884352271335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70148226707374512469695113 52611170030530884352271335)
        ·
          refine ⟨78916755045796326528407003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52611170030530884352271335 78916755045796326528407003)
          ·
            refine ⟨118375132568694489792610505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78916755045796326528407003 118375132568694489792610505)
            ·
              refine ⟨88781349426520867344457879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118375132568694489792610505 88781349426520867344457879)
              ·
                refine ⟨133172024139781301016686819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88781349426520867344457879 133172024139781301016686819)
                ·
                  refine ⟨199758036209671951525030229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133172024139781301016686819 199758036209671951525030229)
                  ·
                    refine ⟨585228621708023295483487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 199758036209671951525030229 585228621708023295483487)
                    ·
                      rfl

theorem cell22_1709593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_1709593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709593 prefixEnd_1709593 := by exact prefixLift 1709593
  have htrace : WordTrace (prefixWord ++ tailWord_1709593) baseStart_1709593 baseEnd_1709593 := by
    simpa [prefixWord, tailWord_1709593, baseEnd_1709593] using wordTrace_append hprefix tailTrace_1709593
  have hstable : (prefixWord ++ tailWord_1709593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709593).length < 2 ^ (prefixWord ++ tailWord_1709593).sum := by decide
  have hdescent : baseEnd_1709593 < baseStart_1709593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709642 : List Nat := [3, 1, 2, 1, 1, 3, 1, 6, 4]
def baseStart_1709642 : Nat := 118140960795 + 1709642 * 2 ^ 59
def prefixEnd_1709642 : Nat := 4983230072969 + 3 ^ 40 * 1709642 * 2
def baseEnd_1709642 : Nat := 195081798469801167002779

theorem tailTrace_1709642 : CollatzResearch.WordTrace tailWord_1709642 prefixEnd_1709642 195081798469801167002779 := by
  unfold tailWord_1709642
  simp only [CollatzResearch.WordTrace]
  refine ⟨15588941618066623113176795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41570510981510994968471453 15588941618066623113176795)
  ·
    refine ⟨23383412427099934669765193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15588941618066623113176795 23383412427099934669765193)
    ·
      refine ⟨17537559320324951002323895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23383412427099934669765193 17537559320324951002323895)
      ·
        refine ⟨26306338980487426503485843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17537559320324951002323895 26306338980487426503485843)
        ·
          refine ⟨39459508470731139755228765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26306338980487426503485843 39459508470731139755228765)
          ·
            refine ⟨14797315676524177408210787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39459508470731139755228765 14797315676524177408210787)
            ·
              refine ⟨22195973514786266112316181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14797315676524177408210787 22195973514786266112316181)
              ·
                refine ⟨1040436258505606224014821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22195973514786266112316181 1040436258505606224014821)
                ·
                  refine ⟨195081798469801167002779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1040436258505606224014821 195081798469801167002779)
                  ·
                    rfl

theorem cell22_1709642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 4].length) (baseStart_1709642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709642 prefixEnd_1709642 := by exact prefixLift 1709642
  have htrace : WordTrace (prefixWord ++ tailWord_1709642) baseStart_1709642 baseEnd_1709642 := by
    simpa [prefixWord, tailWord_1709642, baseEnd_1709642] using wordTrace_append hprefix tailTrace_1709642
  have hstable : (prefixWord ++ tailWord_1709642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709642).length < 2 ^ (prefixWord ++ tailWord_1709642).sum := by decide
  have hdescent : baseEnd_1709642 < baseStart_1709642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709655 : List Nat := [1, 1, 3, 2, 2, 3, 1, 2, 1, 6]
def baseStart_1709655 : Nat := 118140960795 + 1709655 * 2 ^ 59
def prefixEnd_1709655 : Nat := 4983230072969 + 3 ^ 40 * 1709655 * 2
def baseEnd_1709655 : Nat := 585249845575075800433297

theorem tailTrace_1709655 : CollatzResearch.WordTrace tailWord_1709655 prefixEnd_1709655 585249845575075800433297 := by
  unfold tailWord_1709655
  simp only [CollatzResearch.WordTrace]
  refine ⟨62356240621219395672930419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41570827080812930448620279 62356240621219395672930419)
  ·
    refine ⟨93534360931829093509395629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62356240621219395672930419 93534360931829093509395629)
    ·
      refine ⟨35075385349435910066023361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93534360931829093509395629 35075385349435910066023361)
      ·
        refine ⟨26306539012076932549517521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35075385349435910066023361 26306539012076932549517521)
        ·
          refine ⟨19729904259057699412138141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26306539012076932549517521 19729904259057699412138141)
          ·
            refine ⟨7398714097146637279551803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19729904259057699412138141 7398714097146637279551803)
            ·
              refine ⟨11098071145719955919327705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7398714097146637279551803 11098071145719955919327705)
              ·
                refine ⟨8323553359289966939495779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11098071145719955919327705 8323553359289966939495779)
                ·
                  refine ⟨12485330038934950409243669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8323553359289966939495779 12485330038934950409243669)
                  ·
                    refine ⟨585249845575075800433297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12485330038934950409243669 585249845575075800433297)
                    ·
                      rfl

theorem cell22_1709655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_1709655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709655 prefixEnd_1709655 := by exact prefixLift 1709655
  have htrace : WordTrace (prefixWord ++ tailWord_1709655) baseStart_1709655 baseEnd_1709655 := by
    simpa [prefixWord, tailWord_1709655, baseEnd_1709655] using wordTrace_append hprefix tailTrace_1709655
  have hstable : (prefixWord ++ tailWord_1709655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709655).length < 2 ^ (prefixWord ++ tailWord_1709655).sum := by decide
  have hdescent : baseEnd_1709655 < baseStart_1709655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709657 : List Nat := [1, 2, 1, 2, 2, 1, 1, 7, 2, 3]
def baseStart_1709657 : Nat := 118140960795 + 1709657 * 2 ^ 59
def prefixEnd_1709657 : Nat := 4983230072969 + 3 ^ 40 * 1709657 * 2
def baseEnd_1709657 : Nat := 585250530215948461883291

theorem tailTrace_1709657 : CollatzResearch.WordTrace tailWord_1709657 prefixEnd_1709657 585250530215948461883291 := by
  unfold tailWord_1709657
  simp only [CollatzResearch.WordTrace]
  refine ⟨62356313567212150014503225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41570875711474766676335483 62356313567212150014503225)
  ·
    refine ⟨46767235175409112510877419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62356313567212150014503225 46767235175409112510877419)
    ·
      refine ⟨70150852763113668766316129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46767235175409112510877419 70150852763113668766316129)
      ·
        refine ⟨52613139572335251574737097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70150852763113668766316129 52613139572335251574737097)
        ·
          refine ⟨39459854679251438681052823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52613139572335251574737097 39459854679251438681052823)
          ·
            refine ⟨59189782018877158021579235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39459854679251438681052823 59189782018877158021579235)
            ·
              refine ⟨88784673028315737032368853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59189782018877158021579235 88784673028315737032368853)
              ·
                refine ⟨2080890774101150086696145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 88784673028315737032368853 2080890774101150086696145)
                ·
                  refine ⟨1560668080575862565022109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2080890774101150086696145 1560668080575862565022109)
                  ·
                    refine ⟨585250530215948461883291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1560668080575862565022109 585250530215948461883291)
                    ·
                      rfl

theorem cell22_1709657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 3].length) (baseStart_1709657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709657 prefixEnd_1709657 := by exact prefixLift 1709657
  have htrace : WordTrace (prefixWord ++ tailWord_1709657) baseStart_1709657 baseEnd_1709657 := by
    simpa [prefixWord, tailWord_1709657, baseEnd_1709657] using wordTrace_append hprefix tailTrace_1709657
  have hstable : (prefixWord ++ tailWord_1709657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709657).length < 2 ^ (prefixWord ++ tailWord_1709657).sum := by decide
  have hdescent : baseEnd_1709657 < baseStart_1709657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709672 : List Nat := [2, 1, 4, 3, 1, 1, 2, 1, 1, 6]
def baseStart_1709672 : Nat := 118140960795 + 1709672 * 2 ^ 59
def prefixEnd_1709672 : Nat := 4983230072969 + 3 ^ 40 * 1709672 * 2
def baseEnd_1709672 : Nat := 585255665022493422758245

theorem tailTrace_1709672 : CollatzResearch.WordTrace tailWord_1709672 prefixEnd_1709672 585255665022493422758245 := by
  unfold tailWord_1709672
  simp only [CollatzResearch.WordTrace]
  refine ⟨31178430331078903788149635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41571240441438538384199513 31178430331078903788149635)
  ·
    refine ⟨46767645496618355682224453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31178430331078903788149635 46767645496618355682224453)
    ·
      refine ⟨8768933530615941690417085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46767645496618355682224453 8768933530615941690417085)
      ·
        refine ⟨3288350073980978133906407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8768933530615941690417085 3288350073980978133906407)
        ·
          refine ⟨4932525110971467200859611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3288350073980978133906407 4932525110971467200859611)
          ·
            refine ⟨7398787666457200801289417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4932525110971467200859611 7398787666457200801289417)
            ·
              refine ⟨5549090749842900600967063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7398787666457200801289417 5549090749842900600967063)
              ·
                refine ⟨8323636124764350901450595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5549090749842900600967063 8323636124764350901450595)
                ·
                  refine ⟨12485454187146526352175893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8323636124764350901450595 12485454187146526352175893)
                  ·
                    refine ⟨585255665022493422758245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12485454187146526352175893 585255665022493422758245)
                    ·
                      rfl

theorem cell22_1709672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_1709672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709672 prefixEnd_1709672 := by exact prefixLift 1709672
  have htrace : WordTrace (prefixWord ++ tailWord_1709672) baseStart_1709672 baseEnd_1709672 := by
    simpa [prefixWord, tailWord_1709672, baseEnd_1709672] using wordTrace_append hprefix tailTrace_1709672
  have hstable : (prefixWord ++ tailWord_1709672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709672).length < 2 ^ (prefixWord ++ tailWord_1709672).sum := by decide
  have hdescent : baseEnd_1709672 < baseStart_1709672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709704 : List Nat := [2, 1, 3, 5, 1, 1, 2, 7]
def baseStart_1709704 : Nat := 118140960795 + 1709704 * 2 ^ 59
def prefixEnd_1709704 : Nat := 4983230072969 + 3 ^ 40 * 1709704 * 2
def baseEnd_1709704 : Nat := 65029624364050667328683

theorem tailTrace_1709704 : CollatzResearch.WordTrace tailWord_1709704 prefixEnd_1709704 65029624364050667328683 := by
  unfold tailWord_1709704
  simp only [CollatzResearch.WordTrace]
  refine ⟨31179013899020938520732083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41572018532027918027642777 31179013899020938520732083)
  ·
    refine ⟨46768520848531407781098125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31179013899020938520732083 46768520848531407781098125)
    ·
      refine ⟨17538195318199277917911797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46768520848531407781098125 17538195318199277917911797)
      ·
        refine ⟨1644205811081182304804231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17538195318199277917911797 1644205811081182304804231)
        ·
          refine ⟨2466308716621773457206347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1644205811081182304804231 2466308716621773457206347)
          ·
            refine ⟨3699463074932660185809521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2466308716621773457206347 3699463074932660185809521)
            ·
              refine ⟨2774597306199495139357141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3699463074932660185809521 2774597306199495139357141)
              ·
                refine ⟨65029624364050667328683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2774597306199495139357141 65029624364050667328683)
                ·
                  rfl

theorem cell22_1709704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 7].length) (baseStart_1709704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709704 prefixEnd_1709704 := by exact prefixLift 1709704
  have htrace : WordTrace (prefixWord ++ tailWord_1709704) baseStart_1709704 baseEnd_1709704 := by
    simpa [prefixWord, tailWord_1709704, baseEnd_1709704] using wordTrace_append hprefix tailTrace_1709704
  have hstable : (prefixWord ++ tailWord_1709704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709704).length < 2 ^ (prefixWord ++ tailWord_1709704).sum := by decide
  have hdescent : baseEnd_1709704 < baseStart_1709704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709777 : List Nat := [1, 2, 2, 1, 2, 5, 1, 2, 6]
def baseStart_1709777 : Nat := 118140960795 + 1709777 * 2 ^ 59
def prefixEnd_1709777 : Nat := 4983230072969 + 3 ^ 40 * 1709777 * 2
def baseEnd_1709777 : Nat := 195097202889436049627641

theorem tailTrace_1709777 : CollatzResearch.WordTrace tailWord_1709777 prefixEnd_1709777 195097202889436049627641 := by
  unfold tailWord_1709777
  simp only [CollatzResearch.WordTrace]
  refine ⟨62360690326777410508871585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41573793551184940339247723 62360690326777410508871585)
  ·
    refine ⟨46770517745083057881653689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62360690326777410508871585 46770517745083057881653689)
    ·
      refine ⟨35077888308812293411240267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46770517745083057881653689 35077888308812293411240267)
      ·
        refine ⟨52616832463218440116860401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35077888308812293411240267 52616832463218440116860401)
        ·
          refine ⟨39462624347413830087645301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52616832463218440116860401 39462624347413830087645301)
          ·
            refine ⟨3699621032570046570716747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39462624347413830087645301 3699621032570046570716747)
            ·
              refine ⟨5549431548855069856075121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3699621032570046570716747 5549431548855069856075121)
              ·
                refine ⟨4162073661641302392056341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5549431548855069856075121 4162073661641302392056341)
                ·
                  refine ⟨195097202889436049627641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4162073661641302392056341 195097202889436049627641)
                  ·
                    rfl

theorem cell22_1709777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 6].length) (baseStart_1709777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709777 prefixEnd_1709777 := by exact prefixLift 1709777
  have htrace : WordTrace (prefixWord ++ tailWord_1709777) baseStart_1709777 baseEnd_1709777 := by
    simpa [prefixWord, tailWord_1709777, baseEnd_1709777] using wordTrace_append hprefix tailTrace_1709777
  have hstable : (prefixWord ++ tailWord_1709777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709777).length < 2 ^ (prefixWord ++ tailWord_1709777).sum := by decide
  have hdescent : baseEnd_1709777 < baseStart_1709777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709792 : List Nat := [2, 1, 1, 3, 1, 2, 4, 2, 1, 5]
def baseStart_1709792 : Nat := 118140960795 + 1709792 * 2 ^ 59
def prefixEnd_1709792 : Nat := 4983230072969 + 3 ^ 40 * 1709792 * 2
def baseEnd_1709792 : Nat := 585296743474853109757877

theorem tailTrace_1709792 : CollatzResearch.WordTrace tailWord_1709792 prefixEnd_1709792 585296743474853109757877 := by
  unfold tailWord_1709792
  simp only [CollatzResearch.WordTrace]
  refine ⟨31180618710861534035333815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41574158281148712047111753 31180618710861534035333815)
  ·
    refine ⟨46770928066292301053000723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31180618710861534035333815 46770928066292301053000723)
    ·
      refine ⟨70156392099438451579501085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46770928066292301053000723 70156392099438451579501085)
      ·
        refine ⟨26308647037289419342312907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70156392099438451579501085 26308647037289419342312907)
        ·
          refine ⟨39462970555934129013469361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26308647037289419342312907 39462970555934129013469361)
          ·
            refine ⟨29597227916950596760102021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39462970555934129013469361 29597227916950596760102021)
            ·
              refine ⟨5549480234428236892519129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29597227916950596760102021 5549480234428236892519129)
              ·
                refine ⟨4162110175821177669389347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5549480234428236892519129 4162110175821177669389347)
                ·
                  refine ⟨6243165263731766504084021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4162110175821177669389347 6243165263731766504084021)
                  ·
                    refine ⟨585296743474853109757877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6243165263731766504084021 585296743474853109757877)
                    ·
                      rfl

theorem cell22_1709792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 1, 5].length) (baseStart_1709792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709792 prefixEnd_1709792 := by exact prefixLift 1709792
  have htrace : WordTrace (prefixWord ++ tailWord_1709792) baseStart_1709792 baseEnd_1709792 := by
    simpa [prefixWord, tailWord_1709792, baseEnd_1709792] using wordTrace_append hprefix tailTrace_1709792
  have hstable : (prefixWord ++ tailWord_1709792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709792).length < 2 ^ (prefixWord ++ tailWord_1709792).sum := by decide
  have hdescent : baseEnd_1709792 < baseStart_1709792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709807 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 4, 4]
def baseStart_1709807 : Nat := 118140960795 + 1709807 * 2 ^ 59
def prefixEnd_1709807 : Nat := 4983230072969 + 3 ^ 40 * 1709807 * 2
def baseEnd_1709807 : Nat := 585301878281398070632831

theorem tailTrace_1709807 : CollatzResearch.WordTrace tailWord_1709807 prefixEnd_1709807 585301878281398070632831 := by
  unfold tailWord_1709807
  simp only [CollatzResearch.WordTrace]
  refine ⟨62361784516668725632463675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41574523011112483754975783 62361784516668725632463675)
  ·
    refine ⟨93542676775003088448695513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62361784516668725632463675 93542676775003088448695513)
    ·
      refine ⟨70157007581252316336521635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93542676775003088448695513 70157007581252316336521635)
      ·
        refine ⟨105235511371878474504782453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70157007581252316336521635 105235511371878474504782453)
        ·
          refine ⟨9865829191113606984823355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105235511371878474504782453 9865829191113606984823355)
          ·
            refine ⟨14798743786670410477235033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9865829191113606984823355 14798743786670410477235033)
            ·
              refine ⟨11099057840002807857926275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14798743786670410477235033 11099057840002807857926275)
              ·
                refine ⟨16648586760004211786889413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11099057840002807857926275 16648586760004211786889413)
                ·
                  refine ⟨3121610017500789710041765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16648586760004211786889413 3121610017500789710041765)
                  ·
                    refine ⟨585301878281398070632831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3121610017500789710041765 585301878281398070632831)
                    ·
                      rfl

theorem cell22_1709807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 4].length) (baseStart_1709807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709807 prefixEnd_1709807 := by exact prefixLift 1709807
  have htrace : WordTrace (prefixWord ++ tailWord_1709807) baseStart_1709807 baseEnd_1709807 := by
    simpa [prefixWord, tailWord_1709807, baseEnd_1709807] using wordTrace_append hprefix tailTrace_1709807
  have hstable : (prefixWord ++ tailWord_1709807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709807).length < 2 ^ (prefixWord ++ tailWord_1709807).sum := by decide
  have hdescent : baseEnd_1709807 < baseStart_1709807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709809 : List Nat := [1, 2, 2, 2, 2, 4, 1, 1, 4, 3]
def baseStart_1709809 : Nat := 118140960795 + 1709809 * 2 ^ 59
def prefixEnd_1709809 : Nat := 4983230072969 + 3 ^ 40 * 1709809 * 2
def baseEnd_1709809 : Nat := 585302562922270732082825

theorem tailTrace_1709809 : CollatzResearch.WordTrace tailWord_1709809 prefixEnd_1709809 585302562922270732082825 := by
  unfold tailWord_1709809
  simp only [CollatzResearch.WordTrace]
  refine ⟨62361857462661479974036481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41574571641774319982690987 62361857462661479974036481)
  ·
    refine ⟨46771393096996109980527361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62361857462661479974036481 46771393096996109980527361)
    ·
      refine ⟨35078544822747082485395521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46771393096996109980527361 35078544822747082485395521)
      ·
        refine ⟨26308908617060311864046641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35078544822747082485395521 26308908617060311864046641)
        ·
          refine ⟨19731681462795233898034981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26308908617060311864046641 19731681462795233898034981)
          ·
            refine ⟨3699690274274106355881559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19731681462795233898034981 3699690274274106355881559)
            ·
              refine ⟨5549535411411159533822339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3699690274274106355881559 5549535411411159533822339)
              ·
                refine ⟨8324303117116739300733509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5549535411411159533822339 8324303117116739300733509)
                ·
                  refine ⟨1560806834459388618887533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8324303117116739300733509 1560806834459388618887533)
                  ·
                    refine ⟨585302562922270732082825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1560806834459388618887533 585302562922270732082825)
                    ·
                      rfl

theorem cell22_1709809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 3].length) (baseStart_1709809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709809 prefixEnd_1709809 := by exact prefixLift 1709809
  have htrace : WordTrace (prefixWord ++ tailWord_1709809) baseStart_1709809 baseEnd_1709809 := by
    simpa [prefixWord, tailWord_1709809, baseEnd_1709809] using wordTrace_append hprefix tailTrace_1709809
  have hstable : (prefixWord ++ tailWord_1709809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709809).length < 2 ^ (prefixWord ++ tailWord_1709809).sum := by decide
  have hdescent : baseEnd_1709809 < baseStart_1709809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709922 : List Nat := [3, 3, 2, 1, 2, 3, 2, 2, 1, 3]
def baseStart_1709922 : Nat := 118140960795 + 1709922 * 2 ^ 59
def prefixEnd_1709922 : Nat := 4983230072969 + 3 ^ 40 * 1709922 * 2
def baseEnd_1709922 : Nat := 585341245131576104007479

theorem tailTrace_1709922 : CollatzResearch.WordTrace tailWord_1709922 prefixEnd_1709922 585341245131576104007479 := by
  unfold tailWord_1709922
  simp only [CollatzResearch.WordTrace]
  refine ⟨15591494727813025068225005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41577319274168066848600013 15591494727813025068225005)
  ·
    refine ⟨5846810522929884400584377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15591494727813025068225005 5846810522929884400584377)
    ·
      refine ⟨4385107892197413300438283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5846810522929884400584377 4385107892197413300438283)
      ·
        refine ⟨6577661838296119950657425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4385107892197413300438283 6577661838296119950657425)
        ·
          refine ⟨4933246378722089962993069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6577661838296119950657425 4933246378722089962993069)
          ·
            refine ⟨1849967392020783736122401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4933246378722089962993069 1849967392020783736122401)
            ·
              refine ⟨1387475544015587802091801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1849967392020783736122401 1387475544015587802091801)
              ·
                refine ⟨1040606658011690851568851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1387475544015587802091801 1040606658011690851568851)
                ·
                  refine ⟨1560909987017536277353277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1040606658011690851568851 1560909987017536277353277)
                  ·
                    refine ⟨585341245131576104007479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1560909987017536277353277 585341245131576104007479)
                    ·
                      rfl

theorem cell22_1709922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_1709922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709922 prefixEnd_1709922 := by exact prefixLift 1709922
  have htrace : WordTrace (prefixWord ++ tailWord_1709922) baseStart_1709922 baseEnd_1709922 := by
    simpa [prefixWord, tailWord_1709922, baseEnd_1709922] using wordTrace_append hprefix tailTrace_1709922
  have hstable : (prefixWord ++ tailWord_1709922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709922).length < 2 ^ (prefixWord ++ tailWord_1709922).sum := by decide
  have hdescent : baseEnd_1709922 < baseStart_1709922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709978 : List Nat := [3, 1, 1, 4, 2, 1, 3, 2, 2, 3]
def baseStart_1709978 : Nat := 118140960795 + 1709978 * 2 ^ 59
def prefixEnd_1709978 : Nat := 4983230072969 + 3 ^ 40 * 1709978 * 2
def baseEnd_1709978 : Nat := 585360415076010624607307

theorem tailTrace_1709978 : CollatzResearch.WordTrace tailWord_1709978 prefixEnd_1709978 585360415076010624607307 := by
  unfold tailWord_1709978
  simp only [CollatzResearch.WordTrace]
  refine ⟨15592005349762305459234647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41578680932699481224625725 15592005349762305459234647)
  ·
    refine ⟨23388008024643458188851971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15592005349762305459234647 23388008024643458188851971)
    ·
      refine ⟨35082012036965187283277957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23388008024643458188851971 35082012036965187283277957)
      ·
        refine ⟨6577877256930972615614617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35082012036965187283277957 6577877256930972615614617)
        ·
          refine ⟨4933407942698229461710963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6577877256930972615614617 4933407942698229461710963)
          ·
            refine ⟨7400111914047344192566445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4933407942698229461710963 7400111914047344192566445)
            ·
              refine ⟨2775041967767754072212417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7400111914047344192566445 2775041967767754072212417)
              ·
                refine ⟨2081281475825815554159313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2775041967767754072212417 2081281475825815554159313)
                ·
                  refine ⟨1560961106869361665619485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2081281475825815554159313 1560961106869361665619485)
                  ·
                    refine ⟨585360415076010624607307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1560961106869361665619485 585360415076010624607307)
                    ·
                      rfl

theorem cell22_1709978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 2, 3].length) (baseStart_1709978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1709978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1709978 prefixEnd_1709978 := by exact prefixLift 1709978
  have htrace : WordTrace (prefixWord ++ tailWord_1709978) baseStart_1709978 baseEnd_1709978 := by
    simpa [prefixWord, tailWord_1709978, baseEnd_1709978] using wordTrace_append hprefix tailTrace_1709978
  have hstable : (prefixWord ++ tailWord_1709978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709978).length < 2 ^ (prefixWord ++ tailWord_1709978).sum := by decide
  have hdescent : baseEnd_1709978 < baseStart_1709978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710036 : List Nat := [2, 4, 1, 2, 1, 1, 2, 4, 5]
def baseStart_1710036 : Nat := 118140960795 + 1710036 * 2 ^ 59
def prefixEnd_1710036 : Nat := 4983230072969 + 3 ^ 40 * 1710036 * 2
def baseEnd_1710036 : Nat := 195126756553772602219043

theorem tailTrace_1710036 : CollatzResearch.WordTrace tailWord_1710036 prefixEnd_1710036 195126756553772602219043 := by
  unfold tailWord_1710036
  simp only [CollatzResearch.WordTrace]
  refine ⟨31185068416419548871274981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41580091221892731828366641 31185068416419548871274981)
  ·
    refine ⟨5847200328078665413364059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31185068416419548871274981 5847200328078665413364059)
    ·
      refine ⟨8770800492117998120046089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5847200328078665413364059 8770800492117998120046089)
      ·
        refine ⟨6578100369088498590034567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8770800492117998120046089 6578100369088498590034567)
        ·
          refine ⟨9867150553632747885051851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6578100369088498590034567 9867150553632747885051851)
          ·
            refine ⟨14800725830449121827577777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9867150553632747885051851 14800725830449121827577777)
            ·
              refine ⟨11100544372836841370683333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14800725830449121827577777 11100544372836841370683333)
              ·
                refine ⟨2081352069906907757003125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11100544372836841370683333 2081352069906907757003125)
                ·
                  refine ⟨195126756553772602219043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2081352069906907757003125 195126756553772602219043)
                  ·
                    rfl

theorem cell22_1710036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_1710036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710036 prefixEnd_1710036 := by exact prefixLift 1710036
  have htrace : WordTrace (prefixWord ++ tailWord_1710036) baseStart_1710036 baseEnd_1710036 := by
    simpa [prefixWord, tailWord_1710036, baseEnd_1710036] using wordTrace_append hprefix tailTrace_1710036
  have hstable : (prefixWord ++ tailWord_1710036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710036).length < 2 ^ (prefixWord ++ tailWord_1710036).sum := by decide
  have hdescent : baseEnd_1710036 < baseStart_1710036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710040 : List Nat := [2, 1, 2, 2, 2, 2, 5, 2, 1, 3]
def baseStart_1710040 : Nat := 118140960795 + 1710040 * 2 ^ 59
def prefixEnd_1710040 : Nat := 4983230072969 + 3 ^ 40 * 1710040 * 2
def baseEnd_1710040 : Nat := 585381638943063129557117

theorem tailTrace_1710040 : CollatzResearch.WordTrace tailWord_1710040 prefixEnd_1710040 585381638943063129557117 := by
  unfold tailWord_1710040
  simp only [CollatzResearch.WordTrace]
  refine ⟨31185141362412303212847787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41580188483216404283797049 31185141362412303212847787)
  ·
    refine ⟨46777712043618454819271681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31185141362412303212847787 46777712043618454819271681)
    ·
      refine ⟨35083284032713841114453761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46777712043618454819271681 35083284032713841114453761)
      ·
        refine ⟨26312463024535380835840321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35083284032713841114453761 26312463024535380835840321)
        ·
          refine ⟨19734347268401535626880241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26312463024535380835840321 19734347268401535626880241)
          ·
            refine ⟨14800760451301151720160181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19734347268401535626880241 14800760451301151720160181)
            ·
              refine ⟨1387571292309482973765017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14800760451301151720160181 1387571292309482973765017)
              ·
                refine ⟨1040678469232112230323763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1387571292309482973765017 1040678469232112230323763)
                ·
                  refine ⟨1561017703848168345485645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1040678469232112230323763 1561017703848168345485645)
                  ·
                    refine ⟨585381638943063129557117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1561017703848168345485645 585381638943063129557117)
                    ·
                      rfl

theorem cell22_1710040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 1, 3].length) (baseStart_1710040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710040 prefixEnd_1710040 := by exact prefixLift 1710040
  have htrace : WordTrace (prefixWord ++ tailWord_1710040) baseStart_1710040 baseEnd_1710040 := by
    simpa [prefixWord, tailWord_1710040, baseEnd_1710040] using wordTrace_append hprefix tailTrace_1710040
  have hstable : (prefixWord ++ tailWord_1710040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710040).length < 2 ^ (prefixWord ++ tailWord_1710040).sum := by decide
  have hdescent : baseEnd_1710040 < baseStart_1710040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710064 : List Nat := [2, 1, 1, 1, 3, 2, 2, 4, 6]
def baseStart_1710064 : Nat := 118140960795 + 1710064 * 2 ^ 59
def prefixEnd_1710064 : Nat := 4983230072969 + 3 ^ 40 * 1710064 * 2
def baseEnd_1710064 : Nat := 195129951544511688985681

theorem tailTrace_1710064 : CollatzResearch.WordTrace tailWord_1710064 prefixEnd_1710064 195129951544511688985681 := by
  unfold tailWord_1710064
  simp only [CollatzResearch.WordTrace]
  refine ⟨31185579038368829262284623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41580772051158439016379497 31185579038368829262284623)
  ·
    refine ⟨46778368557553243893426935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31185579038368829262284623 46778368557553243893426935)
    ·
      refine ⟨70167552836329865840140403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46778368557553243893426935 70167552836329865840140403)
      ·
        refine ⟨105251329254494798760210605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70167552836329865840140403 105251329254494798760210605)
        ·
          refine ⟨39469248470435549535078977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105251329254494798760210605 39469248470435549535078977)
          ·
            refine ⟨29601936352826662151309233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39469248470435549535078977 29601936352826662151309233)
            ·
              refine ⟨22201452264619996613481925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29601936352826662151309233 22201452264619996613481925)
              ·
                refine ⟨4162772299616249365027861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22201452264619996613481925 4162772299616249365027861)
                ·
                  refine ⟨195129951544511688985681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4162772299616249365027861 195129951544511688985681)
                  ·
                    rfl

theorem cell22_1710064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 6].length) (baseStart_1710064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710064 prefixEnd_1710064 := by exact prefixLift 1710064
  have htrace : WordTrace (prefixWord ++ tailWord_1710064) baseStart_1710064 baseEnd_1710064 := by
    simpa [prefixWord, tailWord_1710064, baseEnd_1710064] using wordTrace_append hprefix tailTrace_1710064
  have hstable : (prefixWord ++ tailWord_1710064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710064).length < 2 ^ (prefixWord ++ tailWord_1710064).sum := by decide
  have hdescent : baseEnd_1710064 < baseStart_1710064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710113 : List Nat := [1, 2, 3, 2, 4, 1, 2, 1, 1, 5]
def baseStart_1710113 : Nat := 118140960795 + 1710113 * 2 ^ 59
def prefixEnd_1710113 : Nat := 4983230072969 + 3 ^ 40 * 1710113 * 2
def baseEnd_1710113 : Nat := 585406628334915272481893

theorem tailTrace_1710113 : CollatzResearch.WordTrace tailWord_1710113 prefixEnd_1710113 585406628334915272481893 := by
  unfold tailWord_1710113
  simp only [CollatzResearch.WordTrace]
  refine ⟨62372945253560139893102993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41581963502373426595401995 62372945253560139893102993)
  ·
    refine ⟨46779708940170104919827245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62372945253560139893102993 46779708940170104919827245)
    ·
      refine ⟨17542390852563789344935217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46779708940170104919827245 17542390852563789344935217)
      ·
        refine ⟨13156793139422842008701413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17542390852563789344935217 13156793139422842008701413)
        ·
          refine ⟨2466898713641782876631515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13156793139422842008701413 2466898713641782876631515)
          ·
            refine ⟨3700348070462674314947273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2466898713641782876631515 3700348070462674314947273)
            ·
              refine ⟨2775261052847005736210455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3700348070462674314947273 2775261052847005736210455)
              ·
                refine ⟨4162891579270508604315683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2775261052847005736210455 4162891579270508604315683)
                ·
                  refine ⟨6244337368905762906473525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4162891579270508604315683 6244337368905762906473525)
                  ·
                    refine ⟨585406628334915272481893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6244337368905762906473525 585406628334915272481893)
                    ·
                      rfl

theorem cell22_1710113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_1710113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710113 prefixEnd_1710113 := by exact prefixLift 1710113
  have htrace : WordTrace (prefixWord ++ tailWord_1710113) baseStart_1710113 baseEnd_1710113 := by
    simpa [prefixWord, tailWord_1710113, baseEnd_1710113] using wordTrace_append hprefix tailTrace_1710113
  have hstable : (prefixWord ++ tailWord_1710113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710113).length < 2 ^ (prefixWord ++ tailWord_1710113).sum := by decide
  have hdescent : baseEnd_1710113 < baseStart_1710113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710124 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 1, 9]
def baseStart_1710124 : Nat := 118140960795 + 1710124 * 2 ^ 59
def prefixEnd_1710124 : Nat := 4983230072969 + 3 ^ 40 * 1710124 * 2
def baseEnd_1710124 : Nat := 585410393859714910456859

theorem tailTrace_1710124 : CollatzResearch.WordTrace tailWord_1710124 prefixEnd_1710124 585410393859714910456859 := by
  unfold tailWord_1710124
  simp only [CollatzResearch.WordTrace]
  refine ⟨31186673228260144385876713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41582230971013525847835617 31186673228260144385876713)
  ·
    refine ⟨23390004921195108289407535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31186673228260144385876713 23390004921195108289407535)
    ·
      refine ⟨35085007381792662434111303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23390004921195108289407535 35085007381792662434111303)
      ·
        refine ⟨52627511072688993651166955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35085007381792662434111303 52627511072688993651166955)
        ·
          refine ⟨78941266609033490476750433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52627511072688993651166955 78941266609033490476750433)
          ·
            refine ⟨59205949956775117857562825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78941266609033490476750433 59205949956775117857562825)
            ·
              refine ⟨44404462467581338393172119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59205949956775117857562825 44404462467581338393172119)
              ·
                refine ⟨66606693701372007589758179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44404462467581338393172119 66606693701372007589758179)
                ·
                  refine ⟨99910040552058011384637269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66606693701372007589758179 99910040552058011384637269)
                  ·
                    refine ⟨585410393859714910456859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 99910040552058011384637269 585410393859714910456859)
                    ·
                      rfl

theorem cell22_1710124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_1710124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710124 prefixEnd_1710124 := by exact prefixLift 1710124
  have htrace : WordTrace (prefixWord ++ tailWord_1710124) baseStart_1710124 baseEnd_1710124 := by
    simpa [prefixWord, tailWord_1710124, baseEnd_1710124] using wordTrace_append hprefix tailTrace_1710124
  have hstable : (prefixWord ++ tailWord_1710124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710124).length < 2 ^ (prefixWord ++ tailWord_1710124).sum := by decide
  have hdescent : baseEnd_1710124 < baseStart_1710124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710128 : List Nat := [2, 1, 1, 1, 2, 7, 1, 1, 2, 4]
def baseStart_1710128 : Nat := 118140960795 + 1710128 * 2 ^ 59
def prefixEnd_1710128 : Nat := 4983230072969 + 3 ^ 40 * 1710128 * 2
def baseEnd_1710128 : Nat := 585411763141460233356847

theorem tailTrace_1710128 : CollatzResearch.WordTrace tailWord_1710128 prefixEnd_1710128 585411763141460233356847 := by
  unfold tailWord_1710128
  simp only [CollatzResearch.WordTrace]
  refine ⟨31186746174252898727449519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41582328232337198303266025 31186746174252898727449519)
  ·
    refine ⟨46780119261379348091174279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31186746174252898727449519 46780119261379348091174279)
    ·
      refine ⟨70170178892069022136761419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46780119261379348091174279 70170178892069022136761419)
      ·
        refine ⟨105255268338103533205142129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70170178892069022136761419 105255268338103533205142129)
        ·
          refine ⟨78941451253577649903856597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105255268338103533205142129 78941451253577649903856597)
          ·
            refine ⟨1850190263755726169621639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 78941451253577649903856597 1850190263755726169621639)
            ·
              refine ⟨2775285395633589254432459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850190263755726169621639 2775285395633589254432459)
              ·
                refine ⟨4162928093450383881648689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2775285395633589254432459 4162928093450383881648689)
                ·
                  refine ⟨3122196070087787911236517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4162928093450383881648689 3122196070087787911236517)
                  ·
                    refine ⟨585411763141460233356847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3122196070087787911236517 585411763141460233356847)
                    ·
                      rfl

theorem cell22_1710128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 2, 4].length) (baseStart_1710128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710128 prefixEnd_1710128 := by exact prefixLift 1710128
  have htrace : WordTrace (prefixWord ++ tailWord_1710128) baseStart_1710128 baseEnd_1710128 := by
    simpa [prefixWord, tailWord_1710128, baseEnd_1710128] using wordTrace_append hprefix tailTrace_1710128
  have hstable : (prefixWord ++ tailWord_1710128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710128).length < 2 ^ (prefixWord ++ tailWord_1710128).sum := by decide
  have hdescent : baseEnd_1710128 < baseStart_1710128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710132 : List Nat := [2, 5, 1, 2, 2, 1, 2, 3, 4]
def baseStart_1710132 : Nat := 118140960795 + 1710132 * 2 ^ 59
def prefixEnd_1710132 : Nat := 4983230072969 + 3 ^ 40 * 1710132 * 2
def baseEnd_1710132 : Nat := 195137710807735185418945

theorem tailTrace_1710132 : CollatzResearch.WordTrace tailWord_1710132 prefixEnd_1710132 195137710807735185418945 := by
  unfold tailWord_1710132
  simp only [CollatzResearch.WordTrace]
  refine ⟨31186819120245653069022325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41582425493660870758696433 31186819120245653069022325)
  ·
    refine ⟨2923764292523029975220843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31186819120245653069022325 2923764292523029975220843)
    ·
      refine ⟨4385646438784544962831265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2923764292523029975220843 4385646438784544962831265)
      ·
        refine ⟨3289234829088408722123449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4385646438784544962831265 3289234829088408722123449)
        ·
          refine ⟨2466926121816306541592587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3289234829088408722123449 2466926121816306541592587)
          ·
            refine ⟨3700389182724459812388881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2466926121816306541592587 3700389182724459812388881)
            ·
              refine ⟨2775291887043344859291661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3700389182724459812388881 2775291887043344859291661)
              ·
                refine ⟨1040734457641254322234373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2775291887043344859291661 1040734457641254322234373)
                ·
                  refine ⟨195137710807735185418945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1040734457641254322234373 195137710807735185418945)
                  ·
                    rfl

theorem cell22_1710132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_1710132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710132 prefixEnd_1710132 := by exact prefixLift 1710132
  have htrace : WordTrace (prefixWord ++ tailWord_1710132) baseStart_1710132 baseEnd_1710132 := by
    simpa [prefixWord, tailWord_1710132, baseEnd_1710132] using wordTrace_append hprefix tailTrace_1710132
  have hstable : (prefixWord ++ tailWord_1710132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710132).length < 2 ^ (prefixWord ++ tailWord_1710132).sum := by decide
  have hdescent : baseEnd_1710132 < baseStart_1710132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710139 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 4, 6]
def baseStart_1710139 : Nat := 118140960795 + 1710139 * 2 ^ 59
def prefixEnd_1710139 : Nat := 4983230072969 + 3 ^ 40 * 1710139 * 2
def baseEnd_1710139 : Nat := 585415528666259871331813

theorem tailTrace_1710139 : CollatzResearch.WordTrace tailWord_1710139 prefixEnd_1710139 585415528666259871331813 := by
  unfold tailWord_1710139
  simp only [CollatzResearch.WordTrace]
  refine ⟨62373893551465946333549471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41582595700977297555699647 62373893551465946333549471)
  ·
    refine ⟨93560840327198919500324207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62373893551465946333549471 93560840327198919500324207)
    ·
      refine ⟨140341260490798379250486311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93560840327198919500324207 140341260490798379250486311)
      ·
        refine ⟨210511890736197568875729467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140341260490798379250486311 210511890736197568875729467)
        ·
          refine ⟨315767836104296353313594201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210511890736197568875729467 315767836104296353313594201)
          ·
            refine ⟨236825877078222264985195651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315767836104296353313594201 236825877078222264985195651)
            ·
              refine ⟨355238815617333397477793477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236825877078222264985195651 355238815617333397477793477)
              ·
                refine ⟨66607277928250012027086277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 355238815617333397477793477 66607277928250012027086277)
                ·
                  refine ⟨12488864611546877255078677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66607277928250012027086277 12488864611546877255078677)
                  ·
                    refine ⟨585415528666259871331813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12488864611546877255078677 585415528666259871331813)
                    ·
                      rfl

theorem cell22_1710139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 6].length) (baseStart_1710139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710139 prefixEnd_1710139 := by exact prefixLift 1710139
  have htrace : WordTrace (prefixWord ++ tailWord_1710139) baseStart_1710139 baseEnd_1710139 := by
    simpa [prefixWord, tailWord_1710139, baseEnd_1710139] using wordTrace_append hprefix tailTrace_1710139
  have hstable : (prefixWord ++ tailWord_1710139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710139).length < 2 ^ (prefixWord ++ tailWord_1710139).sum := by decide
  have hdescent : baseEnd_1710139 < baseStart_1710139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710158 : List Nat := [4, 1, 1, 1, 1, 4, 1, 3, 3, 3]
def baseStart_1710158 : Nat := 118140960795 + 1710158 * 2 ^ 59
def prefixEnd_1710158 : Nat := 4983230072969 + 3 ^ 40 * 1710158 * 2
def baseEnd_1710158 : Nat := 585422032754550155106755

theorem tailTrace_1710158 : CollatzResearch.WordTrace tailWord_1710158 prefixEnd_1710158 585422032754550155106755 := by
  unfold tailWord_1710158
  simp only [CollatzResearch.WordTrace]
  refine ⟨7796823317299639072311391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41583057692264741718994085 7796823317299639072311391)
  ·
    refine ⟨11695234975949458608467087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7796823317299639072311391 11695234975949458608467087)
    ·
      refine ⟨17542852463924187912700631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11695234975949458608467087 17542852463924187912700631)
      ·
        refine ⟨26314278695886281869050947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17542852463924187912700631 26314278695886281869050947)
        ·
          refine ⟨39471418043829422803576421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26314278695886281869050947 39471418043829422803576421)
          ·
            refine ⟨7400890883218016775670579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39471418043829422803576421 7400890883218016775670579)
            ·
              refine ⟨11101336324827025163505869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7400890883218016775670579 11101336324827025163505869)
              ·
                refine ⟨4163001121810134436314701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11101336324827025163505869 4163001121810134436314701)
                ·
                  refine ⟨1561125420678800413618013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4163001121810134436314701 1561125420678800413618013)
                  ·
                    refine ⟨585422032754550155106755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1561125420678800413618013 585422032754550155106755)
                    ·
                      rfl

theorem cell22_1710158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_1710158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710158 prefixEnd_1710158 := by exact prefixLift 1710158
  have htrace : WordTrace (prefixWord ++ tailWord_1710158) baseStart_1710158 baseEnd_1710158 := by
    simpa [prefixWord, tailWord_1710158, baseEnd_1710158] using wordTrace_append hprefix tailTrace_1710158
  have hstable : (prefixWord ++ tailWord_1710158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710158).length < 2 ^ (prefixWord ++ tailWord_1710158).sum := by decide
  have hdescent : baseEnd_1710158 < baseStart_1710158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710192 : List Nat := [2, 1, 1, 1, 5, 4, 1, 3, 1, 3]
def baseStart_1710192 : Nat := 118140960795 + 1710192 * 2 ^ 59
def prefixEnd_1710192 : Nat := 4983230072969 + 3 ^ 40 * 1710192 * 2
def baseEnd_1710192 : Nat := 585433671649385399756651

theorem tailTrace_1710192 : CollatzResearch.WordTrace tailWord_1710192 prefixEnd_1710192 585433671649385399756651 := by
  unfold tailWord_1710192
  simp only [CollatzResearch.WordTrace]
  refine ⟨31187913310136968192614415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41583884413515957590152553 31187913310136968192614415)
  ·
    refine ⟨46781869965205452288921623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31187913310136968192614415 46781869965205452288921623)
    ·
      refine ⟨70172804947808178433382435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46781869965205452288921623 70172804947808178433382435)
      ·
        refine ⟨105259207421712267650073653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70172804947808178433382435 105259207421712267650073653)
        ·
          refine ⟨9868050695785525092194405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105259207421712267650073653 9868050695785525092194405)
          ·
            refine ⟨1850259505459785954786451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9868050695785525092194405 1850259505459785954786451)
            ·
              refine ⟨2775389258189678932179677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850259505459785954786451 2775389258189678932179677)
              ·
                refine ⟨1040770971821129599567379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2775389258189678932179677 1040770971821129599567379)
                ·
                  refine ⟨1561156457731694399351069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1040770971821129599567379 1561156457731694399351069)
                  ·
                    refine ⟨585433671649385399756651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1561156457731694399351069 585433671649385399756651)
                    ·
                      rfl

theorem cell22_1710192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 1, 3].length) (baseStart_1710192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710192 prefixEnd_1710192 := by exact prefixLift 1710192
  have htrace : WordTrace (prefixWord ++ tailWord_1710192) baseStart_1710192 baseEnd_1710192 := by
    simpa [prefixWord, tailWord_1710192, baseEnd_1710192] using wordTrace_append hprefix tailTrace_1710192
  have hstable : (prefixWord ++ tailWord_1710192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710192).length < 2 ^ (prefixWord ++ tailWord_1710192).sum := by decide
  have hdescent : baseEnd_1710192 < baseStart_1710192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710209 : List Nat := [1, 2, 4, 2, 3, 1, 3, 2, 1, 3]
def baseStart_1710209 : Nat := 118140960795 + 1710209 * 2 ^ 59
def prefixEnd_1710209 : Nat := 4983230072969 + 3 ^ 40 * 1710209 * 2
def baseEnd_1710209 : Nat := 585439491096803022081599

theorem tailTrace_1710209 : CollatzResearch.WordTrace tailWord_1710209 prefixEnd_1710209 585439491096803022081599 := by
  unfold tailWord_1710209
  simp only [CollatzResearch.WordTrace]
  refine ⟨62376446661212348288597681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41584297774141565525731787 62376446661212348288597681)
  ·
    refine ⟨46782334995909261216448261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62376446661212348288597681 46782334995909261216448261)
    ·
      refine ⟨8771687811732986478084049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46782334995909261216448261 8771687811732986478084049)
      ·
        refine ⟨6578765858799739858563037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8771687811732986478084049 6578765858799739858563037)
        ·
          refine ⟨2467037197049902446961139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6578765858799739858563037 2467037197049902446961139)
          ·
            refine ⟨3700555795574853670441709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2467037197049902446961139 3700555795574853670441709)
            ·
              refine ⟨1387708423340570126415641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3700555795574853670441709 1387708423340570126415641)
              ·
                refine ⟨1040781317505427594811731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1387708423340570126415641 1040781317505427594811731)
                ·
                  refine ⟨1561171976258141392217597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1040781317505427594811731 1561171976258141392217597)
                  ·
                    refine ⟨585439491096803022081599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1561171976258141392217597 585439491096803022081599)
                    ·
                      rfl

theorem cell22_1710209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_1710209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710209 prefixEnd_1710209 := by exact prefixLift 1710209
  have htrace : WordTrace (prefixWord ++ tailWord_1710209) baseStart_1710209 baseEnd_1710209 := by
    simpa [prefixWord, tailWord_1710209, baseEnd_1710209] using wordTrace_append hprefix tailTrace_1710209
  have hstable : (prefixWord ++ tailWord_1710209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710209).length < 2 ^ (prefixWord ++ tailWord_1710209).sum := by decide
  have hdescent : baseEnd_1710209 < baseStart_1710209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710222 : List Nat := [4, 1, 1, 3, 3, 2, 2, 1, 5]
def baseStart_1710222 : Nat := 118140960795 + 1710222 * 2 ^ 59
def prefixEnd_1710222 : Nat := 4983230072969 + 3 ^ 40 * 1710222 * 2
def baseEnd_1710222 : Nat := 195147980420825107168853

theorem tailTrace_1710222 : CollatzResearch.WordTrace tailWord_1710222 prefixEnd_1710222 195147980420825107168853 := by
  unfold tailWord_1710222
  simp only [CollatzResearch.WordTrace]
  refine ⟨7797115101270656438602615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41584613873443501005880613 7797115101270656438602615)
  ·
    refine ⟨11695672651905984657903923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7797115101270656438602615 11695672651905984657903923)
    ·
      refine ⟨17543508977858976986855885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11695672651905984657903923 17543508977858976986855885)
      ·
        refine ⟨6578815866697116370070957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17543508977858976986855885 6578815866697116370070957)
        ·
          refine ⟨2467055950011418638776609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6578815866697116370070957 2467055950011418638776609)
          ·
            refine ⟨1850291962508563979082457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2467055950011418638776609 1850291962508563979082457)
            ·
              refine ⟨1387718971881422984311843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1850291962508563979082457 1387718971881422984311843)
              ·
                refine ⟨2081578457822134476467765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1387718971881422984311843 2081578457822134476467765)
                ·
                  refine ⟨195147980420825107168853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2081578457822134476467765 195147980420825107168853)
                  ·
                    rfl

theorem cell22_1710222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_1710222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710222 prefixEnd_1710222 := by exact prefixLift 1710222
  have htrace : WordTrace (prefixWord ++ tailWord_1710222) baseStart_1710222 baseEnd_1710222 := by
    simpa [prefixWord, tailWord_1710222, baseEnd_1710222] using wordTrace_append hprefix tailTrace_1710222
  have hstable : (prefixWord ++ tailWord_1710222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710222).length < 2 ^ (prefixWord ++ tailWord_1710222).sum := by decide
  have hdescent : baseEnd_1710222 < baseStart_1710222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710260 : List Nat := [2, 5, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_1710260 : Nat := 118140960795 + 1710260 * 2 ^ 59
def prefixEnd_1710260 : Nat := 4983230072969 + 3 ^ 40 * 1710260 * 2
def baseEnd_1710260 : Nat := 585456949439055889056443

theorem tailTrace_1710260 : CollatzResearch.WordTrace tailWord_1710260 prefixEnd_1710260 585456949439055889056443 := by
  unfold tailWord_1710260
  simp only [CollatzResearch.WordTrace]
  refine ⟨31189153392013791999352117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41585537856018389332469489 31189153392013791999352117)
  ·
    refine ⟨2923983130501292999939261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31189153392013791999352117 2923983130501292999939261)
    ·
      refine ⟨1096493673937984874977223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2923983130501292999939261 1096493673937984874977223)
      ·
        refine ⟨1644740510906977312465835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1096493673937984874977223 1644740510906977312465835)
        ·
          refine ⟨2467110766360465968698753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1644740510906977312465835 2467110766360465968698753)
          ·
            refine ⟨1850333074770349476524065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2467110766360465968698753 1850333074770349476524065)
            ·
              refine ⟨1387749806077762107393049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1850333074770349476524065 1387749806077762107393049)
              ·
                refine ⟨1040812354558321580544787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1387749806077762107393049 1040812354558321580544787)
                ·
                  refine ⟨1561218531837482370817181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1040812354558321580544787 1561218531837482370817181)
                  ·
                    refine ⟨585456949439055889056443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1561218531837482370817181 585456949439055889056443)
                    ·
                      rfl

theorem cell22_1710260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_1710260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710260 prefixEnd_1710260 := by exact prefixLift 1710260
  have htrace : WordTrace (prefixWord ++ tailWord_1710260) baseStart_1710260 baseEnd_1710260 := by
    simpa [prefixWord, tailWord_1710260, baseEnd_1710260] using wordTrace_append hprefix tailTrace_1710260
  have hstable : (prefixWord ++ tailWord_1710260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710260).length < 2 ^ (prefixWord ++ tailWord_1710260).sum := by decide
  have hdescent : baseEnd_1710260 < baseStart_1710260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710263 : List Nat := [1, 1, 3, 1, 4, 2, 2, 2, 2, 4]
def baseStart_1710263 : Nat := 118140960795 + 1710263 * 2 ^ 59
def prefixEnd_1710263 : Nat := 4983230072969 + 3 ^ 40 * 1710263 * 2
def baseEnd_1710263 : Nat := 585457976400364881231433

theorem tailTrace_1710263 : CollatzResearch.WordTrace tailWord_1710263 prefixEnd_1710263 585457976400364881231433 := by
  unfold tailWord_1710263
  simp only [CollatzResearch.WordTrace]
  refine ⟨62378416203016715511063443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41585610802011143674042295 62378416203016715511063443)
  ·
    refine ⟨93567624304525073266595165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62378416203016715511063443 93567624304525073266595165)
    ·
      refine ⟨35087859114196902474973187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93567624304525073266595165 35087859114196902474973187)
      ·
        refine ⟨52631788671295353712459781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35087859114196902474973187 52631788671295353712459781)
        ·
          refine ⟨9868460375867878821086209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52631788671295353712459781 9868460375867878821086209)
          ·
            refine ⟨7401345281900909115814657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9868460375867878821086209 7401345281900909115814657)
            ·
              refine ⟨5551008961425681836860993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7401345281900909115814657 5551008961425681836860993)
              ·
                refine ⟨4163256721069261377645745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5551008961425681836860993 4163256721069261377645745)
                ·
                  refine ⟨3122442540801946033234309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4163256721069261377645745 3122442540801946033234309)
                  ·
                    refine ⟨585457976400364881231433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3122442540801946033234309 585457976400364881231433)
                    ·
                      rfl

theorem cell22_1710263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_1710263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710263 prefixEnd_1710263 := by exact prefixLift 1710263
  have htrace : WordTrace (prefixWord ++ tailWord_1710263) baseStart_1710263 baseEnd_1710263 := by
    simpa [prefixWord, tailWord_1710263, baseEnd_1710263] using wordTrace_append hprefix tailTrace_1710263
  have hstable : (prefixWord ++ tailWord_1710263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710263).length < 2 ^ (prefixWord ++ tailWord_1710263).sum := by decide
  have hdescent : baseEnd_1710263 < baseStart_1710263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710265 : List Nat := [1, 2, 1, 4, 1, 2, 4, 2, 2, 3]
def baseStart_1710265 : Nat := 118140960795 + 1710265 * 2 ^ 59
def prefixEnd_1710265 : Nat := 4983230072969 + 3 ^ 40 * 1710265 * 2
def baseEnd_1710265 : Nat := 585458661041237542681427

theorem tailTrace_1710265 : CollatzResearch.WordTrace tailWord_1710265 prefixEnd_1710265 585458661041237542681427 := by
  unfold tailWord_1710265
  simp only [CollatzResearch.WordTrace]
  refine ⟨62378489149009469852636249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41585659432672979901757499 62378489149009469852636249)
  ·
    refine ⟨46783866861757102389477187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62378489149009469852636249 46783866861757102389477187)
    ·
      refine ⟨70175800292635653584215781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46783866861757102389477187 70175800292635653584215781)
      ·
        refine ⟨13157962554869185047040459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70175800292635653584215781 13157962554869185047040459)
        ·
          refine ⟨19736943832303777570560689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13157962554869185047040459 19736943832303777570560689)
          ·
            refine ⟨14802707874227833177920517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19736943832303777570560689 14802707874227833177920517)
            ·
              refine ⟨2775507726417718720860097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14802707874227833177920517 2775507726417718720860097)
              ·
                refine ⟨2081630794813289040645073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2775507726417718720860097 2081630794813289040645073)
                ·
                  refine ⟨1561223096109966780483805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2081630794813289040645073 1561223096109966780483805)
                  ·
                    refine ⟨585458661041237542681427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1561223096109966780483805 585458661041237542681427)
                    ·
                      rfl

theorem cell22_1710265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 3].length) (baseStart_1710265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710265 prefixEnd_1710265 := by exact prefixLift 1710265
  have htrace : WordTrace (prefixWord ++ tailWord_1710265) baseStart_1710265 baseEnd_1710265 := by
    simpa [prefixWord, tailWord_1710265, baseEnd_1710265] using wordTrace_append hprefix tailTrace_1710265
  have hstable : (prefixWord ++ tailWord_1710265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710265).length < 2 ^ (prefixWord ++ tailWord_1710265).sum := by decide
  have hdescent : baseEnd_1710265 < baseStart_1710265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710434 : List Nat := [3, 3, 2, 1, 1, 3, 2, 2, 2, 3]
def baseStart_1710434 : Nat := 118140960795 + 1710434 * 2 ^ 59
def prefixEnd_1710434 : Nat := 4983230072969 + 3 ^ 40 * 1710434 * 2
def baseEnd_1710434 : Nat := 585516513194977435205909

theorem tailTrace_1710434 : CollatzResearch.WordTrace tailWord_1710434 prefixEnd_1710434 585516513194977435205909 := by
  unfold tailWord_1710434
  simp only [CollatzResearch.WordTrace]
  refine ⟨15596163271349302928884589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41589768723598141143692237 15596163271349302928884589)
  ·
    refine ⟨5848561226755988598331721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15596163271349302928884589 5848561226755988598331721)
    ·
      refine ⟨4386420920066991448748791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5848561226755988598331721 4386420920066991448748791)
      ·
        refine ⟨6579631380100487173123187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4386420920066991448748791 6579631380100487173123187)
        ·
          refine ⟨9869447070150730759684781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6579631380100487173123187 9869447070150730759684781)
          ·
            refine ⟨3701042651306524034881793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9869447070150730759684781 3701042651306524034881793)
            ·
              refine ⟨2775781988479893026161345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3701042651306524034881793 2775781988479893026161345)
              ·
                refine ⟨2081836491359919769621009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2775781988479893026161345 2081836491359919769621009)
                ·
                  refine ⟨1561377368519939827215757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2081836491359919769621009 1561377368519939827215757)
                  ·
                    refine ⟨585516513194977435205909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1561377368519939827215757 585516513194977435205909)
                    ·
                      rfl

theorem cell22_1710434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_1710434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710434 prefixEnd_1710434 := by exact prefixLift 1710434
  have htrace : WordTrace (prefixWord ++ tailWord_1710434) baseStart_1710434 baseEnd_1710434 := by
    simpa [prefixWord, tailWord_1710434, baseEnd_1710434] using wordTrace_append hprefix tailTrace_1710434
  have hstable : (prefixWord ++ tailWord_1710434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710434).length < 2 ^ (prefixWord ++ tailWord_1710434).sum := by decide
  have hdescent : baseEnd_1710434 < baseStart_1710434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710466 : List Nat := [3, 4, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_1710466 : Nat := 118140960795 + 1710466 * 2 ^ 59
def prefixEnd_1710466 : Nat := 4983230072969 + 3 ^ 40 * 1710466 * 2
def baseEnd_1710466 : Nat := 585527467448940018405811

theorem tailTrace_1710466 : CollatzResearch.WordTrace tailWord_1710466 prefixEnd_1710466 585527467448940018405811 := by
  unfold tailWord_1710466
  simp only [CollatzResearch.WordTrace]
  refine ⟨15596455055320320295175813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41590546814187520787135501 15596455055320320295175813)
  ·
    refine ⟨2924335322872560055345465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15596455055320320295175813 2924335322872560055345465)
    ·
      refine ⟨2193251492154420041509099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2924335322872560055345465 2193251492154420041509099)
      ·
        refine ⟨3289877238231630062263649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2193251492154420041509099 3289877238231630062263649)
        ·
          refine ⟨2467407928673722546697737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3289877238231630062263649 2467407928673722546697737)
          ·
            refine ⟨1850555946505291910023303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2467407928673722546697737 1850555946505291910023303)
            ·
              refine ⟨2775833919757937865034955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850555946505291910023303 2775833919757937865034955)
              ·
                refine ⟨4163750879636906797552433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2775833919757937865034955 4163750879636906797552433)
                ·
                  refine ⟨3122813159727680098164325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4163750879636906797552433 3122813159727680098164325)
                  ·
                    refine ⟨585527467448940018405811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3122813159727680098164325 585527467448940018405811)
                    ·
                      rfl

theorem cell22_1710466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_1710466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710466 prefixEnd_1710466 := by exact prefixLift 1710466
  have htrace : WordTrace (prefixWord ++ tailWord_1710466) baseStart_1710466 baseEnd_1710466 := by
    simpa [prefixWord, tailWord_1710466, baseEnd_1710466] using wordTrace_append hprefix tailTrace_1710466
  have hstable : (prefixWord ++ tailWord_1710466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710466).length < 2 ^ (prefixWord ++ tailWord_1710466).sum := by decide
  have hdescent : baseEnd_1710466 < baseStart_1710466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710490 : List Nat := [3, 1, 1, 4, 1, 2, 1, 2, 2, 5]
def baseStart_1710490 : Nat := 118140960795 + 1710490 * 2 ^ 59
def prefixEnd_1710490 : Nat := 4983230072969 + 3 ^ 40 * 1710490 * 2
def baseEnd_1710490 : Nat := 585535683139411955805737

theorem tailTrace_1710490 : CollatzResearch.WordTrace tailWord_1710490 prefixEnd_1710490 585535683139411955805737 := by
  unfold tailWord_1710490
  simp only [CollatzResearch.WordTrace]
  refine ⟨15596673893298583319894231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41591130382129555519717949 15596673893298583319894231)
  ·
    refine ⟨23395010839947874979841347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15596673893298583319894231 23395010839947874979841347)
    ·
      refine ⟨35092516259921812469762021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23395010839947874979841347 35092516259921812469762021)
      ·
        refine ⟨6579846798735339838080379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35092516259921812469762021 6579846798735339838080379)
        ·
          refine ⟨9869770198103009757120569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6579846798735339838080379 9869770198103009757120569)
          ·
            refine ⟨7402327648577257317840427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9869770198103009757120569 7402327648577257317840427)
            ·
              refine ⟨11103491472865885976760641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7402327648577257317840427 11103491472865885976760641)
              ·
                refine ⟨8327618604649414482570481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11103491472865885976760641 8327618604649414482570481)
                ·
                  refine ⟨6245713953487060861927861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8327618604649414482570481 6245713953487060861927861)
                  ·
                    refine ⟨585535683139411955805737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6245713953487060861927861 585535683139411955805737)
                    ·
                      rfl

theorem cell22_1710490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_1710490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710490 prefixEnd_1710490 := by exact prefixLift 1710490
  have htrace : WordTrace (prefixWord ++ tailWord_1710490) baseStart_1710490 baseEnd_1710490 := by
    simpa [prefixWord, tailWord_1710490, baseEnd_1710490] using wordTrace_append hprefix tailTrace_1710490
  have hstable : (prefixWord ++ tailWord_1710490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710490).length < 2 ^ (prefixWord ++ tailWord_1710490).sum := by decide
  have hdescent : baseEnd_1710490 < baseStart_1710490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710537 : List Nat := [1, 2, 1, 1, 2, 1, 7, 3, 4]
def baseStart_1710537 : Nat := 118140960795 + 1710537 * 2 ^ 59
def prefixEnd_1710537 : Nat := 4983230072969 + 3 ^ 40 * 1710537 * 2
def baseEnd_1710537 : Nat := 195183924066639833293531

theorem tailTrace_1710537 : CollatzResearch.WordTrace tailWord_1710537 prefixEnd_1710537 195183924066639833293531 := by
  unfold tailWord_1710537
  simp only [CollatzResearch.WordTrace]
  refine ⟨62388409804024060306537865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41592273202682706871025243 62388409804024060306537865)
  ·
    refine ⟨46791307353018045229903399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62388409804024060306537865 46791307353018045229903399)
    ·
      refine ⟨70186961029527067844855099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46791307353018045229903399 70186961029527067844855099)
      ·
        refine ⟨105280441544290601767282649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70186961029527067844855099 105280441544290601767282649)
        ·
          refine ⟨78960331158217951325461987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105280441544290601767282649 78960331158217951325461987)
          ·
            refine ⟨118440496737326926988192981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78960331158217951325461987 118440496737326926988192981)
            ·
              refine ⟨2775949142281099851285773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 118440496737326926988192981 2775949142281099851285773)
              ·
                refine ⟨1040980928355412444232165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2775949142281099851285773 1040980928355412444232165)
                ·
                  refine ⟨195183924066639833293531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1040980928355412444232165 195183924066639833293531)
                  ·
                    rfl

theorem cell22_1710537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 4].length) (baseStart_1710537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710537 prefixEnd_1710537 := by exact prefixLift 1710537
  have htrace : WordTrace (prefixWord ++ tailWord_1710537) baseStart_1710537 baseEnd_1710537 := by
    simpa [prefixWord, tailWord_1710537, baseEnd_1710537] using wordTrace_append hprefix tailTrace_1710537
  have hstable : (prefixWord ++ tailWord_1710537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710537).length < 2 ^ (prefixWord ++ tailWord_1710537).sum := by decide
  have hdescent : baseEnd_1710537 < baseStart_1710537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710552 : List Nat := [2, 1, 2, 2, 2, 1, 1, 6, 2, 3]
def baseStart_1710552 : Nat := 118140960795 + 1710552 * 2 ^ 59
def prefixEnd_1710552 : Nat := 4983230072969 + 3 ^ 40 * 1710552 * 2
def baseEnd_1710552 : Nat := 585556907006464460755547

theorem tailTrace_1710552 : CollatzResearch.WordTrace tailWord_1710552 prefixEnd_1710552 585556907006464460755547 := by
  unfold tailWord_1710552
  simp only [CollatzResearch.WordTrace]
  refine ⟨31194478449484858934166955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41592637932646478578889273 31194478449484858934166955)
  ·
    refine ⟨46791717674227288401250433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31194478449484858934166955 46791717674227288401250433)
    ·
      refine ⟨35093788255670466300937825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46791717674227288401250433 35093788255670466300937825)
      ·
        refine ⟨26320341191752849725703369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35093788255670466300937825 26320341191752849725703369)
        ·
          refine ⟨19740255893814637294277527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26320341191752849725703369 19740255893814637294277527)
          ·
            refine ⟨29610383840721955941416291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19740255893814637294277527 29610383840721955941416291)
            ·
              refine ⟨44415575761082933912124437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29610383840721955941416291 44415575761082933912124437)
              ·
                refine ⟨2081980113800762527130833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44415575761082933912124437 2081980113800762527130833)
                ·
                  refine ⟨1561485085350571895348125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2081980113800762527130833 1561485085350571895348125)
                  ·
                    refine ⟨585556907006464460755547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1561485085350571895348125 585556907006464460755547)
                    ·
                      rfl

theorem cell22_1710552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 2, 3].length) (baseStart_1710552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710552 prefixEnd_1710552 := by exact prefixLift 1710552
  have htrace : WordTrace (prefixWord ++ tailWord_1710552) baseStart_1710552 baseEnd_1710552 := by
    simpa [prefixWord, tailWord_1710552, baseEnd_1710552] using wordTrace_append hprefix tailTrace_1710552
  have hstable : (prefixWord ++ tailWord_1710552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710552).length < 2 ^ (prefixWord ++ tailWord_1710552).sum := by decide
  have hdescent : baseEnd_1710552 < baseStart_1710552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710554 : List Nat := [3, 1, 1, 2, 3, 1, 5, 2, 4]
def baseStart_1710554 : Nat := 118140960795 + 1710554 * 2 ^ 59
def prefixEnd_1710554 : Nat := 4983230072969 + 3 ^ 40 * 1710554 * 2
def baseEnd_1710554 : Nat := 195185863882445707401847

theorem tailTrace_1710554 : CollatzResearch.WordTrace tailWord_1710554 prefixEnd_1710554 195185863882445707401847 := by
  unfold tailWord_1710554
  simp only [CollatzResearch.WordTrace]
  refine ⟨15597257461240618052476679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41592686563308314806604477 15597257461240618052476679)
  ·
    refine ⟨23395886191860927078715019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15597257461240618052476679 23395886191860927078715019)
    ·
      refine ⟨35093829287791390618072529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23395886191860927078715019 35093829287791390618072529)
      ·
        refine ⟨26320371965843542963554397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35093829287791390618072529 26320371965843542963554397)
        ·
          refine ⟨9870139487191328611332899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26320371965843542963554397 9870139487191328611332899)
          ·
            refine ⟨14805209230786992916999349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9870139487191328611332899 14805209230786992916999349)
            ·
              refine ⟨1387988365386280585968689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14805209230786992916999349 1387988365386280585968689)
              ·
                refine ⟨1040991274039710439476517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1387988365386280585968689 1040991274039710439476517)
                ·
                  refine ⟨195185863882445707401847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1040991274039710439476517 195185863882445707401847)
                  ·
                    rfl

theorem cell22_1710554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 4].length) (baseStart_1710554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710554 prefixEnd_1710554 := by exact prefixLift 1710554
  have htrace : WordTrace (prefixWord ++ tailWord_1710554) baseStart_1710554 baseEnd_1710554 := by
    simpa [prefixWord, tailWord_1710554, baseEnd_1710554] using wordTrace_append hprefix tailTrace_1710554
  have hstable : (prefixWord ++ tailWord_1710554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710554).length < 2 ^ (prefixWord ++ tailWord_1710554).sum := by decide
  have hdescent : baseEnd_1710554 < baseStart_1710554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710605 : List Nat := [1, 7, 1, 1, 1, 3, 2, 2, 4]
def baseStart_1710605 : Nat := 118140960795 + 1710605 * 2 ^ 59
def prefixEnd_1710605 : Nat := 4983230072969 + 3 ^ 40 * 1710605 * 2
def baseEnd_1710605 : Nat := 195191683329863329726795

theorem tailTrace_1710605 : CollatzResearch.WordTrace tailWord_1710605 prefixEnd_1710605 195191683329863329726795 := by
  unfold tailWord_1710605
  simp only [CollatzResearch.WordTrace]
  refine ⟨62390889967777707920013269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41593926645185138613342179 62390889967777707920013269)
  ·
    refine ⟨1462286483619790029375311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 62390889967777707920013269 1462286483619790029375311)
    ·
      refine ⟨2193429725429685044062967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1462286483619790029375311 2193429725429685044062967)
      ·
        refine ⟨3290144588144527566094451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2193429725429685044062967 3290144588144527566094451)
        ·
          refine ⟨4935216882216791349141677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3290144588144527566094451 4935216882216791349141677)
          ·
            refine ⟨1850706330831296755928129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4935216882216791349141677 1850706330831296755928129)
            ·
              refine ⟨1388029748123472566946097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1850706330831296755928129 1388029748123472566946097)
              ·
                refine ⟨1041022311092604425209573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1388029748123472566946097 1041022311092604425209573)
                ·
                  refine ⟨195191683329863329726795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1041022311092604425209573 195191683329863329726795)
                  ·
                    rfl

theorem cell22_1710605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_1710605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710605 prefixEnd_1710605 := by exact prefixLift 1710605
  have htrace : WordTrace (prefixWord ++ tailWord_1710605) baseStart_1710605 baseEnd_1710605 := by
    simpa [prefixWord, tailWord_1710605, baseEnd_1710605] using wordTrace_append hprefix tailTrace_1710605
  have hstable : (prefixWord ++ tailWord_1710605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710605).length < 2 ^ (prefixWord ++ tailWord_1710605).sum := by decide
  have hdescent : baseEnd_1710605 < baseStart_1710605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710627 : List Nat := [1, 1, 1, 4, 4, 1, 2, 3, 5]
def baseStart_1710627 : Nat := 118140960795 + 1710627 * 2 ^ 59
def prefixEnd_1710627 : Nat := 4983230072969 + 3 ^ 40 * 1710627 * 2
def baseEnd_1710627 : Nat := 195194193679729755043439

theorem tailTrace_1710627 : CollatzResearch.WordTrace tailWord_1710627 prefixEnd_1710627 195194193679729755043439 := by
  unfold tailWord_1710627
  simp only [CollatzResearch.WordTrace]
  refine ⟨62391692373698005677314135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41594461582465337118209423 62391692373698005677314135)
  ·
    refine ⟨93587538560547008515971203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62391692373698005677314135 93587538560547008515971203)
    ·
      refine ⟨140381307840820512773956805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93587538560547008515971203 140381307840820512773956805)
      ·
        refine ⟨26321495220153846145116901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140381307840820512773956805 26321495220153846145116901)
        ·
          refine ⟨4935280353778846152209419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26321495220153846145116901 4935280353778846152209419)
          ·
            refine ⟨7402920530668269228314129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4935280353778846152209419 7402920530668269228314129)
            ·
              refine ⟨5552190398001201921235597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7402920530668269228314129 5552190398001201921235597)
              ·
                refine ⟨2082071399250450720463349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5552190398001201921235597 2082071399250450720463349)
                ·
                  refine ⟨195194193679729755043439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2082071399250450720463349 195194193679729755043439)
                  ·
                    rfl

theorem cell22_1710627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 5].length) (baseStart_1710627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710627 prefixEnd_1710627 := by exact prefixLift 1710627
  have htrace : WordTrace (prefixWord ++ tailWord_1710627) baseStart_1710627 baseEnd_1710627 := by
    simpa [prefixWord, tailWord_1710627, baseEnd_1710627] using wordTrace_append hprefix tailTrace_1710627
  have hstable : (prefixWord ++ tailWord_1710627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710627).length < 2 ^ (prefixWord ++ tailWord_1710627).sum := by decide
  have hdescent : baseEnd_1710627 < baseStart_1710627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710655 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 8]
def baseStart_1710655 : Nat := 118140960795 + 1710655 * 2 ^ 59
def prefixEnd_1710655 : Nat := 4983230072969 + 3 ^ 40 * 1710655 * 2
def baseEnd_1710655 : Nat := 195197388670468841810077

theorem tailTrace_1710655 : CollatzResearch.WordTrace tailWord_1710655 prefixEnd_1710655 195197388670468841810077 := by
  unfold tailWord_1710655
  simp only [CollatzResearch.WordTrace]
  refine ⟨62392713617596566459333419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41595142411731044306222279 62392713617596566459333419)
  ·
    refine ⟨93589070426394849689000129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62392713617596566459333419 93589070426394849689000129)
    ·
      refine ⟨70191802819796137266750097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93589070426394849689000129 70191802819796137266750097)
      ·
        refine ⟨52643852114847102950062573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70191802819796137266750097 52643852114847102950062573)
        ·
          refine ⟨19741444543067663606273465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52643852114847102950062573 19741444543067663606273465)
          ·
            refine ⟨14806083407300747704705099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19741444543067663606273465 14806083407300747704705099)
            ·
              refine ⟨22209125110951121557057649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14806083407300747704705099 22209125110951121557057649)
              ·
                refine ⟨16656843833213341167793237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22209125110951121557057649 16656843833213341167793237)
                ·
                  refine ⟨195197388670468841810077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16656843833213341167793237 195197388670468841810077)
                  ·
                    rfl

theorem cell22_1710655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 8].length) (baseStart_1710655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710655 prefixEnd_1710655 := by exact prefixLift 1710655
  have htrace : WordTrace (prefixWord ++ tailWord_1710655) baseStart_1710655 baseEnd_1710655 := by
    simpa [prefixWord, tailWord_1710655, baseEnd_1710655] using wordTrace_append hprefix tailTrace_1710655
  have hstable : (prefixWord ++ tailWord_1710655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710655).length < 2 ^ (prefixWord ++ tailWord_1710655).sum := by decide
  have hdescent : baseEnd_1710655 < baseStart_1710655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710738 : List Nat := [3, 2, 3, 1, 2, 1, 4, 1, 2, 3]
def baseStart_1710738 : Nat := 118140960795 + 1710738 * 2 ^ 59
def prefixEnd_1710738 : Nat := 4983230072969 + 3 ^ 40 * 1710738 * 2
def baseEnd_1710738 : Nat := 585620578607621975604977

theorem tailTrace_1710738 : CollatzResearch.WordTrace tailWord_1710738 prefixEnd_1710738 585620578607621975604977 := by
  unfold tailWord_1710738
  simp only [CollatzResearch.WordTrace]
  refine ⟨15598935219073967908651217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41597160584197247756403245 15598935219073967908651217)
  ·
    refine ⟨11699201414305475931488413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15598935219073967908651217 11699201414305475931488413)
    ·
      refine ⟨4387200530364553474308155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11699201414305475931488413 4387200530364553474308155)
      ·
        refine ⟨6580800795546830211462233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4387200530364553474308155 6580800795546830211462233)
        ·
          refine ⟨4935600596660122658596675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6580800795546830211462233 4935600596660122658596675)
          ·
            refine ⟨7403400894990183987895013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4935600596660122658596675 7403400894990183987895013)
            ·
              refine ⟨1388137667810659497730315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7403400894990183987895013 1388137667810659497730315)
              ·
                refine ⟨2082206501715989246595473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1388137667810659497730315 2082206501715989246595473)
                ·
                  refine ⟨1561654876286991934946605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2082206501715989246595473 1561654876286991934946605)
                  ·
                    refine ⟨585620578607621975604977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1561654876286991934946605 585620578607621975604977)
                    ·
                      rfl

theorem cell22_1710738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_1710738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710738 prefixEnd_1710738 := by exact prefixLift 1710738
  have htrace : WordTrace (prefixWord ++ tailWord_1710738) baseStart_1710738 baseEnd_1710738 := by
    simpa [prefixWord, tailWord_1710738, baseEnd_1710738] using wordTrace_append hprefix tailTrace_1710738
  have hstable : (prefixWord ++ tailWord_1710738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710738).length < 2 ^ (prefixWord ++ tailWord_1710738).sum := by decide
  have hdescent : baseEnd_1710738 < baseStart_1710738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710749 : List Nat := [1, 4, 2, 1, 1, 1, 2, 4, 3, 3]
def baseStart_1710749 : Nat := 118140960795 + 1710749 * 2 ^ 59
def prefixEnd_1710749 : Nat := 4983230072969 + 3 ^ 40 * 1710749 * 2
def baseEnd_1710749 : Nat := 585624344132421613579943

theorem tailTrace_1710749 : CollatzResearch.WordTrace tailWord_1710749 prefixEnd_1710749 585624344132421613579943 := by
  unfold tailWord_1710749
  simp only [CollatzResearch.WordTrace]
  refine ⟨62396142079256020513255301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41597428052837347008836867 62396142079256020513255301)
  ·
    refine ⟨11699276639860503846235369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62396142079256020513255301 11699276639860503846235369)
    ·
      refine ⟨8774457479895377884676527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11699276639860503846235369 8774457479895377884676527)
      ·
        refine ⟨13161686219843066827014791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8774457479895377884676527 13161686219843066827014791)
        ·
          refine ⟨19742529329764600240522187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13161686219843066827014791 19742529329764600240522187)
          ·
            refine ⟨29613793994646900360783281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19742529329764600240522187 29613793994646900360783281)
            ·
              refine ⟨22210345495985175270587461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29613793994646900360783281 22210345495985175270587461)
              ·
                refine ⟨4164439780497220363235149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22210345495985175270587461 4164439780497220363235149)
                ·
                  refine ⟨1561664917686457636213181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4164439780497220363235149 1561664917686457636213181)
                  ·
                    refine ⟨585624344132421613579943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1561664917686457636213181 585624344132421613579943)
                    ·
                      rfl

theorem cell22_1710749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_1710749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710749 prefixEnd_1710749 := by exact prefixLift 1710749
  have htrace : WordTrace (prefixWord ++ tailWord_1710749) baseStart_1710749 baseEnd_1710749 := by
    simpa [prefixWord, tailWord_1710749, baseEnd_1710749] using wordTrace_append hprefix tailTrace_1710749
  have hstable : (prefixWord ++ tailWord_1710749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710749).length < 2 ^ (prefixWord ++ tailWord_1710749).sum := by decide
  have hdescent : baseEnd_1710749 < baseStart_1710749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710777 : List Nat := [1, 2, 1, 4, 1, 1, 1, 4, 2, 5]
def baseStart_1710777 : Nat := 118140960795 + 1710777 * 2 ^ 59
def prefixEnd_1710777 : Nat := 4983230072969 + 3 ^ 40 * 1710777 * 2
def baseEnd_1710777 : Nat := 585633929104638873879857

theorem tailTrace_1710777 : CollatzResearch.WordTrace tailWord_1710777 prefixEnd_1710777 585633929104638873879857 := by
  unfold tailWord_1710777
  simp only [CollatzResearch.WordTrace]
  refine ⟨62397163323154581295274585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41598108882103054196849723 62397163323154581295274585)
  ·
    refine ⟨46797872492365935971455939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62397163323154581295274585 46797872492365935971455939)
    ·
      refine ⟨70196808738548903957183909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46797872492365935971455939 70196808738548903957183909)
      ·
        refine ⟨13161901638477919491971983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70196808738548903957183909 13161901638477919491971983)
        ·
          refine ⟨19742852457716879237957975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13161901638477919491971983 19742852457716879237957975)
          ·
            refine ⟨29614278686575318856936963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19742852457716879237957975 29614278686575318856936963)
            ·
              refine ⟨44421418029862978285405445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29614278686575318856936963 44421418029862978285405445)
              ·
                refine ⟨8329015880599308428513521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44421418029862978285405445 8329015880599308428513521)
                ·
                  refine ⟨6246761910449481321385141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8329015880599308428513521 6246761910449481321385141)
                  ·
                    refine ⟨585633929104638873879857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6246761910449481321385141 585633929104638873879857)
                    ·
                      rfl

theorem cell22_1710777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 5].length) (baseStart_1710777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710777 prefixEnd_1710777 := by exact prefixLift 1710777
  have htrace : WordTrace (prefixWord ++ tailWord_1710777) baseStart_1710777 baseEnd_1710777 := by
    simpa [prefixWord, tailWord_1710777, baseEnd_1710777] using wordTrace_append hprefix tailTrace_1710777
  have hstable : (prefixWord ++ tailWord_1710777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710777).length < 2 ^ (prefixWord ++ tailWord_1710777).sum := by decide
  have hdescent : baseEnd_1710777 < baseStart_1710777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710783 : List Nat := [1, 1, 2, 2, 2, 4, 4, 2, 1, 3]
def baseStart_1710783 : Nat := 118140960795 + 1710783 * 2 ^ 59
def prefixEnd_1710783 : Nat := 4983230072969 + 3 ^ 40 * 1710783 * 2
def baseEnd_1710783 : Nat := 585635983027256858229839

theorem tailTrace_1710783 : CollatzResearch.WordTrace tailWord_1710783 prefixEnd_1710783 585635983027256858229839 := by
  unfold tailWord_1710783
  simp only [CollatzResearch.WordTrace]
  refine ⟨62397382161132844319993003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41598254774088562879995335 62397382161132844319993003)
  ·
    refine ⟨93596073241699266479989505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62397382161132844319993003 93596073241699266479989505)
    ·
      refine ⟨70197054931274449859992129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93596073241699266479989505 70197054931274449859992129)
      ·
        refine ⟨52647791198455837394994097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70197054931274449859992129 52647791198455837394994097)
        ·
          refine ⟨39485843398841878046245573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52647791198455837394994097 39485843398841878046245573)
          ·
            refine ⟨7403595637282852133671045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39485843398841878046245573 7403595637282852133671045)
            ·
              refine ⟨1388174181990534775063321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7403595637282852133671045 1388174181990534775063321)
              ·
                refine ⟨1041130636492901081297491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1388174181990534775063321 1041130636492901081297491)
                ·
                  refine ⟨1561695954739351621946237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1041130636492901081297491 1561695954739351621946237)
                  ·
                    refine ⟨585635983027256858229839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1561695954739351621946237 585635983027256858229839)
                    ·
                      rfl

theorem cell22_1710783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 1, 3].length) (baseStart_1710783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710783 prefixEnd_1710783 := by exact prefixLift 1710783
  have htrace : WordTrace (prefixWord ++ tailWord_1710783) baseStart_1710783 baseEnd_1710783 := by
    simpa [prefixWord, tailWord_1710783, baseEnd_1710783] using wordTrace_append hprefix tailTrace_1710783
  have hstable : (prefixWord ++ tailWord_1710783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710783).length < 2 ^ (prefixWord ++ tailWord_1710783).sum := by decide
  have hdescent : baseEnd_1710783 < baseStart_1710783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710794 : List Nat := [3, 1, 2, 1, 4, 2, 1, 1, 2, 5]
def baseStart_1710794 : Nat := 118140960795 + 1710794 * 2 ^ 59
def prefixEnd_1710794 : Nat := 4983230072969 + 3 ^ 40 * 1710794 * 2
def baseEnd_1710794 : Nat := 585639748552056496204805

theorem tailTrace_1710794 : CollatzResearch.WordTrace tailWord_1710794 prefixEnd_1710794 585639748552056496204805 := by
  unfold tailWord_1710794
  simp only [CollatzResearch.WordTrace]
  refine ⟨15599445841023248299660859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41598522242728662132428957 15599445841023248299660859)
  ·
    refine ⟨23399168761534872449491289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15599445841023248299660859 23399168761534872449491289)
    ·
      refine ⟨17549376571151154337118467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23399168761534872449491289 17549376571151154337118467)
      ·
        refine ⟨26324064856726731505677701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17549376571151154337118467 26324064856726731505677701)
        ·
          refine ⟨4935762160636262157314569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26324064856726731505677701 4935762160636262157314569)
          ·
            refine ⟨3701821620477196617985927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4935762160636262157314569 3701821620477196617985927)
            ·
              refine ⟨5552732430715794926978891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3701821620477196617985927 5552732430715794926978891)
              ·
                refine ⟨8329098646073692390468337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5552732430715794926978891 8329098646073692390468337)
                ·
                  refine ⟨6246823984555269292851253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8329098646073692390468337 6246823984555269292851253)
                  ·
                    refine ⟨585639748552056496204805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6246823984555269292851253 585639748552056496204805)
                    ·
                      rfl

theorem cell22_1710794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_1710794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710794 prefixEnd_1710794 := by exact prefixLift 1710794
  have htrace : WordTrace (prefixWord ++ tailWord_1710794) baseStart_1710794 baseEnd_1710794 := by
    simpa [prefixWord, tailWord_1710794, baseEnd_1710794] using wordTrace_append hprefix tailTrace_1710794
  have hstable : (prefixWord ++ tailWord_1710794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710794).length < 2 ^ (prefixWord ++ tailWord_1710794).sum := by decide
  have hdescent : baseEnd_1710794 < baseStart_1710794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710807 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 8]
def baseStart_1710807 : Nat := 118140960795 + 1710807 * 2 ^ 59
def prefixEnd_1710807 : Nat := 4983230072969 + 3 ^ 40 * 1710807 * 2
def baseEnd_1710807 : Nat := 195214732905909598543255

theorem tailTrace_1710807 : CollatzResearch.WordTrace tailWord_1710807 prefixEnd_1710807 195214732905909598543255 := by
  unfold tailWord_1710807
  simp only [CollatzResearch.WordTrace]
  refine ⟨62398257513045896418866675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41598838342030597612577783 62398257513045896418866675)
  ·
    refine ⟨93597386269568844628300013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62398257513045896418866675 93597386269568844628300013)
    ·
      refine ⟨35099019851088316735612505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93597386269568844628300013 35099019851088316735612505)
      ·
        refine ⟨26324264888316237551709379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35099019851088316735612505 26324264888316237551709379)
        ·
          refine ⟨39486397332474356327564069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26324264888316237551709379 39486397332474356327564069)
          ·
            refine ⟨7403699499838941811418263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39486397332474356327564069 7403699499838941811418263)
            ·
              refine ⟨11105549249758412717127395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7403699499838941811418263 11105549249758412717127395)
              ·
                refine ⟨16658323874637619075691093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11105549249758412717127395 16658323874637619075691093)
                ·
                  refine ⟨195214732905909598543255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16658323874637619075691093 195214732905909598543255)
                  ·
                    rfl

theorem cell22_1710807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 8].length) (baseStart_1710807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710807 prefixEnd_1710807 := by exact prefixLift 1710807
  have htrace : WordTrace (prefixWord ++ tailWord_1710807) baseStart_1710807 baseEnd_1710807 := by
    simpa [prefixWord, tailWord_1710807, baseEnd_1710807] using wordTrace_append hprefix tailTrace_1710807
  have hstable : (prefixWord ++ tailWord_1710807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710807).length < 2 ^ (prefixWord ++ tailWord_1710807).sum := by decide
  have hdescent : baseEnd_1710807 < baseStart_1710807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710809 : List Nat := [1, 2, 1, 2, 3, 2, 2, 4, 1, 4]
def baseStart_1710809 : Nat := 118140960795 + 1710809 * 2 ^ 59
def prefixEnd_1710809 : Nat := 4983230072969 + 3 ^ 40 * 1710809 * 2
def baseEnd_1710809 : Nat := 585644883358601457079759

theorem tailTrace_1710809 : CollatzResearch.WordTrace tailWord_1710809 prefixEnd_1710809 585644883358601457079759 := by
  unfold tailWord_1710809
  simp only [CollatzResearch.WordTrace]
  refine ⟨62398330459038650760439481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41598886972692433840292987 62398330459038650760439481)
  ·
    refine ⟨46798747844278988070329611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62398330459038650760439481 46798747844278988070329611)
    ·
      refine ⟨70198121766418482105494417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46798747844278988070329611 70198121766418482105494417)
      ·
        refine ⟨52648591324813861579120813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70198121766418482105494417 52648591324813861579120813)
        ·
          refine ⟨19743221746805198092170305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52648591324813861579120813 19743221746805198092170305)
          ·
            refine ⟨14807416310103898569127729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19743221746805198092170305 14807416310103898569127729)
            ·
              refine ⟨11105562232577923926845797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14807416310103898569127729 11105562232577923926845797)
              ·
                refine ⟨2082292918608360736283587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11105562232577923926845797 2082292918608360736283587)
                ·
                  refine ⟨3123439377912541104425381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2082292918608360736283587 3123439377912541104425381)
                  ·
                    refine ⟨585644883358601457079759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3123439377912541104425381 585644883358601457079759)
                    ·
                      rfl

theorem cell22_1710809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 4].length) (baseStart_1710809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710809 prefixEnd_1710809 := by exact prefixLift 1710809
  have htrace : WordTrace (prefixWord ++ tailWord_1710809) baseStart_1710809 baseEnd_1710809 := by
    simpa [prefixWord, tailWord_1710809, baseEnd_1710809] using wordTrace_append hprefix tailTrace_1710809
  have hstable : (prefixWord ++ tailWord_1710809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710809).length < 2 ^ (prefixWord ++ tailWord_1710809).sum := by decide
  have hdescent : baseEnd_1710809 < baseStart_1710809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710856 : List Nat := [2, 1, 3, 2, 2, 4, 1, 1, 1, 5]
def baseStart_1710856 : Nat := 118140960795 + 1710856 * 2 ^ 59
def prefixEnd_1710856 : Nat := 4983230072969 + 3 ^ 40 * 1710856 * 2
def baseEnd_1710856 : Nat := 585660972419109001154615

theorem tailTrace_1710856 : CollatzResearch.WordTrace tailWord_1710856 prefixEnd_1710856 585660972419109001154615 := by
  unfold tailWord_1710856
  simp only [CollatzResearch.WordTrace]
  refine ⟨31200022344934188893700211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41600029793245585191600281 31200022344934188893700211)
  ·
    refine ⟨46800033517401283340550317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31200022344934188893700211 46800033517401283340550317)
    ·
      refine ⟨17550012569025481252706369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46800033517401283340550317 17550012569025481252706369)
      ·
        refine ⟨13162509426769110939529777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17550012569025481252706369 13162509426769110939529777)
        ·
          refine ⟨9871882070076833204647333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13162509426769110939529777 9871882070076833204647333)
          ·
            refine ⟨1850977888139406225871375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9871882070076833204647333 1850977888139406225871375)
            ·
              refine ⟨2776466832209109338807063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850977888139406225871375 2776466832209109338807063)
              ·
                refine ⟨4164700248313664008210595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2776466832209109338807063 4164700248313664008210595)
                ·
                  refine ⟨6247050372470496012315893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4164700248313664008210595 6247050372470496012315893)
                  ·
                    refine ⟨585660972419109001154615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6247050372470496012315893 585660972419109001154615)
                    ·
                      rfl

theorem cell22_1710856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_1710856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710856 prefixEnd_1710856 := by exact prefixLift 1710856
  have htrace : WordTrace (prefixWord ++ tailWord_1710856) baseStart_1710856 baseEnd_1710856 := by
    simpa [prefixWord, tailWord_1710856, baseEnd_1710856] using wordTrace_append hprefix tailTrace_1710856
  have hstable : (prefixWord ++ tailWord_1710856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710856).length < 2 ^ (prefixWord ++ tailWord_1710856).sum := by decide
  have hdescent : baseEnd_1710856 < baseStart_1710856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710867 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 2, 7]
def baseStart_1710867 : Nat := 118140960795 + 1710867 * 2 ^ 59
def prefixEnd_1710867 : Nat := 4983230072969 + 3 ^ 40 * 1710867 * 2
def baseEnd_1710867 : Nat := 585664737943908639129581

theorem tailTrace_1710867 : CollatzResearch.WordTrace tailWord_1710867 prefixEnd_1710867 585664737943908639129581 := by
  unfold tailWord_1710867
  simp only [CollatzResearch.WordTrace]
  refine ⟨62400445892828526666050855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41600297261885684444033903 62400445892828526666050855)
  ·
    refine ⟨93600668839242789999076283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62400445892828526666050855 93600668839242789999076283)
    ·
      refine ⟨140401003258864184998614425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93600668839242789999076283 140401003258864184998614425)
      ·
        refine ⟨105300752444148138748960819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140401003258864184998614425 105300752444148138748960819)
        ·
          refine ⟨157951128666222208123441229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105300752444148138748960819 157951128666222208123441229)
          ·
            refine ⟨59231673249833328046290461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157951128666222208123441229 59231673249833328046290461)
            ·
              refine ⟨22211877468687498017358923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59231673249833328046290461 22211877468687498017358923)
              ·
                refine ⟨33317816203031247026038385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22211877468687498017358923 33317816203031247026038385)
                ·
                  refine ⟨24988362152273435269528789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33317816203031247026038385 24988362152273435269528789)
                  ·
                    refine ⟨585664737943908639129581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24988362152273435269528789 585664737943908639129581)
                    ·
                      rfl

theorem cell22_1710867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 7].length) (baseStart_1710867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710867 prefixEnd_1710867 := by exact prefixLift 1710867
  have htrace : WordTrace (prefixWord ++ tailWord_1710867) baseStart_1710867 baseEnd_1710867 := by
    simpa [prefixWord, tailWord_1710867, baseEnd_1710867] using wordTrace_append hprefix tailTrace_1710867
  have hstable : (prefixWord ++ tailWord_1710867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710867).length < 2 ^ (prefixWord ++ tailWord_1710867).sum := by decide
  have hdescent : baseEnd_1710867 < baseStart_1710867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710952 : List Nat := [2, 1, 4, 2, 1, 4, 2, 2, 1, 3]
def baseStart_1710952 : Nat := 118140960795 + 1710952 * 2 ^ 59
def prefixEnd_1710952 : Nat := 4983230072969 + 3 ^ 40 * 1710952 * 2
def baseEnd_1710952 : Nat := 585693835180996750754321

theorem tailTrace_1710952 : CollatzResearch.WordTrace tailWord_1710952 prefixEnd_1710952 585693835180996750754321 := by
  unfold tailWord_1710952
  simp only [CollatzResearch.WordTrace]
  refine ⟨31201773048760293091447555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41602364065013724121930073 31201773048760293091447555)
  ·
    refine ⟨46802659573140439637171333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31201773048760293091447555 46802659573140439637171333)
    ·
      refine ⟨8775498669963832431969625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46802659573140439637171333 8775498669963832431969625)
      ·
        refine ⟨6581624002472874323977219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8775498669963832431969625 6581624002472874323977219)
        ·
          refine ⟨9872436003709311485965829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6581624002472874323977219 9872436003709311485965829)
          ·
            refine ⟨1851081750695495903618593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9872436003709311485965829 1851081750695495903618593)
            ·
              refine ⟨1388311313021621927713945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1851081750695495903618593 1388311313021621927713945)
              ·
                refine ⟨1041233484766216445785459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1388311313021621927713945 1041233484766216445785459)
                ·
                  refine ⟨1561850227149324668678189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1041233484766216445785459 1561850227149324668678189)
                  ·
                    refine ⟨585693835180996750754321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1561850227149324668678189 585693835180996750754321)
                    ·
                      rfl

theorem cell22_1710952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_1710952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1710952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1710952 prefixEnd_1710952 := by exact prefixLift 1710952
  have htrace : WordTrace (prefixWord ++ tailWord_1710952) baseStart_1710952 baseEnd_1710952 := by
    simpa [prefixWord, tailWord_1710952, baseEnd_1710952] using wordTrace_append hprefix tailTrace_1710952
  have hstable : (prefixWord ++ tailWord_1710952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710952).length < 2 ^ (prefixWord ++ tailWord_1710952).sum := by decide
  have hdescent : baseEnd_1710952 < baseStart_1710952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711008 : List Nat := [2, 1, 1, 4, 1, 1, 5, 2, 2, 3]
def baseStart_1711008 : Nat := 118140960795 + 1711008 * 2 ^ 59
def prefixEnd_1711008 : Nat := 4983230072969 + 3 ^ 40 * 1711008 * 2
def baseEnd_1711008 : Nat := 585713005125431271354149

theorem tailTrace_1711008 : CollatzResearch.WordTrace tailWord_1711008 prefixEnd_1711008 585713005125431271354149 := by
  unfold tailWord_1711008
  simp only [CollatzResearch.WordTrace]
  refine ⟨31202794292658853873466839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41603725723545138497955785 31202794292658853873466839)
  ·
    refine ⟨46804191438988280810200259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31202794292658853873466839 46804191438988280810200259)
    ·
      refine ⟨70206287158482421215300389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46804191438988280810200259 70206287158482421215300389)
      ·
        refine ⟨13163678842215453977868823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70206287158482421215300389 13163678842215453977868823)
        ·
          refine ⟨19745518263323180966803235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13163678842215453977868823 19745518263323180966803235)
          ·
            refine ⟨29618277394984771450204853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19745518263323180966803235 29618277394984771450204853)
            ·
              refine ⟨2776713505779822323456705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29618277394984771450204853 2776713505779822323456705)
              ·
                refine ⟨2082535129334866742592529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2776713505779822323456705 2082535129334866742592529)
                ·
                  refine ⟨1561901347001150056944397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2082535129334866742592529 1561901347001150056944397)
                  ·
                    refine ⟨585713005125431271354149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1561901347001150056944397 585713005125431271354149)
                    ·
                      rfl

theorem cell22_1711008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 2, 3].length) (baseStart_1711008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711008 prefixEnd_1711008 := by exact prefixLift 1711008
  have htrace : WordTrace (prefixWord ++ tailWord_1711008) baseStart_1711008 baseEnd_1711008 := by
    simpa [prefixWord, tailWord_1711008, baseEnd_1711008] using wordTrace_append hprefix tailTrace_1711008
  have hstable : (prefixWord ++ tailWord_1711008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711008).length < 2 ^ (prefixWord ++ tailWord_1711008).sum := by decide
  have hdescent : baseEnd_1711008 < baseStart_1711008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711025 : List Nat := [1, 2, 2, 4, 4, 1, 1, 1, 1, 5]
def baseStart_1711025 : Nat := 118140960795 + 1711025 * 2 ^ 59
def prefixEnd_1711025 : Nat := 4983230072969 + 3 ^ 40 * 1711025 * 2
def baseEnd_1711025 : Nat := 585718824572848893679097

theorem tailTrace_1711025 : CollatzResearch.WordTrace tailWord_1711025 prefixEnd_1711025 585718824572848893679097 := by
  unfold tailWord_1711025
  simp only [CollatzResearch.WordTrace]
  refine ⟨62406208626256119650302529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41604139084170746433535019 62406208626256119650302529)
  ·
    refine ⟨46804656469692089737726897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62406208626256119650302529 46804656469692089737726897)
    ·
      refine ⟨35103492352269067303295173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46804656469692089737726897 35103492352269067303295173)
      ·
        refine ⟨6581904816050450119367845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35103492352269067303295173 6581904816050450119367845)
        ·
          refine ⟨1234107153009459397381471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6581904816050450119367845 1234107153009459397381471)
          ·
            refine ⟨1851160729514189096072207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1234107153009459397381471 1851160729514189096072207)
            ·
              refine ⟨2776741094271283644108311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1851160729514189096072207 2776741094271283644108311)
              ·
                refine ⟨4165111641406925466162467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2776741094271283644108311 4165111641406925466162467)
                ·
                  refine ⟨6247667462110388199243701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4165111641406925466162467 6247667462110388199243701)
                  ·
                    refine ⟨585718824572848893679097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6247667462110388199243701 585718824572848893679097)
                    ·
                      rfl

theorem cell22_1711025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 1, 5].length) (baseStart_1711025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711025 prefixEnd_1711025 := by exact prefixLift 1711025
  have htrace : WordTrace (prefixWord ++ tailWord_1711025) baseStart_1711025 baseEnd_1711025 := by
    simpa [prefixWord, tailWord_1711025, baseEnd_1711025] using wordTrace_append hprefix tailTrace_1711025
  have hstable : (prefixWord ++ tailWord_1711025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711025).length < 2 ^ (prefixWord ++ tailWord_1711025).sum := by decide
  have hdescent : baseEnd_1711025 < baseStart_1711025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711044 : List Nat := [2, 3, 3, 3, 2, 1, 1, 3, 4]
def baseStart_1711044 : Nat := 118140960795 + 1711044 * 2 ^ 59
def prefixEnd_1711044 : Nat := 4983230072969 + 3 ^ 40 * 1711044 * 2
def baseEnd_1711044 : Nat := 195241776220379725818013

theorem tailTrace_1711044 : CollatzResearch.WordTrace tailWord_1711044 prefixEnd_1711044 195241776220379725818013 := by
  unfold tailWord_1711044
  simp only [CollatzResearch.WordTrace]
  refine ⟨31203450806593642947622093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41604601075458190596829457 31203450806593642947622093)
  ·
    refine ⟨11701294052472616105358285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31203450806593642947622093 11701294052472616105358285)
    ·
      refine ⟨4387985269677231039509357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11701294052472616105358285 4387985269677231039509357)
      ·
        refine ⟨1645494476128961639816009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4387985269677231039509357 1645494476128961639816009)
        ·
          refine ⟨1234120857096721229862007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1645494476128961639816009 1234120857096721229862007)
          ·
            refine ⟨1851181285645081844793011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1234120857096721229862007 1851181285645081844793011)
            ·
              refine ⟨2776771928467622767189517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1851181285645081844793011 2776771928467622767189517)
              ·
                refine ⟨1041289473175358537696069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2776771928467622767189517 1041289473175358537696069)
                ·
                  refine ⟨195241776220379725818013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1041289473175358537696069 195241776220379725818013)
                  ·
                    rfl

theorem cell22_1711044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_1711044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711044 prefixEnd_1711044 := by exact prefixLift 1711044
  have htrace : WordTrace (prefixWord ++ tailWord_1711044) baseStart_1711044 baseEnd_1711044 := by
    simpa [prefixWord, tailWord_1711044, baseEnd_1711044] using wordTrace_append hprefix tailTrace_1711044
  have hstable : (prefixWord ++ tailWord_1711044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711044).length < 2 ^ (prefixWord ++ tailWord_1711044).sum := by decide
  have hdescent : baseEnd_1711044 < baseStart_1711044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711066 : List Nat := [3, 1, 1, 2, 4, 1, 2, 1, 7]
def baseStart_1711066 : Nat := 118140960795 + 1711066 * 2 ^ 59
def prefixEnd_1711066 : Nat := 4983230072969 + 3 ^ 40 * 1711066 * 2
def baseEnd_1711066 : Nat := 195244286570246151134657

theorem tailTrace_1711066 : CollatzResearch.WordTrace tailWord_1711066 prefixEnd_1711066 195244286570246151134657 := by
  unfold tailWord_1711066
  simp only [CollatzResearch.WordTrace]
  refine ⟨15601926004776895913136263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41605136012738389101696701 15601926004776895913136263)
  ·
    refine ⟨23402889007165343869704395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15601926004776895913136263 23402889007165343869704395)
    ·
      refine ⟨35104333510748015804556593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23402889007165343869704395 35104333510748015804556593)
      ·
        refine ⟨26328250133061011853417445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35104333510748015804556593 26328250133061011853417445)
        ·
          refine ⟨4936546899948939722515771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26328250133061011853417445 4936546899948939722515771)
          ·
            refine ⟨7404820349923409583773657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4936546899948939722515771 7404820349923409583773657)
            ·
              refine ⟨5553615262442557187830243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7404820349923409583773657 5553615262442557187830243)
              ·
                refine ⟨8330422893663835781745365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5553615262442557187830243 8330422893663835781745365)
                ·
                  refine ⟨195244286570246151134657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8330422893663835781745365 195244286570246151134657)
                  ·
                    rfl

theorem cell22_1711066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_1711066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711066 prefixEnd_1711066 := by exact prefixLift 1711066
  have htrace : WordTrace (prefixWord ++ tailWord_1711066) baseStart_1711066 baseEnd_1711066 := by
    simpa [prefixWord, tailWord_1711066, baseEnd_1711066] using wordTrace_append hprefix tailTrace_1711066
  have hstable : (prefixWord ++ tailWord_1711066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711066).length < 2 ^ (prefixWord ++ tailWord_1711066).sum := by decide
  have hdescent : baseEnd_1711066 < baseStart_1711066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711141 : List Nat := [1, 3, 1, 2, 2, 2, 2, 2, 1, 6]
def baseStart_1711141 : Nat := 118140960795 + 1711141 * 2 ^ 59
def prefixEnd_1711141 : Nat := 4983230072969 + 3 ^ 40 * 1711141 * 2
def baseEnd_1711141 : Nat := 585758533743463257778741

theorem tailTrace_1711141 : CollatzResearch.WordTrace tailWord_1711141 prefixEnd_1711141 585758533743463257778741 := by
  unfold tailWord_1711141
  simp only [CollatzResearch.WordTrace]
  refine ⟨62410439493835871461525277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41606959662557247641016851 62410439493835871461525277)
  ·
    refine ⟨23403914810188451798071979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62410439493835871461525277 23403914810188451798071979)
    ·
      refine ⟨35105872215282677697107969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23403914810188451798071979 35105872215282677697107969)
      ·
        refine ⟨26329404161462008272830977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35105872215282677697107969 26329404161462008272830977)
        ·
          refine ⟨19747053121096506204623233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26329404161462008272830977 19747053121096506204623233)
          ·
            refine ⟨14810289840822379653467425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19747053121096506204623233 14810289840822379653467425)
            ·
              refine ⟨11107717380616784740100569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14810289840822379653467425 11107717380616784740100569)
              ·
                refine ⟨8330788035462588555075427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11107717380616784740100569 8330788035462588555075427)
                ·
                  refine ⟨12496182053193882832613141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8330788035462588555075427 12496182053193882832613141)
                  ·
                    refine ⟨585758533743463257778741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12496182053193882832613141 585758533743463257778741)
                    ·
                      rfl

theorem cell22_1711141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_1711141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711141 prefixEnd_1711141 := by exact prefixLift 1711141
  have htrace : WordTrace (prefixWord ++ tailWord_1711141) baseStart_1711141 baseEnd_1711141 := by
    simpa [prefixWord, tailWord_1711141, baseEnd_1711141] using wordTrace_append hprefix tailTrace_1711141
  have hstable : (prefixWord ++ tailWord_1711141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711141).length < 2 ^ (prefixWord ++ tailWord_1711141).sum := by decide
  have hdescent : baseEnd_1711141 < baseStart_1711141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711282 : List Nat := [3, 2, 1, 1, 1, 5, 3, 1, 1, 4]
def baseStart_1711282 : Nat := 118140960795 + 1711282 * 2 ^ 59
def prefixEnd_1711282 : Nat := 4983230072969 + 3 ^ 40 * 1711282 * 2
def baseEnd_1711282 : Nat := 585806800924985890003309

theorem tailTrace_1711282 : CollatzResearch.WordTrace tailWord_1711282 prefixEnd_1711282 585806800924985890003309 := by
  unfold tailWord_1711282
  simp only [CollatzResearch.WordTrace]
  refine ⟨15603895546581263135602025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41610388124216701694938733 15603895546581263135602025)
  ·
    refine ⟨11702921659935947351701519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15603895546581263135602025 11702921659935947351701519)
    ·
      refine ⟨17554382489903921027552279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11702921659935947351701519 17554382489903921027552279)
      ·
        refine ⟨26331573734855881541328419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17554382489903921027552279 26331573734855881541328419)
        ·
          refine ⟨39497360602283822311992629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26331573734855881541328419 39497360602283822311992629)
          ·
            refine ⟨3702877556464108341749309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39497360602283822311992629 3702877556464108341749309)
            ·
              refine ⟨1388579083674040628155991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3702877556464108341749309 1388579083674040628155991)
              ·
                refine ⟨2082868625511060942233987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1388579083674040628155991 2082868625511060942233987)
                ·
                  refine ⟨3124302938266591413350981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2082868625511060942233987 3124302938266591413350981)
                  ·
                    refine ⟨585806800924985890003309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3124302938266591413350981 585806800924985890003309)
                    ·
                      rfl

theorem cell22_1711282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_1711282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711282 prefixEnd_1711282 := by exact prefixLift 1711282
  have htrace : WordTrace (prefixWord ++ tailWord_1711282) baseStart_1711282 baseEnd_1711282 := by
    simpa [prefixWord, tailWord_1711282, baseEnd_1711282] using wordTrace_append hprefix tailTrace_1711282
  have hstable : (prefixWord ++ tailWord_1711282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711282).length < 2 ^ (prefixWord ++ tailWord_1711282).sum := by decide
  have hdescent : baseEnd_1711282 < baseStart_1711282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711295 : List Nat := [1, 1, 2, 2, 2, 2, 3, 4, 2, 3]
def baseStart_1711295 : Nat := 118140960795 + 1711295 * 2 ^ 59
def prefixEnd_1711295 : Nat := 4983230072969 + 3 ^ 40 * 1711295 * 2
def baseEnd_1711295 : Nat := 585811251090658189428269

theorem tailTrace_1711295 : CollatzResearch.WordTrace tailWord_1711295 prefixEnd_1711295 585811251090658189428269 := by
  unfold tailWord_1711295
  simp only [CollatzResearch.WordTrace]
  refine ⟨62416056335277955762631339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41610704223518637175087559 62416056335277955762631339)
  ·
    refine ⟨93624084502916933643947009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62416056335277955762631339 93624084502916933643947009)
    ·
      refine ⟨70218063377187700232960257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93624084502916933643947009 70218063377187700232960257)
      ·
        refine ⟨52663547532890775174720193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70218063377187700232960257 52663547532890775174720193)
        ·
          refine ⟨39497660649668081381040145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52663547532890775174720193 39497660649668081381040145)
          ·
            refine ⟨29623245487251061035780109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39497660649668081381040145 29623245487251061035780109)
            ·
              refine ⟨11108717057719147888417541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29623245487251061035780109 11108717057719147888417541)
              ·
                refine ⟨2082884448322340229078289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11108717057719147888417541 2082884448322340229078289)
                ·
                  refine ⟨1562163336241755171808717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2082884448322340229078289 1562163336241755171808717)
                  ·
                    refine ⟨585811251090658189428269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1562163336241755171808717 585811251090658189428269)
                    ·
                      rfl

theorem cell22_1711295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 3].length) (baseStart_1711295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711295 prefixEnd_1711295 := by exact prefixLift 1711295
  have htrace : WordTrace (prefixWord ++ tailWord_1711295) baseStart_1711295 baseEnd_1711295 := by
    simpa [prefixWord, tailWord_1711295, baseEnd_1711295] using wordTrace_append hprefix tailTrace_1711295
  have hstable : (prefixWord ++ tailWord_1711295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711295).length < 2 ^ (prefixWord ++ tailWord_1711295).sum := by decide
  have hdescent : baseEnd_1711295 < baseStart_1711295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711346 : List Nat := [3, 2, 1, 3, 4, 1, 1, 2, 2, 3]
def baseStart_1711346 : Nat := 118140960795 + 1711346 * 2 ^ 59
def prefixEnd_1711346 : Nat := 4983230072969 + 3 ^ 40 * 1711346 * 2
def baseEnd_1711346 : Nat := 585828709432911056403113

theorem tailTrace_1711346 : CollatzResearch.WordTrace tailWord_1711346 prefixEnd_1711346 585828709432911056403113 := by
  unfold tailWord_1711346
  simp only [CollatzResearch.WordTrace]
  refine ⟨15604479114523297868184473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41611944305395460981825261 15604479114523297868184473)
  ·
    refine ⟨11703359335892473401138355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15604479114523297868184473 11703359335892473401138355)
    ·
      refine ⟨17555039003838710101707533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11703359335892473401138355 17555039003838710101707533)
      ·
        refine ⟨6583139626439516288140325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17555039003838710101707533 6583139626439516288140325)
        ·
          refine ⟨1234338679957409304026311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6583139626439516288140325 1234338679957409304026311)
          ·
            refine ⟨1851508019936113956039467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1234338679957409304026311 1851508019936113956039467)
            ·
              refine ⟨2777262029904170934059201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1851508019936113956039467 2777262029904170934059201)
              ·
                refine ⟨2082946522428128200544401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2777262029904170934059201 2082946522428128200544401)
                ·
                  refine ⟨1562209891821096150408301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2082946522428128200544401 1562209891821096150408301)
                  ·
                    refine ⟨585828709432911056403113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1562209891821096150408301 585828709432911056403113)
                    ·
                      rfl

theorem cell22_1711346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_1711346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711346 prefixEnd_1711346 := by exact prefixLift 1711346
  have htrace : WordTrace (prefixWord ++ tailWord_1711346) baseStart_1711346 baseEnd_1711346 := by
    simpa [prefixWord, tailWord_1711346, baseEnd_1711346] using wordTrace_append hprefix tailTrace_1711346
  have hstable : (prefixWord ++ tailWord_1711346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711346).length < 2 ^ (prefixWord ++ tailWord_1711346).sum := by decide
  have hdescent : baseEnd_1711346 < baseStart_1711346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711353 : List Nat := [1, 2, 1, 3, 1, 1, 5, 1, 7]
def baseStart_1711353 : Nat := 118140960795 + 1711353 * 2 ^ 59
def prefixEnd_1711353 : Nat := 4983230072969 + 3 ^ 40 * 1711353 * 2
def baseEnd_1711353 : Nat := 195277035225321790492697

theorem tailTrace_1711353 : CollatzResearch.WordTrace tailWord_1711353 prefixEnd_1711353 195277035225321790492697 := by
  unfold tailWord_1711353
  simp only [CollatzResearch.WordTrace]
  refine ⟨62418171769067831668242713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41612114512711887778828475 62418171769067831668242713)
  ·
    refine ⟨46813628826800873751182035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62418171769067831668242713 46813628826800873751182035)
    ·
      refine ⟨70220443240201310626773053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46813628826800873751182035 70220443240201310626773053)
      ·
        refine ⟨26332666215075491485039895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70220443240201310626773053 26332666215075491485039895)
        ·
          refine ⟨39498999322613237227559843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26332666215075491485039895 39498999322613237227559843)
          ·
            refine ⟨59248498983919855841339765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39498999322613237227559843 59248498983919855841339765)
            ·
              refine ⟨5554546779742486485125603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59248498983919855841339765 5554546779742486485125603)
              ·
                refine ⟨8331820169613729727688405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5554546779742486485125603 8331820169613729727688405)
                ·
                  refine ⟨195277035225321790492697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8331820169613729727688405 195277035225321790492697)
                  ·
                    rfl

theorem cell22_1711353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 7].length) (baseStart_1711353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711353 prefixEnd_1711353 := by exact prefixLift 1711353
  have htrace : WordTrace (prefixWord ++ tailWord_1711353) baseStart_1711353 baseEnd_1711353 := by
    simpa [prefixWord, tailWord_1711353, baseEnd_1711353] using wordTrace_append hprefix tailTrace_1711353
  have hstable : (prefixWord ++ tailWord_1711353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711353).length < 2 ^ (prefixWord ++ tailWord_1711353).sum := by decide
  have hdescent : baseEnd_1711353 < baseStart_1711353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711391 : List Nat := [1, 1, 2, 4, 4, 2, 1, 3, 1, 3]
def baseStart_1711391 : Nat := 118140960795 + 1711391 * 2 ^ 59
def prefixEnd_1711391 : Nat := 4983230072969 + 3 ^ 40 * 1711391 * 2
def baseEnd_1711391 : Nat := 585844113852545939027975

theorem tailTrace_1711391 : CollatzResearch.WordTrace tailWord_1711391 prefixEnd_1711391 585844113852545939027975 := by
  unfold tailWord_1711391
  simp only [CollatzResearch.WordTrace]
  refine ⟨62419557742930164158126027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41613038495286776105417351 62419557742930164158126027)
  ·
    refine ⟨93629336614395246237189041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62419557742930164158126027 93629336614395246237189041)
    ·
      refine ⟨70222002460796434677891781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93629336614395246237189041 70222002460796434677891781)
      ·
        refine ⟨13166625461399331502104709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70222002460796434677891781 13166625461399331502104709)
        ·
          refine ⟨2468742274012374656644633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13166625461399331502104709 2468742274012374656644633)
          ·
            refine ⟨1851556705509280992483475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2468742274012374656644633 1851556705509280992483475)
            ·
              refine ⟨2777335058263921488725213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1851556705509280992483475 2777335058263921488725213)
              ·
                refine ⟨1041500646848970558271955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2777335058263921488725213 1041500646848970558271955)
                ·
                  refine ⟨1562250970273455837407933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1041500646848970558271955 1562250970273455837407933)
                  ·
                    refine ⟨585844113852545939027975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1562250970273455837407933 585844113852545939027975)
                    ·
                      rfl

theorem cell22_1711391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 1, 3].length) (baseStart_1711391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711391 prefixEnd_1711391 := by exact prefixLift 1711391
  have htrace : WordTrace (prefixWord ++ tailWord_1711391) baseStart_1711391 baseEnd_1711391 := by
    simpa [prefixWord, tailWord_1711391, baseEnd_1711391] using wordTrace_append hprefix tailTrace_1711391
  have hstable : (prefixWord ++ tailWord_1711391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711391).length < 2 ^ (prefixWord ++ tailWord_1711391).sum := by decide
  have hdescent : baseEnd_1711391 < baseStart_1711391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711421 : List Nat := [1, 4, 1, 5, 1, 2, 2, 1, 5]
def baseStart_1711421 : Nat := 118140960795 + 1711421 * 2 ^ 59
def prefixEnd_1711421 : Nat := 4983230072969 + 3 ^ 40 * 1711421 * 2
def baseEnd_1711421 : Nat := 195284794488545286925961

theorem tailTrace_1711421 : CollatzResearch.WordTrace tailWord_1711421 prefixEnd_1711421 195284794488545286925961 := by
  unfold tailWord_1711421
  simp only [CollatzResearch.WordTrace]
  refine ⟨62420651932821479281718117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41613767955214319521145411 62420651932821479281718117)
  ·
    refine ⟨11703872237404027365322147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62420651932821479281718117 11703872237404027365322147)
    ·
      refine ⟨17555808356106041047983221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11703872237404027365322147 17555808356106041047983221)
      ·
        refine ⟨1645857033384941348248427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17555808356106041047983221 1645857033384941348248427)
        ·
          refine ⟨2468785550077412022372641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1645857033384941348248427 2468785550077412022372641)
          ·
            refine ⟨1851589162558059016779481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2468785550077412022372641 1851589162558059016779481)
            ·
              refine ⟨1388691871918544262584611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1851589162558059016779481 1388691871918544262584611)
              ·
                refine ⟨2083037807877816393876917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1388691871918544262584611 2083037807877816393876917)
                ·
                  refine ⟨195284794488545286925961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2083037807877816393876917 195284794488545286925961)
                  ·
                    rfl

theorem cell22_1711421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_1711421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711421 prefixEnd_1711421 := by exact prefixLift 1711421
  have htrace : WordTrace (prefixWord ++ tailWord_1711421) baseStart_1711421 baseEnd_1711421 := by
    simpa [prefixWord, tailWord_1711421, baseEnd_1711421] using wordTrace_append hprefix tailTrace_1711421
  have hstable : (prefixWord ++ tailWord_1711421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711421).length < 2 ^ (prefixWord ++ tailWord_1711421).sum := by decide
  have hdescent : baseEnd_1711421 < baseStart_1711421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711443 : List Nat := [1, 1, 1, 2, 1, 1, 5, 10]
def baseStart_1711443 : Nat := 118140960795 + 1711443 * 2 ^ 59
def prefixEnd_1711443 : Nat := 4983230072969 + 3 ^ 40 * 1711443 * 2
def baseEnd_1711443 : Nat := 65095768279470570747535

theorem tailTrace_1711443 : CollatzResearch.WordTrace tailWord_1711443 prefixEnd_1711443 65095768279470570747535 := by
  unfold tailWord_1711443
  simp only [CollatzResearch.WordTrace]
  refine ⟨62421454338741777039018983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41614302892494518026012655 62421454338741777039018983)
  ·
    refine ⟨93632181508112665558528475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62421454338741777039018983 93632181508112665558528475)
    ·
      refine ⟨140448272262168998337792713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93632181508112665558528475 140448272262168998337792713)
      ·
        refine ⟨105336204196626748753344535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140448272262168998337792713 105336204196626748753344535)
        ·
          refine ⟨158004306294940123130016803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105336204196626748753344535 158004306294940123130016803)
          ·
            refine ⟨237006459442410184695025205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158004306294940123130016803 237006459442410184695025205)
            ·
              refine ⟨22219355572725954815158613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 237006459442410184695025205 22219355572725954815158613)
              ·
                refine ⟨65095768279470570747535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22219355572725954815158613 65095768279470570747535)
                ·
                  rfl

theorem cell22_1711443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 10].length) (baseStart_1711443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711443 prefixEnd_1711443 := by exact prefixLift 1711443
  have htrace : WordTrace (prefixWord ++ tailWord_1711443) baseStart_1711443 baseEnd_1711443 := by
    simpa [prefixWord, tailWord_1711443, baseEnd_1711443] using wordTrace_append hprefix tailTrace_1711443
  have hstable : (prefixWord ++ tailWord_1711443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711443).length < 2 ^ (prefixWord ++ tailWord_1711443).sum := by decide
  have hdescent : baseEnd_1711443 < baseStart_1711443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711492 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 5, 3]
def baseStart_1711492 : Nat := 118140960795 + 1711492 * 2 ^ 59
def prefixEnd_1711492 : Nat := 4983230072969 + 3 ^ 40 * 1711492 * 2
def baseEnd_1711492 : Nat := 585878688216615342252665

theorem tailTrace_1711492 : CollatzResearch.WordTrace tailWord_1711492 prefixEnd_1711492 585878688216615342252665 := by
  unfold tailWord_1711492
  simp only [CollatzResearch.WordTrace]
  refine ⟨31211620757782129203776365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41615494343709505605035153 31211620757782129203776365)
  ·
    refine ⟨11704357784168298451416137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31211620757782129203776365 11704357784168298451416137)
    ·
      refine ⟨8778268338126223838562103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11704357784168298451416137 8778268338126223838562103)
      ·
        refine ⟨13167402507189335757843155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8778268338126223838562103 13167402507189335757843155)
        ·
          refine ⟨19751103760784003636764733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13167402507189335757843155 19751103760784003636764733)
          ·
            refine ⟨7406663910294001363786775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19751103760784003636764733 7406663910294001363786775)
            ·
              refine ⟨11109995865441002045680163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7406663910294001363786775 11109995865441002045680163)
              ·
                refine ⟨16664993798161503068520245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11109995865441002045680163 16664993798161503068520245)
                ·
                  refine ⟨1562343168577640912673773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16664993798161503068520245 1562343168577640912673773)
                  ·
                    refine ⟨585878688216615342252665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1562343168577640912673773 585878688216615342252665)
                    ·
                      rfl

theorem cell22_1711492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_1711492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711492 prefixEnd_1711492 := by exact prefixLift 1711492
  have htrace : WordTrace (prefixWord ++ tailWord_1711492) baseStart_1711492 baseEnd_1711492 := by
    simpa [prefixWord, tailWord_1711492, baseEnd_1711492] using wordTrace_append hprefix tailTrace_1711492
  have hstable : (prefixWord ++ tailWord_1711492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711492).length < 2 ^ (prefixWord ++ tailWord_1711492).sum := by decide
  have hdescent : baseEnd_1711492 < baseStart_1711492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711509 : List Nat := [1, 3, 2, 1, 1, 2, 3, 5, 1, 3]
def baseStart_1711509 : Nat := 118140960795 + 1711509 * 2 ^ 59
def prefixEnd_1711509 : Nat := 4983230072969 + 3 ^ 40 * 1711509 * 2
def baseEnd_1711509 : Nat := 585884507664032964577613

theorem tailTrace_1711509 : CollatzResearch.WordTrace tailWord_1711509 prefixEnd_1711509 585884507664032964577613 := by
  unfold tailWord_1711509
  simp only [CollatzResearch.WordTrace]
  refine ⟨62423861556502670310921581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41615907704335113540614387 62423861556502670310921581)
  ·
    refine ⟨23408948083688501366595593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62423861556502670310921581 23408948083688501366595593)
    ·
      refine ⟨17556711062766376024946695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23408948083688501366595593 17556711062766376024946695)
      ·
        refine ⟨26335066594149564037420043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17556711062766376024946695 26335066594149564037420043)
        ·
          refine ⟨39502599891224346056130065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26335066594149564037420043 39502599891224346056130065)
          ·
            refine ⟨29626949918418259542097549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39502599891224346056130065 29626949918418259542097549)
            ·
              refine ⟨11110106219406847328286581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29626949918418259542097549 11110106219406847328286581)
              ·
                refine ⟨1041572458069391937026867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11110106219406847328286581 1041572458069391937026867)
                ·
                  refine ⟨1562358687104087905540301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1041572458069391937026867 1562358687104087905540301)
                  ·
                    refine ⟨585884507664032964577613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1562358687104087905540301 585884507664032964577613)
                    ·
                      rfl

theorem cell22_1711509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_1711509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711509 prefixEnd_1711509 := by exact prefixLift 1711509
  have htrace : WordTrace (prefixWord ++ tailWord_1711509) baseStart_1711509 baseEnd_1711509 := by
    simpa [prefixWord, tailWord_1711509, baseEnd_1711509] using wordTrace_append hprefix tailTrace_1711509
  have hstable : (prefixWord ++ tailWord_1711509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711509).length < 2 ^ (prefixWord ++ tailWord_1711509).sum := by decide
  have hdescent : baseEnd_1711509 < baseStart_1711509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711520 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 4, 5]
def baseStart_1711520 : Nat := 118140960795 + 1711520 * 2 ^ 59
def prefixEnd_1711520 : Nat := 4983230072969 + 3 ^ 40 * 1711520 * 2
def baseEnd_1711520 : Nat := 585888273188832602552579

theorem tailTrace_1711520 : CollatzResearch.WordTrace tailWord_1711520 prefixEnd_1711520 585888273188832602552579 := by
  unfold tailWord_1711520
  simp only [CollatzResearch.WordTrace]
  refine ⟨31212131379731409594786007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41616175172975212793048009 31212131379731409594786007)
  ·
    refine ⟨46818197069597114392179011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31212131379731409594786007 46818197069597114392179011)
    ·
      refine ⟨70227295604395671588268517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46818197069597114392179011 70227295604395671588268517)
      ·
        refine ⟨13167617925824188422800347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70227295604395671588268517 13167617925824188422800347)
        ·
          refine ⟨19751426888736282634200521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13167617925824188422800347 19751426888736282634200521)
          ·
            refine ⟨14813570166552211975650391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19751426888736282634200521 14813570166552211975650391)
            ·
              refine ⟨22220355249828317963475587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14813570166552211975650391 22220355249828317963475587)
              ·
                refine ⟨33330532874742476945213381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22220355249828317963475587 33330532874742476945213381)
                ·
                  refine ⟨6249474914014214427227509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33330532874742476945213381 6249474914014214427227509)
                  ·
                    refine ⟨585888273188832602552579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6249474914014214427227509 585888273188832602552579)
                    ·
                      rfl

theorem cell22_1711520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 4, 5].length) (baseStart_1711520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711520 prefixEnd_1711520 := by exact prefixLift 1711520
  have htrace : WordTrace (prefixWord ++ tailWord_1711520) baseStart_1711520 baseEnd_1711520 := by
    simpa [prefixWord, tailWord_1711520, baseEnd_1711520] using wordTrace_append hprefix tailTrace_1711520
  have hstable : (prefixWord ++ tailWord_1711520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711520).length < 2 ^ (prefixWord ++ tailWord_1711520).sum := by decide
  have hdescent : baseEnd_1711520 < baseStart_1711520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711522 : List Nat := [3, 3, 1, 2, 1, 3, 1, 1, 7]
def baseStart_1711522 : Nat := 118140960795 + 1711522 * 2 ^ 59
def prefixEnd_1711522 : Nat := 4983230072969 + 3 ^ 40 * 1711522 * 2
def baseEnd_1711522 : Nat := 195296319276568421334191

theorem tailTrace_1711522 : CollatzResearch.WordTrace tailWord_1711522 prefixEnd_1711522 195296319276568421334191 := by
  unfold tailWord_1711522
  simp only [CollatzResearch.WordTrace]
  refine ⟨15606083926363893382786205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41616223803637049020763213 15606083926363893382786205)
  ·
    refine ⟨5852281472386460018544827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15606083926363893382786205 5852281472386460018544827)
    ·
      refine ⟨8778422208579690027817241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5852281472386460018544827 8778422208579690027817241)
      ·
        refine ⟨6583816656434767520862931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8778422208579690027817241 6583816656434767520862931)
        ·
          refine ⟨9875724984652151281294397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6583816656434767520862931 9875724984652151281294397)
          ·
            refine ⟨3703396869244556730485399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9875724984652151281294397 3703396869244556730485399)
            ·
              refine ⟨5555095303866835095728099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3703396869244556730485399 5555095303866835095728099)
              ·
                refine ⟨8332642955800252643592149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5555095303866835095728099 8332642955800252643592149)
                ·
                  refine ⟨195296319276568421334191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8332642955800252643592149 195296319276568421334191)
                  ·
                    rfl

theorem cell22_1711522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_1711522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711522 prefixEnd_1711522 := by exact prefixLift 1711522
  have htrace : WordTrace (prefixWord ++ tailWord_1711522) baseStart_1711522 baseEnd_1711522 := by
    simpa [prefixWord, tailWord_1711522, baseEnd_1711522] using wordTrace_append hprefix tailTrace_1711522
  have hstable : (prefixWord ++ tailWord_1711522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711522).length < 2 ^ (prefixWord ++ tailWord_1711522).sum := by decide
  have hdescent : baseEnd_1711522 < baseStart_1711522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711535 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 5, 4]
def baseStart_1711535 : Nat := 118140960795 + 1711535 * 2 ^ 59
def prefixEnd_1711535 : Nat := 4983230072969 + 3 ^ 40 * 1711535 * 2
def baseEnd_1711535 : Nat := 585893407995377563427533

theorem tailTrace_1711535 : CollatzResearch.WordTrace tailWord_1711535 prefixEnd_1711535 585893407995377563427533 := by
  unfold tailWord_1711535
  simp only [CollatzResearch.WordTrace]
  refine ⟨62424809854408476751368059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41616539902938984500912039 62424809854408476751368059)
  ·
    refine ⟨93637214781612715127052089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62424809854408476751368059 93637214781612715127052089)
    ·
      refine ⟨70227911086209536345289067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93637214781612715127052089 70227911086209536345289067)
      ·
        refine ⟨105341866629314304517933601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70227911086209536345289067 105341866629314304517933601)
        ·
          refine ⟨79006399971985728388450201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105341866629314304517933601 79006399971985728388450201)
          ·
            refine ⟨59254799978989296291337651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79006399971985728388450201 59254799978989296291337651)
            ·
              refine ⟨88882199968483944437006477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59254799978989296291337651 88882199968483944437006477)
              ·
                refine ⟨33330824988181479163877429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88882199968483944437006477 33330824988181479163877429)
                ·
                  refine ⟨3124764842642013671613509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33330824988181479163877429 3124764842642013671613509)
                  ·
                    refine ⟨585893407995377563427533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3124764842642013671613509 585893407995377563427533)
                    ·
                      rfl

theorem cell22_1711535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 4].length) (baseStart_1711535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711535 prefixEnd_1711535 := by exact prefixLift 1711535
  have htrace : WordTrace (prefixWord ++ tailWord_1711535) baseStart_1711535 baseEnd_1711535 := by
    simpa [prefixWord, tailWord_1711535, baseEnd_1711535] using wordTrace_append hprefix tailTrace_1711535
  have hstable : (prefixWord ++ tailWord_1711535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711535).length < 2 ^ (prefixWord ++ tailWord_1711535).sum := by decide
  have hdescent : baseEnd_1711535 < baseStart_1711535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711552 : List Nat := [2, 1, 1, 2, 3, 1, 3, 4, 1, 4]
def baseStart_1711552 : Nat := 118140960795 + 1711552 * 2 ^ 59
def prefixEnd_1711552 : Nat := 4983230072969 + 3 ^ 40 * 1711552 * 2
def baseEnd_1711552 : Nat := 585899227442795185752481

theorem tailTrace_1711552 : CollatzResearch.WordTrace tailWord_1711552 prefixEnd_1711552 585899227442795185752481 := by
  unfold tailWord_1711552
  simp only [CollatzResearch.WordTrace]
  refine ⟨31212714947673444327368455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41616953263564592436491273 31212714947673444327368455)
  ·
    refine ⟨46819072421510166491052683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31212714947673444327368455 46819072421510166491052683)
    ·
      refine ⟨70228608632265249736579025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46819072421510166491052683 70228608632265249736579025)
      ·
        refine ⟨52671456474198937302434269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70228608632265249736579025 52671456474198937302434269)
        ·
          refine ⟨19751796177824601488412851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52671456474198937302434269 19751796177824601488412851)
          ·
            refine ⟨29627694266736902232619277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19751796177824601488412851 29627694266736902232619277)
            ·
              refine ⟨11110385350026338337232229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29627694266736902232619277 11110385350026338337232229)
              ·
                refine ⟨2083197253129938438231043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11110385350026338337232229 2083197253129938438231043)
                ·
                  refine ⟨3124795879694907657346565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2083197253129938438231043 3124795879694907657346565)
                  ·
                    refine ⟨585899227442795185752481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3124795879694907657346565 585899227442795185752481)
                    ·
                      rfl

theorem cell22_1711552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 1, 4].length) (baseStart_1711552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711552 prefixEnd_1711552 := by exact prefixLift 1711552
  have htrace : WordTrace (prefixWord ++ tailWord_1711552) baseStart_1711552 baseEnd_1711552 := by
    simpa [prefixWord, tailWord_1711552, baseEnd_1711552] using wordTrace_append hprefix tailTrace_1711552
  have hstable : (prefixWord ++ tailWord_1711552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711552).length < 2 ^ (prefixWord ++ tailWord_1711552).sum := by decide
  have hdescent : baseEnd_1711552 < baseStart_1711552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711629 : List Nat := [1, 7, 1, 1, 12]
def baseStart_1711629 : Nat := 118140960795 + 1711629 * 2 ^ 59
def prefixEnd_1711629 : Nat := 4983230072969 + 3 ^ 40 * 1711629 * 2
def baseEnd_1711629 : Nat := 2411216403771163175215

theorem tailTrace_1711629 : CollatzResearch.WordTrace tailWord_1711629 prefixEnd_1711629 2411216403771163175215 := by
  unfold tailWord_1711629
  simp only [CollatzResearch.WordTrace]
  refine ⟨62428238316067930805289941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41618825544045287203526627 62428238316067930805289941)
  ·
    refine ⟨1463161835532842128248983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 62428238316067930805289941 1463161835532842128248983)
    ·
      refine ⟨2194742753299263192373475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1463161835532842128248983 2194742753299263192373475)
      ·
        refine ⟨3292114129948894788560213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2194742753299263192373475 3292114129948894788560213)
        ·
          refine ⟨2411216403771163175215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3292114129948894788560213 2411216403771163175215)
          ·
            rfl

theorem cell22_1711629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 12].length) (baseStart_1711629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711629 prefixEnd_1711629 := by exact prefixLift 1711629
  have htrace : WordTrace (prefixWord ++ tailWord_1711629) baseStart_1711629 baseEnd_1711629 := by
    simpa [prefixWord, tailWord_1711629, baseEnd_1711629] using wordTrace_append hprefix tailTrace_1711629
  have hstable : (prefixWord ++ tailWord_1711629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711629).length < 2 ^ (prefixWord ++ tailWord_1711629).sum := by decide
  have hdescent : baseEnd_1711629 < baseStart_1711629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711644 : List Nat := [2, 2, 3, 1, 2, 1, 2, 3, 3, 3]
def baseStart_1711644 : Nat := 118140960795 + 1711644 * 2 ^ 59
def prefixEnd_1711644 : Nat := 4983230072969 + 3 ^ 40 * 1711644 * 2
def baseEnd_1711644 : Nat := 585930720922937612452199

theorem tailTrace_1711644 : CollatzResearch.WordTrace tailWord_1711644 prefixEnd_1711644 585930720922937612452199 := by
  unfold tailWord_1711644
  simp only [CollatzResearch.WordTrace]
  refine ⟨31214392705506794183542993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41619190274009058911390657 31214392705506794183542993)
  ·
    refine ⟨23410794529130095637657245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31214392705506794183542993 23410794529130095637657245)
    ·
      refine ⟨8779047948423785864121467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23410794529130095637657245 8779047948423785864121467)
      ·
        refine ⟨13168571922635678796182201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8779047948423785864121467 13168571922635678796182201)
        ·
          refine ⟨9876428941976759097136651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13168571922635678796182201 9876428941976759097136651)
          ·
            refine ⟨14814643412965138645704977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9876428941976759097136651 14814643412965138645704977)
            ·
              refine ⟨11110982559723853984278733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14814643412965138645704977 11110982559723853984278733)
              ·
                refine ⟨4166618459896445244104525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11110982559723853984278733 4166618459896445244104525)
                ·
                  refine ⟨1562481922461166966539197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4166618459896445244104525 1562481922461166966539197)
                  ·
                    refine ⟨585930720922937612452199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1562481922461166966539197 585930720922937612452199)
                    ·
                      rfl

theorem cell22_1711644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_1711644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711644 prefixEnd_1711644 := by exact prefixLift 1711644
  have htrace : WordTrace (prefixWord ++ tailWord_1711644) baseStart_1711644 baseEnd_1711644 := by
    simpa [prefixWord, tailWord_1711644, baseEnd_1711644] using wordTrace_append hprefix tailTrace_1711644
  have hstable : (prefixWord ++ tailWord_1711644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711644).length < 2 ^ (prefixWord ++ tailWord_1711644).sum := by decide
  have hdescent : baseEnd_1711644 < baseStart_1711644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711749 : List Nat := [1, 3, 1, 1, 4, 1, 3, 2, 2, 4]
def baseStart_1711749 : Nat := 118140960795 + 1711749 * 2 ^ 59
def prefixEnd_1711749 : Nat := 4983230072969 + 3 ^ 40 * 1711749 * 2
def baseEnd_1711749 : Nat := 585966664568752338576877

theorem tailTrace_1711749 : CollatzResearch.WordTrace tailWord_1711749 prefixEnd_1711749 585966664568752338576877 := by
  unfold tailWord_1711749
  simp only [CollatzResearch.WordTrace]
  refine ⟨62432615075633191299658301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41621743383755460866438867 62432615075633191299658301)
  ·
    refine ⟨23412230653362446737371863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62432615075633191299658301 23412230653362446737371863)
    ·
      refine ⟨35118345980043670106057795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23412230653362446737371863 35118345980043670106057795)
      ·
        refine ⟨52677518970065505159086693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35118345980043670106057795 52677518970065505159086693)
        ·
          refine ⟨9877034806887282217328755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52677518970065505159086693 9877034806887282217328755)
          ·
            refine ⟨14815552210330923325993133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9877034806887282217328755 14815552210330923325993133)
            ·
              refine ⟨5555832078874096247247425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14815552210330923325993133 5555832078874096247247425)
              ·
                refine ⟨4166874059155572185435569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5555832078874096247247425 4166874059155572185435569)
                ·
                  refine ⟨3125155544366679139076677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4166874059155572185435569 3125155544366679139076677)
                  ·
                    refine ⟨585966664568752338576877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3125155544366679139076677 585966664568752338576877)
                    ·
                      rfl

theorem cell22_1711749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_1711749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711749 prefixEnd_1711749 := by exact prefixLift 1711749
  have htrace : WordTrace (prefixWord ++ tailWord_1711749) baseStart_1711749 baseEnd_1711749 := by
    simpa [prefixWord, tailWord_1711749, baseEnd_1711749] using wordTrace_append hprefix tailTrace_1711749
  have hstable : (prefixWord ++ tailWord_1711749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711749).length < 2 ^ (prefixWord ++ tailWord_1711749).sum := by decide
  have hdescent : baseEnd_1711749 < baseStart_1711749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711768 : List Nat := [2, 1, 2, 4, 1, 2, 4, 1, 2, 3]
def baseStart_1711768 : Nat := 118140960795 + 1711768 * 2 ^ 59
def prefixEnd_1711768 : Nat := 4983230072969 + 3 ^ 40 * 1711768 * 2
def baseEnd_1711768 : Nat := 585973168657042622351819

theorem tailTrace_1711768 : CollatzResearch.WordTrace tailWord_1711768 prefixEnd_1711768 585973168657042622351819 := by
  unfold tailWord_1711768
  simp only [CollatzResearch.WordTrace]
  refine ⟨31216654031282178772299979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41622205375042905029733305 31216654031282178772299979)
  ·
    refine ⟨46824981046923268158449969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31216654031282178772299979 46824981046923268158449969)
    ·
      refine ⟨35118735785192451118837477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46824981046923268158449969 35118735785192451118837477)
      ·
        refine ⟨6584762959723584584782027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35118735785192451118837477 6584762959723584584782027)
        ·
          refine ⟨9877144439585376877173041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6584762959723584584782027 9877144439585376877173041)
          ·
            refine ⟨7407858329689032657879781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9877144439585376877173041 7407858329689032657879781)
            ·
              refine ⟨1388973436816693623352459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7407858329689032657879781 1388973436816693623352459)
              ·
                refine ⟨2083460155225040435028689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1388973436816693623352459 2083460155225040435028689)
                ·
                  refine ⟨1562595116418780326271517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2083460155225040435028689 1562595116418780326271517)
                  ·
                    refine ⟨585973168657042622351819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1562595116418780326271517 585973168657042622351819)
                    ·
                      rfl

theorem cell22_1711768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 2, 3].length) (baseStart_1711768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711768 prefixEnd_1711768 := by exact prefixLift 1711768
  have htrace : WordTrace (prefixWord ++ tailWord_1711768) baseStart_1711768 baseEnd_1711768 := by
    simpa [prefixWord, tailWord_1711768, baseEnd_1711768] using wordTrace_append hprefix tailTrace_1711768
  have hstable : (prefixWord ++ tailWord_1711768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711768).length < 2 ^ (prefixWord ++ tailWord_1711768).sum := by decide
  have hdescent : baseEnd_1711768 < baseStart_1711768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711779 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 5, 3]
def baseStart_1711779 : Nat := 118140960795 + 1711779 * 2 ^ 59
def prefixEnd_1711779 : Nat := 4983230072969 + 3 ^ 40 * 1711779 * 2
def baseEnd_1711779 : Nat := 585976934181842260326785

theorem tailTrace_1711779 : CollatzResearch.WordTrace tailWord_1711779 prefixEnd_1711779 585976934181842260326785 := by
  unfold tailWord_1711779
  simp only [CollatzResearch.WordTrace]
  refine ⟨62433709265524506423250391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41622472843683004282166927 62433709265524506423250391)
  ·
    refine ⟨93650563898286759634875587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62433709265524506423250391 93650563898286759634875587)
    ·
      refine ⟨140475845847430139452313381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93650563898286759634875587 140475845847430139452313381)
      ·
        refine ⟨26339221096393151147308759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140475845847430139452313381 26339221096393151147308759)
        ·
          refine ⟨39508831644589726720963139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26339221096393151147308759 39508831644589726720963139)
          ·
            refine ⟨59263247466884590081444709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39508831644589726720963139 59263247466884590081444709)
            ·
              refine ⟨11111858900040860640270883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59263247466884590081444709 11111858900040860640270883)
              ·
                refine ⟨16667788350061290960406325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11111858900040860640270883 16667788350061290960406325)
                ·
                  refine ⟨1562605157818246027538093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16667788350061290960406325 1562605157818246027538093)
                  ·
                    refine ⟨585976934181842260326785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1562605157818246027538093 585976934181842260326785)
                    ·
                      rfl

theorem cell22_1711779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 3].length) (baseStart_1711779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711779 prefixEnd_1711779 := by exact prefixLift 1711779
  have htrace : WordTrace (prefixWord ++ tailWord_1711779) baseStart_1711779 baseEnd_1711779 := by
    simpa [prefixWord, tailWord_1711779, baseEnd_1711779] using wordTrace_append hprefix tailTrace_1711779
  have hstable : (prefixWord ++ tailWord_1711779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711779).length < 2 ^ (prefixWord ++ tailWord_1711779).sum := by decide
  have hdescent : baseEnd_1711779 < baseStart_1711779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711792 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 9]
def baseStart_1711792 : Nat := 118140960795 + 1711792 * 2 ^ 59
def prefixEnd_1711792 : Nat := 4983230072969 + 3 ^ 40 * 1711792 * 2
def baseEnd_1711792 : Nat := 195327128115838186583915

theorem tailTrace_1711792 : CollatzResearch.WordTrace tailWord_1711792 prefixEnd_1711792 195327128115838186583915 := by
  unfold tailWord_1711792
  simp only [CollatzResearch.WordTrace]
  refine ⟨31217091707238704821736815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41622788942984939762315753 31217091707238704821736815)
  ·
    refine ⟨46825637560858057232605223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31217091707238704821736815 46825637560858057232605223)
    ·
      refine ⟨70238456341287085848907835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46825637560858057232605223 70238456341287085848907835)
      ·
        refine ⟨105357684511930628773361753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70238456341287085848907835 105357684511930628773361753)
        ·
          refine ⟨79018263383947971580021315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105357684511930628773361753 79018263383947971580021315)
          ·
            refine ⟨118527395075921957370031973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79018263383947971580021315 118527395075921957370031973)
            ·
              refine ⟨22223886576735367006880995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118527395075921957370031973 22223886576735367006880995)
              ·
                refine ⟨33335829865103050510321493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22223886576735367006880995 33335829865103050510321493)
                ·
                  refine ⟨195327128115838186583915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33335829865103050510321493 195327128115838186583915)
                  ·
                    rfl

theorem cell22_1711792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 9].length) (baseStart_1711792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711792 prefixEnd_1711792 := by exact prefixLift 1711792
  have htrace : WordTrace (prefixWord ++ tailWord_1711792) baseStart_1711792 baseEnd_1711792 := by
    simpa [prefixWord, tailWord_1711792, baseEnd_1711792] using wordTrace_append hprefix tailTrace_1711792
  have hstable : (prefixWord ++ tailWord_1711792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711792).length < 2 ^ (prefixWord ++ tailWord_1711792).sum := by decide
  have hdescent : baseEnd_1711792 < baseStart_1711792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711826 : List Nat := [3, 2, 2, 2, 2, 1, 2, 3, 5]
def baseStart_1711826 : Nat := 118140960795 + 1711826 * 2 ^ 59
def prefixEnd_1711826 : Nat := 4983230072969 + 3 ^ 40 * 1711826 * 2
def baseEnd_1711826 : Nat := 195331007747449934800547

theorem tailTrace_1711826 : CollatzResearch.WordTrace tailWord_1711826 prefixEnd_1711826 195331007747449934800547 := by
  unfold tailWord_1711826
  simp only [CollatzResearch.WordTrace]
  refine ⟨15608855874088558362552833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41623615664236155633474221 15608855874088558362552833)
  ·
    refine ⟨11706641905566418771914625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15608855874088558362552833 11706641905566418771914625)
    ·
      refine ⟨8779981429174814078935969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11706641905566418771914625 8779981429174814078935969)
      ·
        refine ⟨6584986071881110559201977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8779981429174814078935969 6584986071881110559201977)
        ·
          refine ⟨4938739553910832919401483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6584986071881110559201977 4938739553910832919401483)
          ·
            refine ⟨7408109330866249379102225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4938739553910832919401483 7408109330866249379102225)
            ·
              refine ⟨5556081998149687034326669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7408109330866249379102225 5556081998149687034326669)
              ·
                refine ⟨2083530749306132637872501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5556081998149687034326669 2083530749306132637872501)
                ·
                  refine ⟨195331007747449934800547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2083530749306132637872501 195331007747449934800547)
                  ·
                    rfl

theorem cell22_1711826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_1711826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711826 prefixEnd_1711826 := by exact prefixLift 1711826
  have htrace : WordTrace (prefixWord ++ tailWord_1711826) baseStart_1711826 baseEnd_1711826 := by
    simpa [prefixWord, tailWord_1711826, baseEnd_1711826] using wordTrace_append hprefix tailTrace_1711826
  have hstable : (prefixWord ++ tailWord_1711826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711826).length < 2 ^ (prefixWord ++ tailWord_1711826).sum := by decide
  have hdescent : baseEnd_1711826 < baseStart_1711826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711839 : List Nat := [1, 1, 2, 3, 2, 2, 1, 3, 3, 4]
def baseStart_1711839 : Nat := 118140960795 + 1711839 * 2 ^ 59
def prefixEnd_1711839 : Nat := 4983230072969 + 3 ^ 40 * 1711839 * 2
def baseEnd_1711839 : Nat := 585997473408022103826601

theorem tailTrace_1711839 : CollatzResearch.WordTrace tailWord_1711839 prefixEnd_1711839 585997473408022103826601 := by
  unfold tailWord_1711839
  simp only [CollatzResearch.WordTrace]
  refine ⟨62435897645307136670434571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41623931763538091113623047 62435897645307136670434571)
  ·
    refine ⟨93653846467960705005651857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62435897645307136670434571 93653846467960705005651857)
    ·
      refine ⟨70240384850970528754238893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93653846467960705005651857 70240384850970528754238893)
      ·
        refine ⟨26340144319113948282839585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70240384850970528754238893 26340144319113948282839585)
        ·
          refine ⟨19755108239335461212129689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26340144319113948282839585 19755108239335461212129689)
          ·
            refine ⟨14816331179501595909097267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19755108239335461212129689 14816331179501595909097267)
            ·
              refine ⟨22224496769252393863645901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14816331179501595909097267 22224496769252393863645901)
              ·
                refine ⟨8334186288469647698867213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22224496769252393863645901 8334186288469647698867213)
                ·
                  refine ⟨3125319858176117887075205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8334186288469647698867213 3125319858176117887075205)
                  ·
                    refine ⟨585997473408022103826601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3125319858176117887075205 585997473408022103826601)
                    ·
                      rfl

theorem cell22_1711839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 4].length) (baseStart_1711839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711839 prefixEnd_1711839 := by exact prefixLift 1711839
  have htrace : WordTrace (prefixWord ++ tailWord_1711839) baseStart_1711839 baseEnd_1711839 := by
    simpa [prefixWord, tailWord_1711839, baseEnd_1711839] using wordTrace_append hprefix tailTrace_1711839
  have hstable : (prefixWord ++ tailWord_1711839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711839).length < 2 ^ (prefixWord ++ tailWord_1711839).sum := by decide
  have hdescent : baseEnd_1711839 < baseStart_1711839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711847 : List Nat := [1, 1, 5, 4, 1, 1, 2, 3, 1, 3]
def baseStart_1711847 : Nat := 118140960795 + 1711847 * 2 ^ 59
def prefixEnd_1711847 : Nat := 4983230072969 + 3 ^ 40 * 1711847 * 2
def baseEnd_1711847 : Nat := 586000211971512749626577

theorem tailTrace_1711847 : CollatzResearch.WordTrace tailWord_1711847 prefixEnd_1711847 586000211971512749626577 := by
  unfold tailWord_1711847
  simp only [CollatzResearch.WordTrace]
  refine ⟨62436189429278154036725795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41624126286185436024483863 62436189429278154036725795)
  ·
    refine ⟨93654284143917231055088693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62436189429278154036725795 93654284143917231055088693)
    ·
      refine ⟨8780089138492240411414565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93654284143917231055088693 8780089138492240411414565)
      ·
        refine ⟨1646266713467295077140231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8780089138492240411414565 1646266713467295077140231)
        ·
          refine ⟨2469400070200942615710347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1646266713467295077140231 2469400070200942615710347)
          ·
            refine ⟨3704100105301413923565521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2469400070200942615710347 3704100105301413923565521)
            ·
              refine ⟨2778075078976060442674141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3704100105301413923565521 2778075078976060442674141)
              ·
                refine ⟨1041778154616022666002803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2778075078976060442674141 1041778154616022666002803)
                ·
                  refine ⟨1562667231924033999004205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1041778154616022666002803 1562667231924033999004205)
                  ·
                    refine ⟨586000211971512749626577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1562667231924033999004205 586000211971512749626577)
                    ·
                      rfl

theorem cell22_1711847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_1711847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711847 prefixEnd_1711847 := by exact prefixLift 1711847
  have htrace : WordTrace (prefixWord ++ tailWord_1711847) baseStart_1711847 baseEnd_1711847 := by
    simpa [prefixWord, tailWord_1711847, baseEnd_1711847] using wordTrace_append hprefix tailTrace_1711847
  have hstable : (prefixWord ++ tailWord_1711847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711847).length < 2 ^ (prefixWord ++ tailWord_1711847).sum := by decide
  have hdescent : baseEnd_1711847 < baseStart_1711847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711854 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 8]
def baseStart_1711854 : Nat := 118140960795 + 1711854 * 2 ^ 59
def prefixEnd_1711854 : Nat := 4983230072969 + 3 ^ 40 * 1711854 * 2
def baseEnd_1711854 : Nat := 195334202738189021567185

theorem tailTrace_1711854 : CollatzResearch.WordTrace tailWord_1711854 prefixEnd_1711854 195334202738189021567185 := by
  unfold tailWord_1711854
  simp only [CollatzResearch.WordTrace]
  refine ⟨7804555592531599279028827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41624296493501862821487077 7804555592531599279028827)
  ·
    refine ⟨11706833388797398918543241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7804555592531599279028827 11706833388797398918543241)
    ·
      refine ⟨8780125041598049188907431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11706833388797398918543241 8780125041598049188907431)
      ·
        refine ⟨13170187562397073783361147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8780125041598049188907431 13170187562397073783361147)
        ·
          refine ⟨19755281343595610675041721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13170187562397073783361147 19755281343595610675041721)
          ·
            refine ⟨14816461007696708006281291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19755281343595610675041721 14816461007696708006281291)
            ·
              refine ⟨22224691511545062009421937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14816461007696708006281291 22224691511545062009421937)
              ·
                refine ⟨16668518633658796507066453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22224691511545062009421937 16668518633658796507066453)
                ·
                  refine ⟨195334202738189021567185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16668518633658796507066453 195334202738189021567185)
                  ·
                    rfl

theorem cell22_1711854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_1711854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711854 prefixEnd_1711854 := by exact prefixLift 1711854
  have htrace : WordTrace (prefixWord ++ tailWord_1711854) baseStart_1711854 baseEnd_1711854 := by
    simpa [prefixWord, tailWord_1711854, baseEnd_1711854] using wordTrace_append hprefix tailTrace_1711854
  have hstable : (prefixWord ++ tailWord_1711854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711854).length < 2 ^ (prefixWord ++ tailWord_1711854).sum := by decide
  have hdescent : baseEnd_1711854 < baseStart_1711854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
