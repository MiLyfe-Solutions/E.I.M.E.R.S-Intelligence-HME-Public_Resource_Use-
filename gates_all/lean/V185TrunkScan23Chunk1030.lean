import V185TrunkScan23Chunk1029

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6097007 : List Nat := [1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 4]
def baseStart_6097007 : Nat := 118140960795 + 6097007 * 2 ^ 59
def prefixEnd_6097007 : Nat := 4983230072969 + 3 ^ 40 * 6097007 * 2
def baseEnd_6097007 : Nat := 3130695144827332165772881

theorem tailTrace_6097007 : CollatzResearch.WordTrace tailWord_6097007 prefixEnd_6097007 3130695144827332165772881 := by
  unfold tailWord_6097007
  simp only [CollatzResearch.WordTrace]
  refine ⟨222376114222592399739705275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148250742815061599826470183 222376114222592399739705275)
  ·
    refine ⟨333564171333888599609557913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222376114222592399739705275 333564171333888599609557913)
    ·
      refine ⟨250173128500416449707168435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333564171333888599609557913 250173128500416449707168435)
      ·
        refine ⟨375259692750624674560752653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250173128500416449707168435 375259692750624674560752653)
        ·
          refine ⟨140722384781484252960282245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 375259692750624674560752653 140722384781484252960282245)
          ·
            refine ⟨26385447146528297430052921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140722384781484252960282245 26385447146528297430052921)
            ·
              refine ⟨19789085359896223072539691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26385447146528297430052921 19789085359896223072539691)
              ·
                refine ⟨29683628039844334608809537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19789085359896223072539691 29683628039844334608809537)
                ·
                  refine ⟨22262721029883250956607153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29683628039844334608809537 22262721029883250956607153)
                  ·
                    refine ⟨16697040772412438217455365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22262721029883250956607153 16697040772412438217455365)
                    ·
                      refine ⟨3130695144827332165772881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16697040772412438217455365 3130695144827332165772881)
                      ·
                        rfl

theorem cell23_6097007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 4].length) (baseStart_6097007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097007 prefixEnd_6097007 := by exact prefixLift 6097007
  have htrace : WordTrace (prefixWord ++ tailWord_6097007) baseStart_6097007 baseEnd_6097007 := by
    simpa [prefixWord, tailWord_6097007, baseEnd_6097007] using wordTrace_append hprefix tailTrace_6097007
  have hstable : (prefixWord ++ tailWord_6097007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097007).length < 2 ^ (prefixWord ++ tailWord_6097007).sum := by decide
  have hdescent : baseEnd_6097007 < baseStart_6097007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097017 : List Nat := [1, 2, 1, 3, 4, 1, 2, 2, 7]
def baseStart_6097017 : Nat := 118140960795 + 6097017 * 2 ^ 59
def prefixEnd_6097017 : Nat := 4983230072969 + 3 ^ 40 * 6097017 * 2
def baseEnd_6097017 : Nat := 347855586625986347405315

theorem tailTrace_6097017 : CollatzResearch.WordTrace tailWord_6097017 prefixEnd_6097017 347855586625986347405315 := by
  unfold tailWord_6097017
  simp only [CollatzResearch.WordTrace]
  refine ⟨222376478952556171447569305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148250985968370780965046203 222376478952556171447569305)
  ·
    refine ⟨166782359214417128585676979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222376478952556171447569305 166782359214417128585676979)
    ·
      refine ⟨250173538821625692878515469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166782359214417128585676979 250173538821625692878515469)
      ·
        refine ⟨93815077058109634829443301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250173538821625692878515469 93815077058109634829443301)
        ·
          refine ⟨17590326948395556530520619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93815077058109634829443301 17590326948395556530520619)
          ·
            refine ⟨26385490422593334795780929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17590326948395556530520619 26385490422593334795780929)
            ·
              refine ⟨19789117816945001096835697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26385490422593334795780929 19789117816945001096835697)
              ·
                refine ⟨14841838362708750822626773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19789117816945001096835697 14841838362708750822626773)
                ·
                  refine ⟨347855586625986347405315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14841838362708750822626773 347855586625986347405315)
                  ·
                    rfl

theorem cell23_6097017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 7].length) (baseStart_6097017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097017 prefixEnd_6097017 := by exact prefixLift 6097017
  have htrace : WordTrace (prefixWord ++ tailWord_6097017) baseStart_6097017 baseEnd_6097017 := by
    simpa [prefixWord, tailWord_6097017, baseEnd_6097017] using wordTrace_append hprefix tailTrace_6097017
  have hstable : (prefixWord ++ tailWord_6097017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097017).length < 2 ^ (prefixWord ++ tailWord_6097017).sum := by decide
  have hdescent : baseEnd_6097017 < baseStart_6097017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097057 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 1, 1, 7]
def baseStart_6097057 : Nat := 118140960795 + 6097057 * 2 ^ 59
def prefixEnd_6097057 : Nat := 4983230072969 + 3 ^ 40 * 6097057 * 2
def baseEnd_6097057 : Nat := 3130720818860056970147651

theorem tailTrace_6097057 : CollatzResearch.WordTrace tailWord_6097057 prefixEnd_6097057 3130720818860056970147651 := by
  unfold tailWord_6097057
  simp only [CollatzResearch.WordTrace]
  refine ⟨222377937872411258279025425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148251958581607505519350283 222377937872411258279025425)
  ·
    refine ⟨166783453404308443709269069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222377937872411258279025425 166783453404308443709269069)
    ·
      refine ⟨62543795026615666390975901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166783453404308443709269069 62543795026615666390975901)
      ·
        refine ⟨23453923134980874896615963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62543795026615666390975901 23453923134980874896615963)
        ·
          refine ⟨35180884702471312344923945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23453923134980874896615963 35180884702471312344923945)
          ·
            refine ⟨26385663526853484258692959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35180884702471312344923945 26385663526853484258692959)
            ·
              refine ⟨39578495290280226388039439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26385663526853484258692959 39578495290280226388039439)
              ·
                refine ⟨59367742935420339582059159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39578495290280226388039439 59367742935420339582059159)
                ·
                  refine ⟨89051614403130509373088739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59367742935420339582059159 89051614403130509373088739)
                  ·
                    refine ⟨133577421604695764059633109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89051614403130509373088739 133577421604695764059633109)
                    ·
                      refine ⟨3130720818860056970147651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 133577421604695764059633109 3130720818860056970147651)
                      ·
                        rfl

theorem cell23_6097057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_6097057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097057 prefixEnd_6097057 := by exact prefixLift 6097057
  have htrace : WordTrace (prefixWord ++ tailWord_6097057) baseStart_6097057 baseEnd_6097057 := by
    simpa [prefixWord, tailWord_6097057, baseEnd_6097057] using wordTrace_append hprefix tailTrace_6097057
  have hstable : (prefixWord ++ tailWord_6097057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097057).length < 2 ^ (prefixWord ++ tailWord_6097057).sum := by decide
  have hdescent : baseEnd_6097057 < baseStart_6097057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097138 : List Nat := [3, 2, 1, 3, 2, 3, 1, 1, 2, 2, 3]
def baseStart_6097138 : Nat := 118140960795 + 6097138 * 2 ^ 59
def prefixEnd_6097138 : Nat := 4983230072969 + 3 ^ 40 * 6097138 * 2
def baseEnd_6097138 : Nat := 3130762410793071153234779

theorem tailTrace_6097138 : CollatzResearch.WordTrace tailWord_6097138 prefixEnd_6097138 3130762410793071153234779 := by
  unfold tailWord_6097138
  simp only [CollatzResearch.WordTrace]
  refine ⟨55595223046279452278181017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148253928123411872741816045 55595223046279452278181017)
  ·
    refine ⟨41696417284709589208635763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55595223046279452278181017 41696417284709589208635763)
    ·
      refine ⟨62544625927064383812953645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41696417284709589208635763 62544625927064383812953645)
      ·
        refine ⟨23454234722649143929857617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62544625927064383812953645 23454234722649143929857617)
        ·
          refine ⟨17590676041986857947393213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23454234722649143929857617 17590676041986857947393213)
          ·
            refine ⟨6596503515745071730272455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17590676041986857947393213 6596503515745071730272455)
            ·
              refine ⟨9894755273617607595408683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6596503515745071730272455 9894755273617607595408683)
              ·
                refine ⟨14842132910426411393113025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9894755273617607595408683 14842132910426411393113025)
                ·
                  refine ⟨11131599682819808544834769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14842132910426411393113025 11131599682819808544834769)
                  ·
                    refine ⟨8348699762114856408626077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11131599682819808544834769 8348699762114856408626077)
                    ·
                      refine ⟨3130762410793071153234779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8348699762114856408626077 3130762410793071153234779)
                      ·
                        rfl

theorem cell23_6097138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_6097138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097138 prefixEnd_6097138 := by exact prefixLift 6097138
  have htrace : WordTrace (prefixWord ++ tailWord_6097138) baseStart_6097138 baseEnd_6097138 := by
    simpa [prefixWord, tailWord_6097138, baseEnd_6097138] using wordTrace_append hprefix tailTrace_6097138
  have hstable : (prefixWord ++ tailWord_6097138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097138).length < 2 ^ (prefixWord ++ tailWord_6097138).sum := by decide
  have hdescent : baseEnd_6097138 < baseStart_6097138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097167 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 3, 6]
def baseStart_6097167 : Nat := 118140960795 + 6097167 * 2 ^ 59
def prefixEnd_6097167 : Nat := 4983230072969 + 3 ^ 40 * 6097167 * 2
def baseEnd_6097167 : Nat := 1043592433910683846590715

theorem tailTrace_6097167 : CollatzResearch.WordTrace tailWord_6097167 prefixEnd_6097167 1043592433910683846590715 := by
  unfold tailWord_6097167
  simp only [CollatzResearch.WordTrace]
  refine ⟨222381949902012747065529755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148254633268008498043686503 222381949902012747065529755)
  ·
    refine ⟨333572924853019120598294633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222381949902012747065529755 333572924853019120598294633)
    ·
      refine ⟨250179693639764340448720975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333572924853019120598294633 250179693639764340448720975)
      ·
        refine ⟨375269540459646510673081463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250179693639764340448720975 375269540459646510673081463)
        ·
          refine ⟨562904310689469766009622195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375269540459646510673081463 562904310689469766009622195)
          ·
            refine ⟨844356466034204649014433293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562904310689469766009622195 844356466034204649014433293)
            ·
              refine ⟨316633674762826743380412485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 844356466034204649014433293 316633674762826743380412485)
              ·
                refine ⟨59368814018030014383827341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 316633674762826743380412485 59368814018030014383827341)
                ·
                  refine ⟨22263305256761255393935253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59368814018030014383827341 22263305256761255393935253)
                  ·
                    refine ⟨1043592433910683846590715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22263305256761255393935253 1043592433910683846590715)
                    ·
                      rfl

theorem cell23_6097167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 6].length) (baseStart_6097167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097167 prefixEnd_6097167 := by exact prefixLift 6097167
  have htrace : WordTrace (prefixWord ++ tailWord_6097167) baseStart_6097167 baseEnd_6097167 := by
    simpa [prefixWord, tailWord_6097167, baseEnd_6097167] using wordTrace_append hprefix tailTrace_6097167
  have hstable : (prefixWord ++ tailWord_6097167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097167).length < 2 ^ (prefixWord ++ tailWord_6097167).sum := by decide
  have hdescent : baseEnd_6097167 < baseStart_6097167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097202 : List Nat := [3, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3]
def baseStart_6097202 : Nat := 118140960795 + 6097202 * 2 ^ 59
def prefixEnd_6097202 : Nat := 4983230072969 + 3 ^ 40 * 6097202 * 2
def baseEnd_6097202 : Nat := 3130795273554958902834485

theorem tailTrace_6097202 : CollatzResearch.WordTrace tailWord_6097202 prefixEnd_6097202 3130795273554958902834485 := by
  unfold tailWord_6097202
  simp only [CollatzResearch.WordTrace]
  refine ⟨55595806614221487010763465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148255484304590632028702573 55595806614221487010763465)
  ·
    refine ⟨41696854960666115258072599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55595806614221487010763465 41696854960666115258072599)
    ·
      refine ⟨62545282440999172887108899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41696854960666115258072599 62545282440999172887108899)
      ·
        refine ⟨93817923661498759330663349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62545282440999172887108899 93817923661498759330663349)
        ·
          refine ⟨8795430343265508687249689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93817923661498759330663349 8795430343265508687249689)
          ·
            refine ⟨6596572757449131515437267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8795430343265508687249689 6596572757449131515437267)
            ·
              refine ⟨9894859136173697273155901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6596572757449131515437267 9894859136173697273155901)
              ·
                refine ⟨3710572176065136477433463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9894859136173697273155901 3710572176065136477433463)
                ·
                  refine ⟨5565858264097704716150195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3710572176065136477433463 5565858264097704716150195)
                  ·
                    refine ⟨8348787396146557074225293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5565858264097704716150195 8348787396146557074225293)
                    ·
                      refine ⟨3130795273554958902834485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8348787396146557074225293 3130795273554958902834485)
                      ·
                        rfl

theorem cell23_6097202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3].length) (baseStart_6097202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097202 prefixEnd_6097202 := by exact prefixLift 6097202
  have htrace : WordTrace (prefixWord ++ tailWord_6097202) baseStart_6097202 baseEnd_6097202 := by
    simpa [prefixWord, tailWord_6097202, baseEnd_6097202] using wordTrace_append hprefix tailTrace_6097202
  have hstable : (prefixWord ++ tailWord_6097202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097202).length < 2 ^ (prefixWord ++ tailWord_6097202).sum := by decide
  have hdescent : baseEnd_6097202 < baseStart_6097202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097214 : List Nat := [4, 2, 1, 2, 1, 2, 11]
def baseStart_6097214 : Nat := 118140960795 + 6097214 * 2 ^ 59
def prefixEnd_6097214 : Nat := 4983230072969 + 3 ^ 40 * 6097214 * 2
def baseEnd_6097214 : Nat := 38651869571886578467709

theorem tailTrace_6097214 : CollatzResearch.WordTrace tailWord_6097214 prefixEnd_6097214 38651869571886578467709 := by
  unfold tailWord_6097214
  simp only [CollatzResearch.WordTrace]
  refine ⟨27797958016605309261561337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148255776088561649394993797 27797958016605309261561337)
  ·
    refine ⟨20848468512453981946171003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27797958016605309261561337 20848468512453981946171003)
    ·
      refine ⟨31272702768680972919256505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20848468512453981946171003 31272702768680972919256505)
      ·
        refine ⟨23454527076510729689442379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31272702768680972919256505 23454527076510729689442379)
        ·
          refine ⟨35181790614766094534163569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23454527076510729689442379 35181790614766094534163569)
          ·
            refine ⟨26386342961074570900622677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35181790614766094534163569 26386342961074570900622677)
            ·
              refine ⟨38651869571886578467709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26386342961074570900622677 38651869571886578467709)
              ·
                rfl

theorem cell23_6097214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 11].length) (baseStart_6097214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097214 prefixEnd_6097214 := by exact prefixLift 6097214
  have htrace : WordTrace (prefixWord ++ tailWord_6097214) baseStart_6097214 baseEnd_6097214 := by
    simpa [prefixWord, tailWord_6097214, baseEnd_6097214] using wordTrace_append hprefix tailTrace_6097214
  have hstable : (prefixWord ++ tailWord_6097214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097214).length < 2 ^ (prefixWord ++ tailWord_6097214).sum := by decide
  have hdescent : baseEnd_6097214 < baseStart_6097214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097246 : List Nat := [4, 4, 2, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_6097246 : Nat := 118140960795 + 6097246 * 2 ^ 59
def prefixEnd_6097246 : Nat := 4983230072969 + 3 ^ 40 * 6097246 * 2
def baseEnd_6097246 : Nat := 3130817866703756730684283

theorem tailTrace_6097246 : CollatzResearch.WordTrace tailWord_6097246 prefixEnd_6097246 3130817866703756730684283 := by
  unfold tailWord_6097246
  simp only [CollatzResearch.WordTrace]
  refine ⟨27798103908590817944706949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148256554179151029038437061 27798103908590817944706949)
  ·
    refine ⟨5212144482860778364632553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27798103908590817944706949 5212144482860778364632553)
    ·
      refine ⟨3909108362145583773474415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5212144482860778364632553 3909108362145583773474415)
      ·
        refine ⟨5863662543218375660211623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3909108362145583773474415 5863662543218375660211623)
        ·
          refine ⟨8795493814827563490317435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5863662543218375660211623 8795493814827563490317435)
          ·
            refine ⟨13193240722241345235476153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8795493814827563490317435 13193240722241345235476153)
            ·
              refine ⟨9894930541681008926607115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13193240722241345235476153 9894930541681008926607115)
              ·
                refine ⟨14842395812521513389910673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9894930541681008926607115 14842395812521513389910673)
                ·
                  refine ⟨11131796859391135042433005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14842395812521513389910673 11131796859391135042433005)
                  ·
                    refine ⟨4174423822271675640912377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11131796859391135042433005 4174423822271675640912377)
                    ·
                      refine ⟨3130817866703756730684283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4174423822271675640912377 3130817866703756730684283)
                      ·
                        rfl

theorem cell23_6097246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_6097246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097246 prefixEnd_6097246 := by exact prefixLift 6097246
  have htrace : WordTrace (prefixWord ++ tailWord_6097246) baseStart_6097246 baseEnd_6097246 := by
    simpa [prefixWord, tailWord_6097246, baseEnd_6097246] using wordTrace_append hprefix tailTrace_6097246
  have hstable : (prefixWord ++ tailWord_6097246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097246).length < 2 ^ (prefixWord ++ tailWord_6097246).sum := by decide
  have hdescent : baseEnd_6097246 < baseStart_6097246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097258 : List Nat := [3, 1, 3, 3, 1, 2, 1, 2, 1, 3, 3]
def baseStart_6097258 : Nat := 118140960795 + 6097258 * 2 ^ 59
def prefixEnd_6097258 : Nat := 4983230072969 + 3 ^ 40 * 6097258 * 2
def baseEnd_6097258 : Nat := 3130824028471610683734227

theorem tailTrace_6097258 : CollatzResearch.WordTrace tailWord_6097258 prefixEnd_6097258 3130824028471610683734227 := by
  unfold tailWord_6097258
  simp only [CollatzResearch.WordTrace]
  refine ⟨55596317236170767401773107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148256845963122046404728285 55596317236170767401773107)
  ·
    refine ⟨83394475854256151102659661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55596317236170767401773107 83394475854256151102659661)
    ·
      refine ⟨31272928445346056663497373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83394475854256151102659661 31272928445346056663497373)
      ·
        refine ⟨11727348167004771248811515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31272928445346056663497373 11727348167004771248811515)
        ·
          refine ⟨17591022250507156873217273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11727348167004771248811515 17591022250507156873217273)
          ·
            refine ⟨13193266687880367654912955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17591022250507156873217273 13193266687880367654912955)
            ·
              refine ⟨19789900031820551482369433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13193266687880367654912955 19789900031820551482369433)
              ·
                refine ⟨14842425023865413611777075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19789900031820551482369433 14842425023865413611777075)
                ·
                  refine ⟨22263637535798120417665613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14842425023865413611777075 22263637535798120417665613)
                  ·
                    refine ⟨8348864075924295156624605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22263637535798120417665613 8348864075924295156624605)
                    ·
                      refine ⟨3130824028471610683734227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8348864075924295156624605 3130824028471610683734227)
                      ·
                        rfl

theorem cell23_6097258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_6097258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097258 prefixEnd_6097258 := by exact prefixLift 6097258
  have htrace : WordTrace (prefixWord ++ tailWord_6097258) baseStart_6097258 baseEnd_6097258 := by
    simpa [prefixWord, tailWord_6097258, baseEnd_6097258] using wordTrace_append hprefix tailTrace_6097258
  have hstable : (prefixWord ++ tailWord_6097258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097258).length < 2 ^ (prefixWord ++ tailWord_6097258).sum := by decide
  have hdescent : baseEnd_6097258 < baseStart_6097258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097281 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_6097281 : Nat := 118140960795 + 6097281 * 2 ^ 59
def prefixEnd_6097281 : Nat := 4983230072969 + 3 ^ 40 * 6097281 * 2
def baseEnd_6097281 : Nat := 3130835838526664093746621

theorem tailTrace_6097281 : CollatzResearch.WordTrace tailWord_6097281 prefixEnd_6097281 3130835838526664093746621 := by
  unfold tailWord_6097281
  simp only [CollatzResearch.WordTrace]
  refine ⟨222386107823599744535179697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148257405215733163023453131 222386107823599744535179697)
  ·
    refine ⟨166789580867699808401384773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222386107823599744535179697 166789580867699808401384773)
    ·
      refine ⟨31273046412693714075259645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166789580867699808401384773 31273046412693714075259645)
      ·
        refine ⟨11727392404760142778222367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31273046412693714075259645 11727392404760142778222367)
        ·
          refine ⟨17591088607140214167333551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11727392404760142778222367 17591088607140214167333551)
          ·
            refine ⟨26386632910710321251000327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17591088607140214167333551 26386632910710321251000327)
            ·
              refine ⟨39579949366065481876500491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26386632910710321251000327 39579949366065481876500491)
              ·
                refine ⟨59369924049098222814750737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39579949366065481876500491 59369924049098222814750737)
                ·
                  refine ⟨44527443036823667111063053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59369924049098222814750737 44527443036823667111063053)
                  ·
                    refine ⟨16697791138808875166648645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44527443036823667111063053 16697791138808875166648645)
                    ·
                      refine ⟨3130835838526664093746621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16697791138808875166648645 3130835838526664093746621)
                      ·
                        rfl

theorem cell23_6097281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_6097281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097281 prefixEnd_6097281 := by exact prefixLift 6097281
  have htrace : WordTrace (prefixWord ++ tailWord_6097281) baseStart_6097281 baseEnd_6097281 := by
    simpa [prefixWord, tailWord_6097281, baseEnd_6097281] using wordTrace_append hprefix tailTrace_6097281
  have hstable : (prefixWord ++ tailWord_6097281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097281).length < 2 ^ (prefixWord ++ tailWord_6097281).sum := by decide
  have hdescent : baseEnd_6097281 < baseStart_6097281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097344 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 7]
def baseStart_6097344 : Nat := 118140960795 + 6097344 * 2 ^ 59
def prefixEnd_6097344 : Nat := 4983230072969 + 3 ^ 40 * 6097344 * 2
def baseEnd_6097344 : Nat := 3130868187807897347258831

theorem tailTrace_6097344 : CollatzResearch.WordTrace tailWord_6097344 prefixEnd_6097344 3130868187807897347258831 := by
  unfold tailWord_6097344
  simp only [CollatzResearch.WordTrace]
  refine ⟨111194202811185753147361543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148258937081581004196482057 111194202811185753147361543)
  ·
    refine ⟨166791304216778629721042315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111194202811185753147361543 166791304216778629721042315)
    ·
      refine ⟨250186956325167944581563473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166791304216778629721042315 250186956325167944581563473)
      ·
        refine ⟨187640217243875958436172605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250186956325167944581563473 187640217243875958436172605)
        ·
          refine ⟨70365081466453484413564727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187640217243875958436172605 70365081466453484413564727)
          ·
            refine ⟨105547622199680226620347091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70365081466453484413564727 105547622199680226620347091)
            ·
              refine ⟨158321433299520339930520637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105547622199680226620347091 158321433299520339930520637)
              ·
                refine ⟨59370537487320127473945239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158321433299520339930520637 59370537487320127473945239)
                ·
                  refine ⟨89055806230980191210917859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59370537487320127473945239 89055806230980191210917859)
                  ·
                    refine ⟨133583709346470286816376789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89055806230980191210917859 133583709346470286816376789)
                    ·
                      refine ⟨3130868187807897347258831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 133583709346470286816376789 3130868187807897347258831)
                      ·
                        rfl

theorem cell23_6097344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_6097344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097344 prefixEnd_6097344 := by exact prefixLift 6097344
  have htrace : WordTrace (prefixWord ++ tailWord_6097344) baseStart_6097344 baseEnd_6097344 := by
    simpa [prefixWord, tailWord_6097344, baseEnd_6097344] using wordTrace_append hprefix tailTrace_6097344
  have hstable : (prefixWord ++ tailWord_6097344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097344).length < 2 ^ (prefixWord ++ tailWord_6097344).sum := by decide
  have hdescent : baseEnd_6097344 < baseStart_6097344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097371 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 2, 10, 2]
def baseStart_6097371 : Nat := 118140960795 + 6097371 * 2 ^ 59
def prefixEnd_6097371 : Nat := 4983230072969 + 3 ^ 40 * 6097371 * 2
def baseEnd_6097371 : Nat := 3130882051785568741621207

theorem tailTrace_6097371 : CollatzResearch.WordTrace tailWord_6097371 prefixEnd_6097371 3130882051785568741621207 := by
  unfold tailWord_6097371
  simp only [CollatzResearch.WordTrace]
  refine ⟨222389390393273689905955967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148259593595515793270637311 222389390393273689905955967)
  ·
    refine ⟨333584085589910534858933951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222389390393273689905955967 333584085589910534858933951)
    ·
      refine ⟨500376128384865802288400927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333584085589910534858933951 500376128384865802288400927)
      ·
        refine ⟨750564192577298703432601391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500376128384865802288400927 750564192577298703432601391)
        ·
          refine ⟨1125846288865948055148902087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750564192577298703432601391 1125846288865948055148902087)
          ·
            refine ⟨1688769433298922082723353131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1125846288865948055148902087 1688769433298922082723353131)
            ·
              refine ⟨2533154149948383124085029697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1688769433298922082723353131 2533154149948383124085029697)
              ·
                refine ⟨1899865612461287343063772273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2533154149948383124085029697 1899865612461287343063772273)
                ·
                  refine ⟨1424899209345965507297829205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1899865612461287343063772273 1424899209345965507297829205)
                  ·
                    refine ⟨4174509402380758322161609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1424899209345965507297829205 4174509402380758322161609)
                    ·
                      refine ⟨3130882051785568741621207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4174509402380758322161609 3130882051785568741621207)
                      ·
                        rfl

theorem cell23_6097371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 10, 2].length) (baseStart_6097371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097371 prefixEnd_6097371 := by exact prefixLift 6097371
  have htrace : WordTrace (prefixWord ++ tailWord_6097371) baseStart_6097371 baseEnd_6097371 := by
    simpa [prefixWord, tailWord_6097371, baseEnd_6097371] using wordTrace_append hprefix tailTrace_6097371
  have hstable : (prefixWord ++ tailWord_6097371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097371).length < 2 ^ (prefixWord ++ tailWord_6097371).sum := by decide
  have hdescent : baseEnd_6097371 < baseStart_6097371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097411 : List Nat := [1, 1, 1, 3, 2, 1, 5, 3, 6]
def baseStart_6097411 : Nat := 118140960795 + 6097411 * 2 ^ 59
def prefixEnd_6097411 : Nat := 4983230072969 + 3 ^ 40 * 6097411 * 2
def baseEnd_6097411 : Nat := 347878065667972065013447

theorem tailTrace_6097411 : CollatzResearch.WordTrace tailWord_6097411 prefixEnd_6097411 347878065667972065013447 := by
  unfold tailWord_6097411
  simp only [CollatzResearch.WordTrace]
  refine ⟨222390849313128776737412087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148260566208752517824941391 222390849313128776737412087)
  ·
    refine ⟨333586273969693165106118131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222390849313128776737412087 333586273969693165106118131)
    ·
      refine ⟨500379410954539747659177197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333586273969693165106118131 500379410954539747659177197)
      ·
        refine ⟨187642279107952405372191449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 500379410954539747659177197 187642279107952405372191449)
        ·
          refine ⟨140731709330964304029143587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187642279107952405372191449 140731709330964304029143587)
          ·
            refine ⟨211097563996446456043715381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140731709330964304029143587 211097563996446456043715381)
            ·
              refine ⟨19790396624666855254098317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 211097563996446456043715381 19790396624666855254098317)
              ·
                refine ⟨7421398734250070720286869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19790396624666855254098317 7421398734250070720286869)
                ·
                  refine ⟨347878065667972065013447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7421398734250070720286869 347878065667972065013447)
                  ·
                    rfl

theorem cell23_6097411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 6].length) (baseStart_6097411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097411 prefixEnd_6097411 := by exact prefixLift 6097411
  have htrace : WordTrace (prefixWord ++ tailWord_6097411) baseStart_6097411 baseEnd_6097411 := by
    simpa [prefixWord, tailWord_6097411, baseEnd_6097411] using wordTrace_append hprefix tailTrace_6097411
  have hstable : (prefixWord ++ tailWord_6097411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097411).length < 2 ^ (prefixWord ++ tailWord_6097411).sum := by decide
  have hdescent : baseEnd_6097411 < baseStart_6097411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097476 : List Nat := [2, 3, 5, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_6097476 : Nat := 118140960795 + 6097476 * 2 ^ 59
def prefixEnd_6097476 : Nat := 4983230072969 + 3 ^ 40 * 6097476 * 2
def baseEnd_6097476 : Nat := 3130935967254290830808225

theorem tailTrace_6097476 : CollatzResearch.WordTrace tailWord_6097476 prefixEnd_6097476 3130935967254290830808225 := by
  unfold tailWord_6097476
  simp only [CollatzResearch.WordTrace]
  refine ⟨111196610028946646419264141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148262146705262195225685521 111196610028946646419264141)
  ·
    refine ⟨41698728760854992407224053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111196610028946646419264141 41698728760854992407224053)
    ·
      refine ⟨3909255821330155538177255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41698728760854992407224053 3909255821330155538177255)
      ·
        refine ⟨5863883731995233307265883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3909255821330155538177255 5863883731995233307265883)
        ·
          refine ⟨8795825597992849960898825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5863883731995233307265883 8795825597992849960898825)
          ·
            refine ⟨6596869198494637470674119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8795825597992849960898825 6596869198494637470674119)
            ·
              refine ⟨9895303797741956206011179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6596869198494637470674119 9895303797741956206011179)
              ·
                refine ⟨14842955696612934309016769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9895303797741956206011179 14842955696612934309016769)
                ·
                  refine ⟨11132216772459700731762577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14842955696612934309016769 11132216772459700731762577)
                  ·
                    refine ⟨8349162579344775548821933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11132216772459700731762577 8349162579344775548821933)
                    ·
                      refine ⟨3130935967254290830808225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8349162579344775548821933 3130935967254290830808225)
                      ·
                        rfl

theorem cell23_6097476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_6097476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097476 prefixEnd_6097476 := by exact prefixLift 6097476
  have htrace : WordTrace (prefixWord ++ tailWord_6097476) baseStart_6097476 baseEnd_6097476 := by
    simpa [prefixWord, tailWord_6097476, baseEnd_6097476] using wordTrace_append hprefix tailTrace_6097476
  have hstable : (prefixWord ++ tailWord_6097476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097476).length < 2 ^ (prefixWord ++ tailWord_6097476).sum := by decide
  have hdescent : baseEnd_6097476 < baseStart_6097476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097482 : List Nat := [3, 1, 2, 1, 1, 6, 1, 1, 2, 3, 2]
def baseStart_6097482 : Nat := 118140960795 + 6097482 * 2 ^ 59
def prefixEnd_6097482 : Nat := 4983230072969 + 3 ^ 40 * 6097482 * 2
def baseEnd_6097482 : Nat := 3130939048138217807333197

theorem tailTrace_6097482 : CollatzResearch.WordTrace tailWord_6097482 prefixEnd_6097482 3130939048138217807333197 := by
  unfold tailWord_6097482
  simp only [CollatzResearch.WordTrace]
  refine ⟨55598359723967888965811675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148262292597247703908831133 55598359723967888965811675)
  ·
    refine ⟨83397539585951833448717513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55598359723967888965811675 83397539585951833448717513)
    ·
      refine ⟨62548154689463875086538135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83397539585951833448717513 62548154689463875086538135)
      ·
        refine ⟨93822232034195812629807203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62548154689463875086538135 93822232034195812629807203)
        ·
          refine ⟨140733348051293718944710805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93822232034195812629807203 140733348051293718944710805)
          ·
            refine ⟨6596875689904393075533319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 140733348051293718944710805 6596875689904393075533319)
            ·
              refine ⟨9895313534856589613299979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6596875689904393075533319 9895313534856589613299979)
              ·
                refine ⟨14842970302284884419949969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9895313534856589613299979 14842970302284884419949969)
                ·
                  refine ⟨11132227726713663314962477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14842970302284884419949969 11132227726713663314962477)
                  ·
                    refine ⟨4174585397517623743110929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11132227726713663314962477 4174585397517623743110929)
                    ·
                      refine ⟨3130939048138217807333197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4174585397517623743110929 3130939048138217807333197)
                      ·
                        rfl

theorem cell23_6097482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 2, 3, 2].length) (baseStart_6097482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097482 prefixEnd_6097482 := by exact prefixLift 6097482
  have htrace : WordTrace (prefixWord ++ tailWord_6097482) baseStart_6097482 baseEnd_6097482 := by
    simpa [prefixWord, tailWord_6097482, baseEnd_6097482] using wordTrace_append hprefix tailTrace_6097482
  have hstable : (prefixWord ++ tailWord_6097482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097482).length < 2 ^ (prefixWord ++ tailWord_6097482).sum := by decide
  have hdescent : baseEnd_6097482 < baseStart_6097482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097492 : List Nat := [2, 4, 1, 1, 1, 5, 2, 1, 1, 5]
def baseStart_6097492 : Nat := 118140960795 + 6097492 * 2 ^ 59
def prefixEnd_6097492 : Nat := 4983230072969 + 3 ^ 40 * 6097492 * 2
def baseEnd_6097492 : Nat := 1043648060981587589402717

theorem tailTrace_6097492 : CollatzResearch.WordTrace tailWord_6097492 prefixEnd_6097492 1043648060981587589402717 := by
  unfold tailWord_6097492
  simp only [CollatzResearch.WordTrace]
  refine ⟨111196901812917663785555365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148262535750556885047407153 111196901812917663785555365)
  ·
    refine ⟨20849419089922061959791631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111196901812917663785555365 20849419089922061959791631)
    ·
      refine ⟨31274128634883092939687447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20849419089922061959791631 31274128634883092939687447)
      ·
        refine ⟨46911192952324639409531171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31274128634883092939687447 46911192952324639409531171)
        ·
          refine ⟨70366789428486959114296757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46911192952324639409531171 70366789428486959114296757)
          ·
            refine ⟨6596886508920652416965321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70366789428486959114296757 6596886508920652416965321)
            ·
              refine ⟨4947664881690489312723991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6596886508920652416965321 4947664881690489312723991)
              ·
                refine ⟨7421497322535733969085987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4947664881690489312723991 7421497322535733969085987)
                ·
                  refine ⟨11132245983803600953628981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7421497322535733969085987 11132245983803600953628981)
                  ·
                    refine ⟨1043648060981587589402717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11132245983803600953628981 1043648060981587589402717)
                    ·
                      rfl

theorem cell23_6097492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_6097492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097492 prefixEnd_6097492 := by exact prefixLift 6097492
  have htrace : WordTrace (prefixWord ++ tailWord_6097492) baseStart_6097492 baseEnd_6097492 := by
    simpa [prefixWord, tailWord_6097492, baseEnd_6097492] using wordTrace_append hprefix tailTrace_6097492
  have hstable : (prefixWord ++ tailWord_6097492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097492).length < 2 ^ (prefixWord ++ tailWord_6097492).sum := by decide
  have hdescent : baseEnd_6097492 < baseStart_6097492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097495 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 5, 2, 2]
def baseStart_6097495 : Nat := 118140960795 + 6097495 * 2 ^ 59
def prefixEnd_6097495 : Nat := 4983230072969 + 3 ^ 40 * 6097495 * 2
def baseEnd_6097495 : Nat := 3130945723386726256470637

theorem tailTrace_6097495 : CollatzResearch.WordTrace tailWord_6097495 prefixEnd_6097495 3130945723386726256470637 := by
  unfold tailWord_6097495
  simp only [CollatzResearch.WordTrace]
  refine ⟨222393913044824459083469939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148262608696549639388979959 222393913044824459083469939)
  ·
    refine ⟨333590869567236688625204909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222393913044824459083469939 333590869567236688625204909)
    ·
      refine ⟨125096576087713758234451841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333590869567236688625204909 125096576087713758234451841)
      ·
        refine ⟨93822432065785318675838881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125096576087713758234451841 93822432065785318675838881)
        ·
          refine ⟨70366824049338989006879161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93822432065785318675838881 70366824049338989006879161)
          ·
            refine ⟨52775118037004241755159371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70366824049338989006879161 52775118037004241755159371)
            ·
              refine ⟨79162677055506362632739057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52775118037004241755159371 79162677055506362632739057)
              ·
                refine ⟨59372007791629771974554293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79162677055506362632739057 59372007791629771974554293)
                ·
                  refine ⟨5566125730465291122614465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59372007791629771974554293 5566125730465291122614465)
                  ·
                    refine ⟨4174594297848968341960849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5566125730465291122614465 4174594297848968341960849)
                    ·
                      refine ⟨3130945723386726256470637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4174594297848968341960849 3130945723386726256470637)
                      ·
                        rfl

theorem cell23_6097495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 2, 2].length) (baseStart_6097495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097495 prefixEnd_6097495 := by exact prefixLift 6097495
  have htrace : WordTrace (prefixWord ++ tailWord_6097495) baseStart_6097495 baseEnd_6097495 := by
    simpa [prefixWord, tailWord_6097495, baseEnd_6097495] using wordTrace_append hprefix tailTrace_6097495
  have hstable : (prefixWord ++ tailWord_6097495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097495).length < 2 ^ (prefixWord ++ tailWord_6097495).sum := by decide
  have hdescent : baseEnd_6097495 < baseStart_6097495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097505 : List Nat := [1, 2, 3, 1, 1, 4, 3, 2, 2, 4]
def baseStart_6097505 : Nat := 118140960795 + 6097505 * 2 ^ 59
def prefixEnd_6097505 : Nat := 4983230072969 + 3 ^ 40 * 6097505 * 2
def baseEnd_6097505 : Nat := 1043650286064423739115197

theorem tailTrace_6097505 : CollatzResearch.WordTrace tailWord_6097505 prefixEnd_6097505 1043650286064423739115197 := by
  unfold tailWord_6097505
  simp only [CollatzResearch.WordTrace]
  refine ⟨222394277774788230791333969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148262851849858820527555979 222394277774788230791333969)
  ·
    refine ⟨166795708331091173093500477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222394277774788230791333969 166795708331091173093500477)
    ·
      refine ⟨62548390624159189910062679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166795708331091173093500477 62548390624159189910062679)
      ·
        refine ⟨93822585936238784865094019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62548390624159189910062679 93822585936238784865094019)
        ·
          refine ⟨140733878904358177297641029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93822585936238784865094019 140733878904358177297641029)
          ·
            refine ⟨26387602294567158243307693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140733878904358177297641029 26387602294567158243307693)
            ·
              refine ⟨9895350860462684341240385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26387602294567158243307693 9895350860462684341240385)
              ·
                refine ⟨7421513145347013255930289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9895350860462684341240385 7421513145347013255930289)
                ·
                  refine ⟨5566134859010259941947717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7421513145347013255930289 5566134859010259941947717)
                  ·
                    refine ⟨1043650286064423739115197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5566134859010259941947717 1043650286064423739115197)
                    ·
                      rfl

theorem cell23_6097505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_6097505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097505 prefixEnd_6097505 := by exact prefixLift 6097505
  have htrace : WordTrace (prefixWord ++ tailWord_6097505) baseStart_6097505 baseEnd_6097505 := by
    simpa [prefixWord, tailWord_6097505, baseEnd_6097505] using wordTrace_append hprefix tailTrace_6097505
  have hstable : (prefixWord ++ tailWord_6097505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097505).length < 2 ^ (prefixWord ++ tailWord_6097505).sum := by decide
  have hdescent : baseEnd_6097505 < baseStart_6097505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097511 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_6097511 : Nat := 118140960795 + 6097511 * 2 ^ 59
def prefixEnd_6097511 : Nat := 4983230072969 + 3 ^ 40 * 6097511 * 2
def baseEnd_6097511 : Nat := 3130953939077198193870563

theorem tailTrace_6097511 : CollatzResearch.WordTrace tailWord_6097511 prefixEnd_6097511 3130953939077198193870563 := by
  unfold tailWord_6097511
  simp only [CollatzResearch.WordTrace]
  refine ⟨222394496612766493816052387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148262997741844329210701591 222394496612766493816052387)
  ·
    refine ⟨333591744919149740724078581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222394496612766493816052387 333591744919149740724078581)
    ·
      refine ⟨31274226086170288192882367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 333591744919149740724078581 31274226086170288192882367)
      ·
        refine ⟨46911339129255432289323551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31274226086170288192882367 46911339129255432289323551)
        ·
          refine ⟨70367008693883148433985327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46911339129255432289323551 70367008693883148433985327)
          ·
            refine ⟨105550513040824722650977991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70367008693883148433985327 105550513040824722650977991)
            ·
              refine ⟨158325769561237083976466987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105550513040824722650977991 158325769561237083976466987)
              ·
                refine ⟨237488654341855625964700481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158325769561237083976466987 237488654341855625964700481)
                ·
                  refine ⟨178116490756391719473525361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237488654341855625964700481 178116490756391719473525361)
                  ·
                    refine ⟨133587368067293789605144021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 178116490756391719473525361 133587368067293789605144021)
                    ·
                      refine ⟨3130953939077198193870563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 133587368067293789605144021 3130953939077198193870563)
                      ·
                        rfl

theorem cell23_6097511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_6097511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097511 prefixEnd_6097511 := by exact prefixLift 6097511
  have htrace : WordTrace (prefixWord ++ tailWord_6097511) baseStart_6097511 baseEnd_6097511 := by
    simpa [prefixWord, tailWord_6097511, baseEnd_6097511] using wordTrace_append hprefix tailTrace_6097511
  have hstable : (prefixWord ++ tailWord_6097511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097511).length < 2 ^ (prefixWord ++ tailWord_6097511).sum := by decide
  have hdescent : baseEnd_6097511 < baseStart_6097511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097522 : List Nat := [3, 2, 1, 2, 5, 1, 1, 1, 1, 6]
def baseStart_6097522 : Nat := 118140960795 + 6097522 * 2 ^ 59
def prefixEnd_6097522 : Nat := 4983230072969 + 3 ^ 40 * 6097522 * 2
def baseEnd_6097522 : Nat := 1043653195788132550277671

theorem tailTrace_6097522 : CollatzResearch.WordTrace tailWord_6097522 prefixEnd_6097522 1043653195788132550277671 := by
  unfold tailWord_6097522
  simp only [CollatzResearch.WordTrace]
  refine ⟨55598724453931660673675705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148263265210484428463135213 55598724453931660673675705)
  ·
    refine ⟨41699043340448745505256779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55598724453931660673675705 41699043340448745505256779)
    ·
      refine ⟨62548565010673118257885169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41699043340448745505256779 62548565010673118257885169)
      ·
        refine ⟨46911423758004838693413877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62548565010673118257885169 46911423758004838693413877)
        ·
          refine ⟨4397945977312953627507551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46911423758004838693413877 4397945977312953627507551)
          ·
            refine ⟨6596918965969430441261327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4397945977312953627507551 6596918965969430441261327)
            ·
              refine ⟨9895378448954145661891991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6596918965969430441261327 9895378448954145661891991)
              ·
                refine ⟨14843067673431218492837987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9895378448954145661891991 14843067673431218492837987)
                ·
                  refine ⟨22264601510146827739256981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14843067673431218492837987 22264601510146827739256981)
                  ·
                    refine ⟨1043653195788132550277671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22264601510146827739256981 1043653195788132550277671)
                    ·
                      rfl

theorem cell23_6097522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_6097522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097522 prefixEnd_6097522 := by exact prefixLift 6097522
  have htrace : WordTrace (prefixWord ++ tailWord_6097522) baseStart_6097522 baseEnd_6097522 := by
    simpa [prefixWord, tailWord_6097522, baseEnd_6097522] using wordTrace_append hprefix tailTrace_6097522
  have hstable : (prefixWord ++ tailWord_6097522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097522).length < 2 ^ (prefixWord ++ tailWord_6097522).sum := by decide
  have hdescent : baseEnd_6097522 < baseStart_6097522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097525 : List Nat := [1, 3, 4, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_6097525 : Nat := 118140960795 + 6097525 * 2 ^ 59
def prefixEnd_6097525 : Nat := 4983230072969 + 3 ^ 40 * 6097525 * 2
def baseEnd_6097525 : Nat := 3130961127806361139095499

theorem tailTrace_6097525 : CollatzResearch.WordTrace tailWord_6097525 prefixEnd_6097525 3130961127806361139095499 := by
  unfold tailWord_6097525
  simp only [CollatzResearch.WordTrace]
  refine ⟨222395007234715774207062029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148263338156477182804708019 222395007234715774207062029)
  ·
    refine ⟨83398127713018415327648261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222395007234715774207062029 83398127713018415327648261)
    ·
      refine ⟨15637148946190952873934049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83398127713018415327648261 15637148946190952873934049)
      ·
        refine ⟨11727861709643214655450537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15637148946190952873934049 11727861709643214655450537)
        ·
          refine ⟨8795896282232410991587903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11727861709643214655450537 8795896282232410991587903)
          ·
            refine ⟨13193844423348616487381855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8795896282232410991587903 13193844423348616487381855)
            ·
              refine ⟨19790766635022924731072783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13193844423348616487381855 19790766635022924731072783)
              ·
                refine ⟨29686149952534387096609175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19790766635022924731072783 29686149952534387096609175)
                ·
                  refine ⟨44529224928801580644913763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29686149952534387096609175 44529224928801580644913763)
                  ·
                    refine ⟨66793837393202370967370645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44529224928801580644913763 66793837393202370967370645)
                    ·
                      refine ⟨3130961127806361139095499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66793837393202370967370645 3130961127806361139095499)
                      ·
                        rfl

theorem cell23_6097525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_6097525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097525 prefixEnd_6097525 := by exact prefixLift 6097525
  have htrace : WordTrace (prefixWord ++ tailWord_6097525) baseStart_6097525 baseEnd_6097525 := by
    simpa [prefixWord, tailWord_6097525, baseEnd_6097525] using wordTrace_append hprefix tailTrace_6097525
  have hstable : (prefixWord ++ tailWord_6097525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097525).length < 2 ^ (prefixWord ++ tailWord_6097525).sum := by decide
  have hdescent : baseEnd_6097525 < baseStart_6097525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097589 : List Nat := [1, 3, 3, 3, 1, 1, 3, 2, 1, 3, 2]
def baseStart_6097589 : Nat := 118140960795 + 6097589 * 2 ^ 59
def prefixEnd_6097589 : Nat := 4983230072969 + 3 ^ 40 * 6097589 * 2
def baseEnd_6097589 : Nat := 3130993990568248888695205

theorem tailTrace_6097589 : CollatzResearch.WordTrace tailWord_6097589 prefixEnd_6097589 3130993990568248888695205 := by
  unfold tailWord_6097589
  simp only [CollatzResearch.WordTrace]
  refine ⟨222397341506483913137391821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148264894337655942091594547 222397341506483913137391821)
  ·
    refine ⟨83399003064931467426521933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222397341506483913137391821 83399003064931467426521933)
    ·
      refine ⟨31274626149349300284945725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83399003064931467426521933 31274626149349300284945725)
      ·
        refine ⟨11727984806005987606854647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31274626149349300284945725 11727984806005987606854647)
        ·
          refine ⟨17591977209008981410281971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11727984806005987606854647 17591977209008981410281971)
          ·
            refine ⟨26387965813513472115422957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17591977209008981410281971 26387965813513472115422957)
            ·
              refine ⟨9895487180067552043283609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26387965813513472115422957 9895487180067552043283609)
              ·
                refine ⟨7421615385050664032462707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9895487180067552043283609 7421615385050664032462707)
                ·
                  refine ⟨11132423077575996048694061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7421615385050664032462707 11132423077575996048694061)
                  ·
                    refine ⟨4174658654090998518260273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11132423077575996048694061 4174658654090998518260273)
                    ·
                      refine ⟨3130993990568248888695205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4174658654090998518260273 3130993990568248888695205)
                      ·
                        rfl

theorem cell23_6097589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_6097589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097589 prefixEnd_6097589 := by exact prefixLift 6097589
  have htrace : WordTrace (prefixWord ++ tailWord_6097589) baseStart_6097589 baseEnd_6097589 := by
    simpa [prefixWord, tailWord_6097589, baseEnd_6097589] using wordTrace_append hprefix tailTrace_6097589
  have hstable : (prefixWord ++ tailWord_6097589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097589).length < 2 ^ (prefixWord ++ tailWord_6097589).sum := by decide
  have hdescent : baseEnd_6097589 < baseStart_6097589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097625 : List Nat := [1, 2, 1, 2, 3, 2, 3, 4, 5]
def baseStart_6097625 : Nat := 118140960795 + 6097625 * 2 ^ 59
def prefixEnd_6097625 : Nat := 4983230072969 + 3 ^ 40 * 6097625 * 2
def baseEnd_6097625 : Nat := 347890275096867860871671

theorem tailTrace_6097625 : CollatzResearch.WordTrace tailWord_6097625 prefixEnd_6097625 347890275096867860871671 := by
  unfold tailWord_6097625
  simp only [CollatzResearch.WordTrace]
  refine ⟨222398654534353491285702329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148265769689568994190468219 222398654534353491285702329)
  ·
    refine ⟨166798990900765118464276747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222398654534353491285702329 166798990900765118464276747)
    ·
      refine ⟨250198486351147677696415121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166798990900765118464276747 250198486351147677696415121)
      ·
        refine ⟨187648864763360758272311341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250198486351147677696415121 187648864763360758272311341)
        ·
          refine ⟨70368324286260284352116753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187648864763360758272311341 70368324286260284352116753)
          ·
            refine ⟨52776243214695213264087565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70368324286260284352116753 52776243214695213264087565)
            ·
              refine ⟨19791091205510704974032837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52776243214695213264087565 19791091205510704974032837)
              ·
                refine ⟨3710829601033257182631157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19791091205510704974032837 3710829601033257182631157)
                ·
                  refine ⟨347890275096867860871671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3710829601033257182631157 347890275096867860871671)
                  ·
                    rfl

theorem cell23_6097625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 5].length) (baseStart_6097625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097625 prefixEnd_6097625 := by exact prefixLift 6097625
  have htrace : WordTrace (prefixWord ++ tailWord_6097625) baseStart_6097625 baseEnd_6097625 := by
    simpa [prefixWord, tailWord_6097625, baseEnd_6097625] using wordTrace_append hprefix tailTrace_6097625
  have hstable : (prefixWord ++ tailWord_6097625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097625).length < 2 ^ (prefixWord ++ tailWord_6097625).sum := by decide
  have hdescent : baseEnd_6097625 < baseStart_6097625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097635 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 3]
def baseStart_6097635 : Nat := 118140960795 + 6097635 * 2 ^ 59
def prefixEnd_6097635 : Nat := 4983230072969 + 3 ^ 40 * 6097635 * 2
def baseEnd_6097635 : Nat := 3131017610678355708719993

theorem tailTrace_6097635 : CollatzResearch.WordTrace tailWord_6097635 prefixEnd_6097635 3131017610678355708719993 := by
  unfold tailWord_6097635
  simp only [CollatzResearch.WordTrace]
  refine ⟨222399019264317262993566359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148266012842878175329044239 222399019264317262993566359)
  ·
    refine ⟨333598528896475894490349539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222399019264317262993566359 333598528896475894490349539)
    ·
      refine ⟨500397793344713841735524309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333598528896475894490349539 500397793344713841735524309)
      ·
        refine ⟨11728073281516730665676351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 500397793344713841735524309 11728073281516730665676351)
        ·
          refine ⟨17592109922275095998514527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11728073281516730665676351 17592109922275095998514527)
          ·
            refine ⟨26388164883412643997771791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17592109922275095998514527 26388164883412643997771791)
            ·
              refine ⟨39582247325118965996657687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26388164883412643997771791 39582247325118965996657687)
              ·
                refine ⟨59373370987678448994986531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39582247325118965996657687 59373370987678448994986531)
                ·
                  refine ⟨89060056481517673492479797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59373370987678448994986531 89060056481517673492479797)
                  ·
                    refine ⟨8349380295142281889919981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89060056481517673492479797 8349380295142281889919981)
                    ·
                      refine ⟨3131017610678355708719993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8349380295142281889919981 3131017610678355708719993)
                      ·
                        rfl

theorem cell23_6097635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_6097635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097635 prefixEnd_6097635 := by exact prefixLift 6097635
  have htrace : WordTrace (prefixWord ++ tailWord_6097635) baseStart_6097635 baseEnd_6097635 := by
    simpa [prefixWord, tailWord_6097635, baseEnd_6097635] using wordTrace_append hprefix tailTrace_6097635
  have hstable : (prefixWord ++ tailWord_6097635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097635).length < 2 ^ (prefixWord ++ tailWord_6097635).sum := by decide
  have hdescent : baseEnd_6097635 < baseStart_6097635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097688 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 4, 1, 6]
def baseStart_6097688 : Nat := 118140960795 + 6097688 * 2 ^ 59
def prefixEnd_6097688 : Nat := 4983230072969 + 3 ^ 40 * 6097688 * 2
def baseEnd_6097688 : Nat := 3131044825153044001357249

theorem tailTrace_6097688 : CollatzResearch.WordTrace tailWord_6097688 prefixEnd_6097688 3131044825153044001357249 := by
  unfold tailWord_6097688
  simp only [CollatzResearch.WordTrace]
  refine ⟨111200476166562626522622859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148267301555416835363497145 111200476166562626522622859)
  ·
    refine ⟨166800714249843939783934289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111200476166562626522622859 166800714249843939783934289)
    ·
      refine ⟨125100535687382954837950717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166800714249843939783934289 125100535687382954837950717)
      ·
        refine ⟨46912700882768608064231519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125100535687382954837950717 46912700882768608064231519)
        ·
          refine ⟨70369051324152912096347279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46912700882768608064231519 70369051324152912096347279)
          ·
            refine ⟨105553576986229368144520919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70369051324152912096347279 105553576986229368144520919)
            ·
              refine ⟨158330365479344052216781379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105553576986229368144520919 158330365479344052216781379)
              ·
                refine ⟨237495548219016078325172069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158330365479344052216781379 237495548219016078325172069)
                ·
                  refine ⟨44530415291065514685969763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 237495548219016078325172069 44530415291065514685969763)
                  ·
                    refine ⟨66795622936598272028954645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44530415291065514685969763 66795622936598272028954645)
                    ·
                      refine ⟨3131044825153044001357249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66795622936598272028954645 3131044825153044001357249)
                      ·
                        rfl

theorem cell23_6097688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_6097688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097688 prefixEnd_6097688 := by exact prefixLift 6097688
  have htrace : WordTrace (prefixWord ++ tailWord_6097688) baseStart_6097688 baseEnd_6097688 := by
    simpa [prefixWord, tailWord_6097688, baseEnd_6097688] using wordTrace_append hprefix tailTrace_6097688
  have hstable : (prefixWord ++ tailWord_6097688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097688).length < 2 ^ (prefixWord ++ tailWord_6097688).sum := by decide
  have hdescent : baseEnd_6097688 < baseStart_6097688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097692 : List Nat := [2, 2, 3, 1, 1, 3, 2, 1, 2, 4, 2]
def baseStart_6097692 : Nat := 118140960795 + 6097692 * 2 ^ 59
def prefixEnd_6097692 : Nat := 4983230072969 + 3 ^ 40 * 6097692 * 2
def baseEnd_6097692 : Nat := 3131046879075661985707231

theorem tailTrace_6097692 : CollatzResearch.WordTrace tailWord_6097692 prefixEnd_6097692 3131046879075661985707231 := by
  unfold tailWord_6097692
  simp only [CollatzResearch.WordTrace]
  refine ⟨111200549112555380864195665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148267398816740507818927553 111200549112555380864195665)
  ·
    refine ⟨83400411834416535648146749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111200549112555380864195665 83400411834416535648146749)
    ·
      refine ⟨31275154437906200868055031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83400411834416535648146749 31275154437906200868055031)
      ·
        refine ⟨46912731656859301302082547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31275154437906200868055031 46912731656859301302082547)
        ·
          refine ⟨70369097485288951953123821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46912731656859301302082547 70369097485288951953123821)
          ·
            refine ⟨26388411556983356982421433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70369097485288951953123821 26388411556983356982421433)
            ·
              refine ⟨19791308667737517736816075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26388411556983356982421433 19791308667737517736816075)
              ·
                refine ⟨29686963001606276605224113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19791308667737517736816075 29686963001606276605224113)
                ·
                  refine ⟨22265222251204707453918085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29686963001606276605224113 22265222251204707453918085)
                  ·
                    refine ⟨4174729172100882647609641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22265222251204707453918085 4174729172100882647609641)
                    ·
                      refine ⟨3131046879075661985707231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4174729172100882647609641 3131046879075661985707231)
                      ·
                        rfl

theorem cell23_6097692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_6097692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097692 prefixEnd_6097692 := by exact prefixLift 6097692
  have htrace : WordTrace (prefixWord ++ tailWord_6097692) baseStart_6097692 baseEnd_6097692 := by
    simpa [prefixWord, tailWord_6097692, baseEnd_6097692] using wordTrace_append hprefix tailTrace_6097692
  have hstable : (prefixWord ++ tailWord_6097692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097692).length < 2 ^ (prefixWord ++ tailWord_6097692).sum := by decide
  have hdescent : baseEnd_6097692 < baseStart_6097692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097695 : List Nat := [1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 3]
def baseStart_6097695 : Nat := 118140960795 + 6097695 * 2 ^ 59
def prefixEnd_6097695 : Nat := 4983230072969 + 3 ^ 40 * 6097695 * 2
def baseEnd_6097695 : Nat := 3131048419517625473969717

theorem tailTrace_6097695 : CollatzResearch.WordTrace tailWord_6097695 prefixEnd_6097695 3131048419517625473969717 := by
  unfold tailWord_6097695
  simp only [CollatzResearch.WordTrace]
  refine ⟨222401207644099893240750539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148267471762733262160500359 222401207644099893240750539)
  ·
    refine ⟨333601811466149839861125809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222401207644099893240750539 333601811466149839861125809)
    ·
      refine ⟨250201358599612379895844357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333601811466149839861125809 250201358599612379895844357)
      ·
        refine ⟨46912754737427321230470817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 250201358599612379895844357 46912754737427321230470817)
        ·
          refine ⟨35184566053070490922853113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46912754737427321230470817 35184566053070490922853113)
          ·
            refine ⟨26388424539802868192139835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35184566053070490922853113 26388424539802868192139835)
            ·
              refine ⟨39582636809704302288209753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26388424539802868192139835 39582636809704302288209753)
              ·
                refine ⟨29686977607278226716157315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39582636809704302288209753 29686977607278226716157315)
                ·
                  refine ⟨44530466410917340074235973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29686977607278226716157315 44530466410917340074235973)
                  ·
                    refine ⟨8349462452047001263919245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44530466410917340074235973 8349462452047001263919245)
                    ·
                      refine ⟨3131048419517625473969717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8349462452047001263919245 3131048419517625473969717)
                      ·
                        rfl

theorem cell23_6097695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_6097695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097695 prefixEnd_6097695 := by exact prefixLift 6097695
  have htrace : WordTrace (prefixWord ++ tailWord_6097695) baseStart_6097695 baseEnd_6097695 := by
    simpa [prefixWord, tailWord_6097695, baseEnd_6097695] using wordTrace_append hprefix tailTrace_6097695
  have hstable : (prefixWord ++ tailWord_6097695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097695).length < 2 ^ (prefixWord ++ tailWord_6097695).sum := by decide
  have hdescent : baseEnd_6097695 < baseStart_6097695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097775 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 6, 4]
def baseStart_6097775 : Nat := 118140960795 + 6097775 * 2 ^ 59
def prefixEnd_6097775 : Nat := 4983230072969 + 3 ^ 40 * 6097775 * 2
def baseEnd_6097775 : Nat := 1043696499323328386989783

theorem tailTrace_6097775 : CollatzResearch.WordTrace tailWord_6097775 prefixEnd_6097775 1043696499323328386989783 := by
  unfold tailWord_6097775
  simp only [CollatzResearch.WordTrace]
  refine ⟨222404125483810066903662779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148269416989206711269108519 222404125483810066903662779)
  ·
    refine ⟨333606188225715100355494169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222404125483810066903662779 333606188225715100355494169)
    ·
      refine ⟨250204641169286325266620627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333606188225715100355494169 250204641169286325266620627)
      ·
        refine ⟨375306961753929487899930941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250204641169286325266620627 375306961753929487899930941)
        ·
          refine ⟨140740110657723557962474103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 375306961753929487899930941 140740110657723557962474103)
          ·
            refine ⟨211110165986585336943711155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140740110657723557962474103 211110165986585336943711155)
            ·
              refine ⟨316665248979878005415566733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211110165986585336943711155 316665248979878005415566733)
              ·
                refine ⟨118749468367454252030837525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 316665248979878005415566733 118749468367454252030837525)
                ·
                  refine ⟨5566381329724418063945509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118749468367454252030837525 5566381329724418063945509)
                  ·
                    refine ⟨1043696499323328386989783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5566381329724418063945509 1043696499323328386989783)
                    ·
                      rfl

theorem cell23_6097775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 4].length) (baseStart_6097775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097775 prefixEnd_6097775 := by exact prefixLift 6097775
  have htrace : WordTrace (prefixWord ++ tailWord_6097775) baseStart_6097775 baseEnd_6097775 := by
    simpa [prefixWord, tailWord_6097775, baseEnd_6097775] using wordTrace_append hprefix tailTrace_6097775
  have hstable : (prefixWord ++ tailWord_6097775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097775).length < 2 ^ (prefixWord ++ tailWord_6097775).sum := by decide
  have hdescent : baseEnd_6097775 < baseStart_6097775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097795 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 4]
def baseStart_6097795 : Nat := 118140960795 + 6097795 * 2 ^ 59
def prefixEnd_6097795 : Nat := 4983230072969 + 3 ^ 40 * 6097795 * 2
def baseEnd_6097795 : Nat := 3131099767583075082719257

theorem tailTrace_6097795 : CollatzResearch.WordTrace tailWord_6097795 prefixEnd_6097795 3131099767583075082719257 := by
  unfold tailWord_6097795
  simp only [CollatzResearch.WordTrace]
  refine ⟨222404854943737610319390839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148269903295825073546260559 222404854943737610319390839)
  ·
    refine ⟨333607282415606415479086259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222404854943737610319390839 333607282415606415479086259)
    ·
      refine ⟨500410923623409623218629389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333607282415606415479086259 500410923623409623218629389)
      ·
        refine ⟨187654096358778608706986021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 500410923623409623218629389 187654096358778608706986021)
        ·
          refine ⟨35185143067270989132559879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187654096358778608706986021 35185143067270989132559879)
          ·
            refine ⟨52777714600906483698839819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35185143067270989132559879 52777714600906483698839819)
            ·
              refine ⟨79166571901359725548259729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52777714600906483698839819 79166571901359725548259729)
              ·
                refine ⟨59374928926019794161194797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79166571901359725548259729 59374928926019794161194797)
                ·
                  refine ⟨22265598347257422810448049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59374928926019794161194797 22265598347257422810448049)
                  ·
                    refine ⟨16699198760443067107836037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22265598347257422810448049 16699198760443067107836037)
                    ·
                      refine ⟨3131099767583075082719257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16699198760443067107836037 3131099767583075082719257)
                      ·
                        rfl

theorem cell23_6097795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_6097795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097795 prefixEnd_6097795 := by exact prefixLift 6097795
  have htrace : WordTrace (prefixWord ++ tailWord_6097795) baseStart_6097795 baseEnd_6097795 := by
    simpa [prefixWord, tailWord_6097795, baseEnd_6097795] using wordTrace_append hprefix tailTrace_6097795
  have hstable : (prefixWord ++ tailWord_6097795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097795).length < 2 ^ (prefixWord ++ tailWord_6097795).sum := by decide
  have hdescent : baseEnd_6097795 < baseStart_6097795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097849 : List Nat := [1, 2, 1, 4, 2, 3, 1, 1, 4, 1, 3]
def baseStart_6097849 : Nat := 118140960795 + 6097849 * 2 ^ 59
def prefixEnd_6097849 : Nat := 4983230072969 + 3 ^ 40 * 6097849 * 2
def baseEnd_6097849 : Nat := 3131127495538417871444009

theorem tailTrace_6097849 : CollatzResearch.WordTrace tailWord_6097849 prefixEnd_6097849 3131127495538417871444009 := by
  unfold tailWord_6097849
  simp only [CollatzResearch.WordTrace]
  refine ⟨222406824485541977541856601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148271216323694651694571067 222406824485541977541856601)
  ·
    refine ⟨166805118364156483156392451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222406824485541977541856601 166805118364156483156392451)
    ·
      refine ⟨250207677546234724734588677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166805118364156483156392451 250207677546234724734588677)
      ·
        refine ⟨46913939539919010887735377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 250207677546234724734588677 46913939539919010887735377)
        ·
          refine ⟨35185454654939258165801533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46913939539919010887735377 35185454654939258165801533)
          ·
            refine ⟨13194545495602221812175575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35185454654939258165801533 13194545495602221812175575)
            ·
              refine ⟨19791818243403332718263363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13194545495602221812175575 19791818243403332718263363)
              ·
                refine ⟨29687727365104999077395045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19791818243403332718263363 29687727365104999077395045)
                ·
                  refine ⟨5566448880957187327011571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29687727365104999077395045 5566448880957187327011571)
                  ·
                    refine ⟨8349673321435780990517357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5566448880957187327011571 8349673321435780990517357)
                    ·
                      refine ⟨3131127495538417871444009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8349673321435780990517357 3131127495538417871444009)
                      ·
                        rfl

theorem cell23_6097849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_6097849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097849 prefixEnd_6097849 := by exact prefixLift 6097849
  have htrace : WordTrace (prefixWord ++ tailWord_6097849) baseStart_6097849 baseEnd_6097849 := by
    simpa [prefixWord, tailWord_6097849, baseEnd_6097849] using wordTrace_append hprefix tailTrace_6097849
  have hstable : (prefixWord ++ tailWord_6097849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097849).length < 2 ^ (prefixWord ++ tailWord_6097849).sum := by decide
  have hdescent : baseEnd_6097849 < baseStart_6097849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097855 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 4]
def baseStart_6097855 : Nat := 118140960795 + 6097855 * 2 ^ 59
def prefixEnd_6097855 : Nat := 4983230072969 + 3 ^ 40 * 6097855 * 2
def baseEnd_6097855 : Nat := 3131130576422344847968981

theorem tailTrace_6097855 : CollatzResearch.WordTrace tailWord_6097855 prefixEnd_6097855 3131130576422344847968981 := by
  unfold tailWord_6097855
  simp only [CollatzResearch.WordTrace]
  refine ⟨222407043323520240566575019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148271362215680160377716679 222407043323520240566575019)
  ·
    refine ⟨333610564985280360849862529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222407043323520240566575019 333610564985280360849862529)
    ·
      refine ⟨250207923738960270637396897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333610564985280360849862529 250207923738960270637396897)
      ·
        refine ⟨187655942804220202978047673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250207923738960270637396897 187655942804220202978047673)
        ·
          refine ⟨140741957103165152233535755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187655942804220202978047673 140741957103165152233535755)
          ·
            refine ⟨211112935654747728350303633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140741957103165152233535755 211112935654747728350303633)
            ·
              refine ⟨158334701741060796262727725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211112935654747728350303633 158334701741060796262727725)
              ·
                refine ⟨59375513152897798598522897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158334701741060796262727725 59375513152897798598522897)
                ·
                  refine ⟨44531634864673348948892173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59375513152897798598522897 44531634864673348948892173)
                  ·
                    refine ⟨16699363074252505855834565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44531634864673348948892173 16699363074252505855834565)
                    ·
                      refine ⟨3131130576422344847968981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16699363074252505855834565 3131130576422344847968981)
                      ·
                        rfl

theorem cell23_6097855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_6097855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097855 prefixEnd_6097855 := by exact prefixLift 6097855
  have htrace : WordTrace (prefixWord ++ tailWord_6097855) baseStart_6097855 baseEnd_6097855 := by
    simpa [prefixWord, tailWord_6097855, baseEnd_6097855] using wordTrace_append hprefix tailTrace_6097855
  have hstable : (prefixWord ++ tailWord_6097855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097855).length < 2 ^ (prefixWord ++ tailWord_6097855).sum := by decide
  have hdescent : baseEnd_6097855 < baseStart_6097855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097876 : List Nat := [2, 4, 1, 2, 1, 2, 1, 4, 1, 3, 2]
def baseStart_6097876 : Nat := 118140960795 + 6097876 * 2 ^ 59
def prefixEnd_6097876 : Nat := 4983230072969 + 3 ^ 40 * 6097876 * 2
def baseEnd_6097876 : Nat := 3131141359516089265806385

theorem tailTrace_6097876 : CollatzResearch.WordTrace tailWord_6097876 prefixEnd_6097876 3131141359516089265806385 := by
  unfold tailWord_6097876
  simp only [CollatzResearch.WordTrace]
  refine ⟨111203904628222080576544741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148271872837629440768726321 111203904628222080576544741)
  ·
    refine ⟨20850732117791640108102139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111203904628222080576544741 20850732117791640108102139)
    ·
      refine ⟨31276098176687460162153209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20850732117791640108102139 31276098176687460162153209)
      ·
        refine ⟨23457073632515595121614907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31276098176687460162153209 23457073632515595121614907)
        ·
          refine ⟨35185610448773392682422361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23457073632515595121614907 35185610448773392682422361)
          ·
            refine ⟨26389207836580044511816771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35185610448773392682422361 26389207836580044511816771)
            ·
              refine ⟨39583811754870066767725157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26389207836580044511816771 39583811754870066767725157)
              ·
                refine ⟨7421964704038137518948467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39583811754870066767725157 7421964704038137518948467)
                ·
                  refine ⟨11132947056057206278422701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7421964704038137518948467 11132947056057206278422701)
                  ·
                    refine ⟨4174855146021452354408513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11132947056057206278422701 4174855146021452354408513)
                    ·
                      refine ⟨3131141359516089265806385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4174855146021452354408513 3131141359516089265806385)
                      ·
                        rfl

theorem cell23_6097876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_6097876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097876 prefixEnd_6097876 := by exact prefixLift 6097876
  have htrace : WordTrace (prefixWord ++ tailWord_6097876) baseStart_6097876 baseEnd_6097876 := by
    simpa [prefixWord, tailWord_6097876, baseEnd_6097876] using wordTrace_append hprefix tailTrace_6097876
  have hstable : (prefixWord ++ tailWord_6097876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097876).length < 2 ^ (prefixWord ++ tailWord_6097876).sum := by decide
  have hdescent : baseEnd_6097876 < baseStart_6097876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6097935 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 5]
def baseStart_6097935 : Nat := 118140960795 + 6097935 * 2 ^ 59
def prefixEnd_6097935 : Nat := 4983230072969 + 3 ^ 40 * 6097935 * 2
def baseEnd_6097935 : Nat := 3131171654874704534968613

theorem tailTrace_6097935 : CollatzResearch.WordTrace tailWord_6097935 prefixEnd_6097935 3131171654874704534968613 := by
  unfold tailWord_6097935
  simp only [CollatzResearch.WordTrace]
  refine ⟨222409961163230414229487259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148273307442153609486324839 222409961163230414229487259)
  ·
    refine ⟨333614941744845621344230889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222409961163230414229487259 333614941744845621344230889)
    ·
      refine ⟨250211206308634216008173167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333614941744845621344230889 250211206308634216008173167)
      ·
        refine ⟨375316809462951324012259751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250211206308634216008173167 375316809462951324012259751)
        ·
          refine ⟨562975214194426986018389627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375316809462951324012259751 562975214194426986018389627)
          ·
            refine ⟨844462821291640479027584441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562975214194426986018389627 844462821291640479027584441)
            ·
              refine ⟨633347115968730359270688331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 844462821291640479027584441 633347115968730359270688331)
              ·
                refine ⟨950020673953095538906032497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 633347115968730359270688331 950020673953095538906032497)
                ·
                  refine ⟨712515505464821654179524373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 950020673953095538906032497 712515505464821654179524373)
                  ·
                    refine ⟨33399164318663515039665205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 712515505464821654179524373 33399164318663515039665205)
                    ·
                      refine ⟨3131171654874704534968613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33399164318663515039665205 3131171654874704534968613)
                      ·
                        rfl

theorem cell23_6097935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 5].length) (baseStart_6097935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6097935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6097935 prefixEnd_6097935 := by exact prefixLift 6097935
  have htrace : WordTrace (prefixWord ++ tailWord_6097935) baseStart_6097935 baseEnd_6097935 := by
    simpa [prefixWord, tailWord_6097935, baseEnd_6097935] using wordTrace_append hprefix tailTrace_6097935
  have hstable : (prefixWord ++ tailWord_6097935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6097935).length < 2 ^ (prefixWord ++ tailWord_6097935).sum := by decide
  have hdescent : baseEnd_6097935 < baseStart_6097935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6097935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098039 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 3, 5, 2]
def baseStart_6098039 : Nat := 118140960795 + 6098039 * 2 ^ 59
def prefixEnd_6098039 : Nat := 4983230072969 + 3 ^ 40 * 6098039 * 2
def baseEnd_6098039 : Nat := 3131225056862772128068135

theorem tailTrace_6098039 : CollatzResearch.WordTrace tailWord_6098039 prefixEnd_6098039 3131225056862772128068135 := by
  unfold tailWord_6098039
  simp only [CollatzResearch.WordTrace]
  refine ⟨222413754354853639991273171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148275836236569093327515447 222413754354853639991273171)
  ·
    refine ⟨333620631532280459986909757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222413754354853639991273171 333620631532280459986909757)
    ·
      refine ⟨125107736824605172495091159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333620631532280459986909757 125107736824605172495091159)
      ·
        refine ⟨187661605236907758742636739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125107736824605172495091159 187661605236907758742636739)
        ·
          refine ⟨281492407855361638113955109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187661605236907758742636739 281492407855361638113955109)
          ·
            refine ⟨52779826472880307146366583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 281492407855361638113955109 52779826472880307146366583)
            ·
              refine ⟨79169739709320460719549875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52779826472880307146366583 79169739709320460719549875)
              ·
                refine ⟨118754609563980691079324813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79169739709320460719549875 118754609563980691079324813)
                ·
                  refine ⟨44532978586492759154746805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118754609563980691079324813 44532978586492759154746805)
                  ·
                    refine ⟨4174966742483696170757513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44532978586492759154746805 4174966742483696170757513)
                    ·
                      refine ⟨3131225056862772128068135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4174966742483696170757513 3131225056862772128068135)
                      ·
                        rfl

theorem cell23_6098039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 5, 2].length) (baseStart_6098039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098039 prefixEnd_6098039 := by exact prefixLift 6098039
  have htrace : WordTrace (prefixWord ++ tailWord_6098039) baseStart_6098039 baseEnd_6098039 := by
    simpa [prefixWord, tailWord_6098039, baseEnd_6098039] using wordTrace_append hprefix tailTrace_6098039
  have hstable : (prefixWord ++ tailWord_6098039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098039).length < 2 ^ (prefixWord ++ tailWord_6098039).sum := by decide
  have hdescent : baseEnd_6098039 < baseStart_6098039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098066 : List Nat := [3, 2, 3, 1, 1, 2, 2, 3, 1, 5]
def baseStart_6098066 : Nat := 118140960795 + 6098066 * 2 ^ 59
def prefixEnd_6098066 : Nat := 4983230072969 + 3 ^ 40 * 6098066 * 2
def baseEnd_6098066 : Nat := 1043746306946814507476837

theorem tailTrace_6098066 : CollatzResearch.WordTrace tailWord_6098066 prefixEnd_6098066 1043746306946814507476837 := by
  unfold tailWord_6098066
  simp only [CollatzResearch.WordTrace]
  refine ⟨55603684781438955900626513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148276492750503882401670701 55603684781438955900626513)
  ·
    refine ⟨41702763586079216925469885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55603684781438955900626513 41702763586079216925469885)
    ·
      refine ⟨15638536344779706347051207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41702763586079216925469885 15638536344779706347051207)
      ·
        refine ⟨23457804517169559520576811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15638536344779706347051207 23457804517169559520576811)
        ·
          refine ⟨35186706775754339280865217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23457804517169559520576811 35186706775754339280865217)
          ·
            refine ⟨26390030081815754460648913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35186706775754339280865217 26390030081815754460648913)
            ·
              refine ⟨19792522561361815845486685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26390030081815754460648913 19792522561361815845486685)
              ·
                refine ⟨7422195960510680942057507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19792522561361815845486685 7422195960510680942057507)
                ·
                  refine ⟨11133293940766021413086261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7422195960510680942057507 11133293940766021413086261)
                  ·
                    refine ⟨1043746306946814507476837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11133293940766021413086261 1043746306946814507476837)
                    ·
                      rfl

theorem cell23_6098066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_6098066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098066 prefixEnd_6098066 := by exact prefixLift 6098066
  have htrace : WordTrace (prefixWord ++ tailWord_6098066) baseStart_6098066 baseEnd_6098066 := by
    simpa [prefixWord, tailWord_6098066, baseEnd_6098066] using wordTrace_append hprefix tailTrace_6098066
  have hstable : (prefixWord ++ tailWord_6098066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098066).length < 2 ^ (prefixWord ++ tailWord_6098066).sum := by decide
  have hdescent : baseEnd_6098066 < baseStart_6098066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098080 : List Nat := [2, 1, 1, 4, 2, 1, 5, 2, 1, 1, 3]
def baseStart_6098080 : Nat := 118140960795 + 6098080 * 2 ^ 59
def prefixEnd_6098080 : Nat := 4983230072969 + 3 ^ 40 * 6098080 * 2
def baseEnd_6098080 : Nat := 3131246109569606467655447

theorem tailTrace_6098080 : CollatzResearch.WordTrace tailWord_6098080 prefixEnd_6098080 3131246109569606467655447 := by
  unfold tailWord_6098080
  simp only [CollatzResearch.WordTrace]
  refine ⟨111207624873852551996757847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148276833165136735995677129 111207624873852551996757847)
  ·
    refine ⟨166811437310778827995136771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111207624873852551996757847 166811437310778827995136771)
    ·
      refine ⟨250217155966168241992705157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166811437310778827995136771 250217155966168241992705157)
      ·
        refine ⟨46915716743656545373632217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 250217155966168241992705157 46915716743656545373632217)
        ·
          refine ⟨35186787557742409030224163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46915716743656545373632217 35186787557742409030224163)
          ·
            refine ⟨52780181336613613545336245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35186787557742409030224163 52780181336613613545336245)
            ·
              refine ⟨4948142000307526269875273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52780181336613613545336245 4948142000307526269875273)
              ·
                refine ⟨3711106500230644702406455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4948142000307526269875273 3711106500230644702406455)
                ·
                  refine ⟨5566659750345967053609683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3711106500230644702406455 5566659750345967053609683)
                  ·
                    refine ⟨8349989625518950580414525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5566659750345967053609683 8349989625518950580414525)
                    ·
                      refine ⟨3131246109569606467655447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8349989625518950580414525 3131246109569606467655447)
                      ·
                        rfl

theorem cell23_6098080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_6098080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098080 prefixEnd_6098080 := by exact prefixLift 6098080
  have htrace : WordTrace (prefixWord ++ tailWord_6098080) baseStart_6098080 baseEnd_6098080 := by
    simpa [prefixWord, tailWord_6098080, baseEnd_6098080] using wordTrace_append hprefix tailTrace_6098080
  have hstable : (prefixWord ++ tailWord_6098080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098080).length < 2 ^ (prefixWord ++ tailWord_6098080).sum := by decide
  have hdescent : baseEnd_6098080 < baseStart_6098080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098180 : List Nat := [2, 3, 2, 2, 2, 2, 1, 3, 1, 3, 2]
def baseStart_6098180 : Nat := 118140960795 + 6098180 * 2 ^ 59
def prefixEnd_6098180 : Nat := 4983230072969 + 3 ^ 40 * 6098180 * 2
def baseEnd_6098180 : Nat := 3131297457635056076404987

theorem tailTrace_6098180 : CollatzResearch.WordTrace tailWord_6098180 prefixEnd_6098180 3131297457635056076404987 := by
  unfold tailWord_6098180
  simp only [CollatzResearch.WordTrace]
  refine ⟨111209448523671410536077997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148279264698228547381437329 111209448523671410536077997)
  ·
    refine ⟨41703543196376778951029249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111209448523671410536077997 41703543196376778951029249)
    ·
      refine ⟨31277657397282584213271937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41703543196376778951029249 31277657397282584213271937)
      ·
        refine ⟨23458243047961938159953953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31277657397282584213271937 23458243047961938159953953)
        ·
          refine ⟨17593682285971453619965465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23458243047961938159953953 17593682285971453619965465)
          ·
            refine ⟨13195261714478590214974099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17593682285971453619965465 13195261714478590214974099)
            ·
              refine ⟨19792892571717885322461149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13195261714478590214974099 19792892571717885322461149)
              ·
                refine ⟨7422334714394206995922931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19792892571717885322461149 7422334714394206995922931)
                ·
                  refine ⟨11133502071591310493884397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7422334714394206995922931 11133502071591310493884397)
                  ·
                    refine ⟨4175063276846741435206649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11133502071591310493884397 4175063276846741435206649)
                    ·
                      refine ⟨3131297457635056076404987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4175063276846741435206649 3131297457635056076404987)
                      ·
                        rfl

theorem cell23_6098180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_6098180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098180 prefixEnd_6098180 := by exact prefixLift 6098180
  have htrace : WordTrace (prefixWord ++ tailWord_6098180) baseStart_6098180 baseEnd_6098180 := by
    simpa [prefixWord, tailWord_6098180, baseEnd_6098180] using wordTrace_append hprefix tailTrace_6098180
  have hstable : (prefixWord ++ tailWord_6098180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098180).length < 2 ^ (prefixWord ++ tailWord_6098180).sum := by decide
  have hdescent : baseEnd_6098180 < baseStart_6098180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098193 : List Nat := [1, 2, 2, 1, 1, 4, 3, 1, 4, 2, 2]
def baseStart_6098193 : Nat := 118140960795 + 6098193 * 2 ^ 59
def prefixEnd_6098193 : Nat := 4983230072969 + 3 ^ 40 * 6098193 * 2
def baseEnd_6098193 : Nat := 3131304132883564525542427

theorem tailTrace_6098193 : CollatzResearch.WordTrace tailWord_6098193 prefixEnd_6098193 3131304132883564525542427 := by
  unfold tailWord_6098193
  simp only [CollatzResearch.WordTrace]
  refine ⟨222419371196295724292379233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148279580797530482861586155 222419371196295724292379233)
  ·
    refine ⟨166814528397221793219284425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222419371196295724292379233 166814528397221793219284425)
    ·
      refine ⟨125110896297916344914463319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166814528397221793219284425 125110896297916344914463319)
      ·
        refine ⟨187666344446874517371694979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125110896297916344914463319 187666344446874517371694979)
        ·
          refine ⟨281499516670311776057542469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187666344446874517371694979 281499516670311776057542469)
          ·
            refine ⟨52781159375683458010789213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 281499516670311776057542469 52781159375683458010789213)
            ·
              refine ⟨19792934765881296754045955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52781159375683458010789213 19792934765881296754045955)
              ·
                refine ⟨29689402148821945131068933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19792934765881296754045955 29689402148821945131068933)
                ·
                  refine ⟨5566762902904114712075425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29689402148821945131068933 5566762902904114712075425)
                  ·
                    refine ⟨4175072177178086034056569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5566762902904114712075425 4175072177178086034056569)
                    ·
                      refine ⟨3131304132883564525542427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4175072177178086034056569 3131304132883564525542427)
                      ·
                        rfl

theorem cell23_6098193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 2, 2].length) (baseStart_6098193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098193 prefixEnd_6098193 := by exact prefixLift 6098193
  have htrace : WordTrace (prefixWord ++ tailWord_6098193) baseStart_6098193 baseEnd_6098193 := by
    simpa [prefixWord, tailWord_6098193, baseEnd_6098193] using wordTrace_append hprefix tailTrace_6098193
  have hstable : (prefixWord ++ tailWord_6098193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098193).length < 2 ^ (prefixWord ++ tailWord_6098193).sum := by decide
  have hdescent : baseEnd_6098193 < baseStart_6098193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098216 : List Nat := [2, 1, 5, 1, 2, 1, 2, 2, 7]
def baseStart_6098216 : Nat := 118140960795 + 6098216 * 2 ^ 59
def prefixEnd_6098216 : Nat := 4983230072969 + 3 ^ 40 * 6098216 * 2
def baseEnd_6098216 : Nat := 347923993659846437283869

theorem tailTrace_6098216 : CollatzResearch.WordTrace tailWord_6098216 prefixEnd_6098216 347923993659846437283869 := by
  unfold tailWord_6098216
  simp only [CollatzResearch.WordTrace]
  refine ⟨111210105037606199610233251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148280140050141599480311001 111210105037606199610233251)
  ·
    refine ⟨166815157556409299415349877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111210105037606199610233251 166815157556409299415349877)
    ·
      refine ⟨15638921020913371820189051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166815157556409299415349877 15638921020913371820189051)
      ·
        refine ⟨23458381531370057730283577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15638921020913371820189051 23458381531370057730283577)
        ·
          refine ⟨17593786148527543297712683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23458381531370057730283577 17593786148527543297712683)
          ·
            refine ⟨26390679222791314946569025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17593786148527543297712683 26390679222791314946569025)
            ·
              refine ⟨19793009417093486209926769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26390679222791314946569025 19793009417093486209926769)
              ·
                refine ⟨14844757062820114657445077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19793009417093486209926769 14844757062820114657445077)
                ·
                  refine ⟨347923993659846437283869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14844757062820114657445077 347923993659846437283869)
                  ·
                    rfl

theorem cell23_6098216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 7].length) (baseStart_6098216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098216 prefixEnd_6098216 := by exact prefixLift 6098216
  have htrace : WordTrace (prefixWord ++ tailWord_6098216) baseStart_6098216 baseEnd_6098216 := by
    simpa [prefixWord, tailWord_6098216, baseEnd_6098216] using wordTrace_append hprefix tailTrace_6098216
  have hstable : (prefixWord ++ tailWord_6098216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098216).length < 2 ^ (prefixWord ++ tailWord_6098216).sum := by decide
  have hdescent : baseEnd_6098216 < baseStart_6098216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098230 : List Nat := [5, 1, 2, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_6098230 : Nat := 118140960795 + 6098230 * 2 ^ 59
def prefixEnd_6098230 : Nat := 4983230072969 + 3 ^ 40 * 6098230 * 2
def baseEnd_6098230 : Nat := 3131323131667780880779757

theorem tailTrace_6098230 : CollatzResearch.WordTrace tailWord_6098230 prefixEnd_6098230 3131323131667780880779757 := by
  unfold tailWord_6098230
  simp only [CollatzResearch.WordTrace]
  refine ⟨13901295043572604975717259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148280480464774453074317429 13901295043572604975717259)
  ·
    refine ⟨20851942565358907463575889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13901295043572604975717259 20851942565358907463575889)
    ·
      refine ⟨15638956924019180597681917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20851942565358907463575889 15638956924019180597681917)
      ·
        refine ⟨5864608846507192724130719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15638956924019180597681917 5864608846507192724130719)
        ·
          refine ⟨8796913269760789086196079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5864608846507192724130719 8796913269760789086196079)
          ·
            refine ⟨13195369904641183629294119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8796913269760789086196079 13195369904641183629294119)
            ·
              refine ⟨19793054856961775443941179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13195369904641183629294119 19793054856961775443941179)
              ·
                refine ⟨29689582285442663165911769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19793054856961775443941179 29689582285442663165911769)
                ·
                  refine ⟨22267186714081997374433827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29689582285442663165911769 22267186714081997374433827)
                  ·
                    refine ⟨33400780071122996061650741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22267186714081997374433827 33400780071122996061650741)
                    ·
                      refine ⟨3131323131667780880779757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33400780071122996061650741 3131323131667780880779757)
                      ·
                        rfl

theorem cell23_6098230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_6098230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098230 prefixEnd_6098230 := by exact prefixLift 6098230
  have htrace : WordTrace (prefixWord ++ tailWord_6098230) baseStart_6098230 baseEnd_6098230 := by
    simpa [prefixWord, tailWord_6098230, baseEnd_6098230] using wordTrace_append hprefix tailTrace_6098230
  have hstable : (prefixWord ++ tailWord_6098230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098230).length < 2 ^ (prefixWord ++ tailWord_6098230).sum := by decide
  have hdescent : baseEnd_6098230 < baseStart_6098230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098289 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 10]
def baseStart_6098289 : Nat := 118140960795 + 6098289 * 2 ^ 59
def prefixEnd_6098289 : Nat := 4983230072969 + 3 ^ 40 * 6098289 * 2
def baseEnd_6098289 : Nat := 347928158558488461104665

theorem tailTrace_6098289 : CollatzResearch.WordTrace tailWord_6098289 prefixEnd_6098289 347928158558488461104665 := by
  unfold tailWord_6098289
  simp only [CollatzResearch.WordTrace]
  refine ⟨222422872603947932687873921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148281915069298621791915947 222422872603947932687873921)
  ·
    refine ⟨166817154452960949515905441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222422872603947932687873921 166817154452960949515905441)
    ·
      refine ⟨125112865839720712136929081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166817154452960949515905441 125112865839720712136929081)
      ·
        refine ⟨93834649379790534102696811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125112865839720712136929081 93834649379790534102696811)
        ·
          refine ⟨140751974069685801154045217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93834649379790534102696811 140751974069685801154045217)
          ·
            refine ⟨105563980552264350865533913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140751974069685801154045217 105563980552264350865533913)
            ·
              refine ⟨79172985414198263149150435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105563980552264350865533913 79172985414198263149150435)
              ·
                refine ⟨118759478121297394723725653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79172985414198263149150435 118759478121297394723725653)
                ·
                  refine ⟨347928158558488461104665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 118759478121297394723725653 347928158558488461104665)
                  ·
                    rfl

theorem cell23_6098289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 10].length) (baseStart_6098289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098289 prefixEnd_6098289 := by exact prefixLift 6098289
  have htrace : WordTrace (prefixWord ++ tailWord_6098289) baseStart_6098289 baseEnd_6098289 := by
    simpa [prefixWord, tailWord_6098289, baseEnd_6098289] using wordTrace_append hprefix tailTrace_6098289
  have hstable : (prefixWord ++ tailWord_6098289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098289).length < 2 ^ (prefixWord ++ tailWord_6098289).sum := by decide
  have hdescent : baseEnd_6098289 < baseStart_6098289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098334 : List Nat := [4, 3, 1, 2, 3, 1, 1, 1, 2, 1, 4]
def baseStart_6098334 : Nat := 118140960795 + 6098334 * 2 ^ 59
def prefixEnd_6098334 : Nat := 4983230072969 + 3 ^ 40 * 6098334 * 2
def baseEnd_6098334 : Nat := 3131376533655848473879279

theorem tailTrace_6098334 : CollatzResearch.WordTrace tailWord_6098334 prefixEnd_6098334 3131376533655848473879279 := by
  unfold tailWord_6098334
  simp only [CollatzResearch.WordTrace]
  refine ⟨27803064236098113171657757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148283009259189936915508037 27803064236098113171657757)
  ·
    refine ⟨10426149088536792439371659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27803064236098113171657757 10426149088536792439371659)
    ·
      refine ⟨15639223632805188659057489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10426149088536792439371659 15639223632805188659057489)
      ·
        refine ⟨11729417724603891494293117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15639223632805188659057489 11729417724603891494293117)
        ·
          refine ⟨4398531646726459310359919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11729417724603891494293117 4398531646726459310359919)
          ·
            refine ⟨6597797470089688965539879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4398531646726459310359919 6597797470089688965539879)
            ·
              refine ⟨9896696205134533448309819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6597797470089688965539879 9896696205134533448309819)
              ·
                refine ⟨14845044307701800172464729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9896696205134533448309819 14845044307701800172464729)
                ·
                  refine ⟨11133783230776350129348547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14845044307701800172464729 11133783230776350129348547)
                  ·
                    refine ⟨16700674846164525194022821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11133783230776350129348547 16700674846164525194022821)
                    ·
                      refine ⟨3131376533655848473879279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16700674846164525194022821 3131376533655848473879279)
                      ·
                        rfl

theorem cell23_6098334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_6098334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098334 prefixEnd_6098334 := by exact prefixLift 6098334
  have htrace : WordTrace (prefixWord ++ tailWord_6098334) baseStart_6098334 baseEnd_6098334 := by
    simpa [prefixWord, tailWord_6098334, baseEnd_6098334] using wordTrace_append hprefix tailTrace_6098334
  have hstable : (prefixWord ++ tailWord_6098334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098334).length < 2 ^ (prefixWord ++ tailWord_6098334).sum := by decide
  have hdescent : baseEnd_6098334 < baseStart_6098334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098336 : List Nat := [2, 1, 1, 4, 1, 2, 1, 3, 3, 5]
def baseStart_6098336 : Nat := 118140960795 + 6098336 * 2 ^ 59
def prefixEnd_6098336 : Nat := 4983230072969 + 3 ^ 40 * 6098336 * 2
def baseEnd_6098336 : Nat := 1043792520205719155351423

theorem tailTrace_6098336 : CollatzResearch.WordTrace tailWord_6098336 prefixEnd_6098336 1043792520205719155351423 := by
  unfold tailWord_6098336
  simp only [CollatzResearch.WordTrace]
  refine ⟨111212293417388829857417431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148283057889851773143223241 111212293417388829857417431)
  ·
    refine ⟨166818440126083244786126147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111212293417388829857417431 166818440126083244786126147)
    ·
      refine ⟨250227660189124867179189221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166818440126083244786126147 250227660189124867179189221)
      ·
        refine ⟨46917686285460912596097979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 250227660189124867179189221 46917686285460912596097979)
        ·
          refine ⟨70376529428191368894146969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46917686285460912596097979 70376529428191368894146969)
          ·
            refine ⟨52782397071143526670610227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70376529428191368894146969 52782397071143526670610227)
            ·
              refine ⟨79173595606715290005915341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52782397071143526670610227 79173595606715290005915341)
              ·
                refine ⟨29690098352518233752218253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79173595606715290005915341 29690098352518233752218253)
                ·
                  refine ⟨11133786882194337657081845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29690098352518233752218253 11133786882194337657081845)
                  ·
                    refine ⟨1043792520205719155351423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11133786882194337657081845 1043792520205719155351423)
                    ·
                      rfl

theorem cell23_6098336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 3, 5].length) (baseStart_6098336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098336 prefixEnd_6098336 := by exact prefixLift 6098336
  have htrace : WordTrace (prefixWord ++ tailWord_6098336) baseStart_6098336 baseEnd_6098336 := by
    simpa [prefixWord, tailWord_6098336, baseEnd_6098336] using wordTrace_append hprefix tailTrace_6098336
  have hstable : (prefixWord ++ tailWord_6098336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098336).length < 2 ^ (prefixWord ++ tailWord_6098336).sum := by decide
  have hdescent : baseEnd_6098336 < baseStart_6098336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098344 : List Nat := [2, 1, 6, 1, 2, 1, 2, 3, 1, 4]
def baseStart_6098344 : Nat := 118140960795 + 6098344 * 2 ^ 59
def prefixEnd_6098344 : Nat := 4983230072969 + 3 ^ 40 * 6098344 * 2
def baseEnd_6098344 : Nat := 1043793889487464478251411

theorem tailTrace_6098344 : CollatzResearch.WordTrace tailWord_6098344 prefixEnd_6098344 1043793889487464478251411 := by
  unfold tailWord_6098344
  simp only [CollatzResearch.WordTrace]
  refine ⟨111212439309374338540563043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148283252412499118054084057 111212439309374338540563043)
  ·
    refine ⟨166818658964061507810844565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111212439309374338540563043 166818658964061507810844565)
    ·
      refine ⟨7819624638940383178633339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 166818658964061507810844565 7819624638940383178633339)
      ·
        refine ⟨11729436958410574767950009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7819624638940383178633339 11729436958410574767950009)
        ·
          refine ⟨8797077718807931075962507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11729436958410574767950009 8797077718807931075962507)
          ·
            refine ⟨13195616578211896613943761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8797077718807931075962507 13195616578211896613943761)
            ·
              refine ⟨9896712433658922460457821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13195616578211896613943761 9896712433658922460457821)
              ·
                refine ⟨3711267162622095922671683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9896712433658922460457821 3711267162622095922671683)
                ·
                  refine ⟨5566900743933143884007525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3711267162622095922671683 5566900743933143884007525)
                  ·
                    refine ⟨1043793889487464478251411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5566900743933143884007525 1043793889487464478251411)
                    ·
                      rfl

theorem cell23_6098344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_6098344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098344 prefixEnd_6098344 := by exact prefixLift 6098344
  have htrace : WordTrace (prefixWord ++ tailWord_6098344) baseStart_6098344 baseEnd_6098344 := by
    simpa [prefixWord, tailWord_6098344, baseEnd_6098344] using wordTrace_append hprefix tailTrace_6098344
  have hstable : (prefixWord ++ tailWord_6098344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098344).length < 2 ^ (prefixWord ++ tailWord_6098344).sum := by decide
  have hdescent : baseEnd_6098344 < baseStart_6098344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098353 : List Nat := [1, 2, 2, 4, 1, 1, 3, 3, 1, 5]
def baseStart_6098353 : Nat := 118140960795 + 6098353 * 2 ^ 59
def prefixEnd_6098353 : Nat := 4983230072969 + 3 ^ 40 * 6098353 * 2
def baseEnd_6098353 : Nat := 1043795429929427966513897

theorem tailTrace_6098353 : CollatzResearch.WordTrace tailWord_6098353 prefixEnd_6098353 1043795429929427966513897 := by
  unfold tailWord_6098353
  simp only [CollatzResearch.WordTrace]
  refine ⟨222425206875716071618203713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148283471250477381078802475 222425206875716071618203713)
  ·
    refine ⟨166818905156787053713652785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222425206875716071618203713 166818905156787053713652785)
    ·
      refine ⟨125114178867590290285239589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166818905156787053713652785 125114178867590290285239589)
      ·
        refine ⟨23458908537673179428482423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125114178867590290285239589 23458908537673179428482423)
        ·
          refine ⟨35188362806509769142723635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23458908537673179428482423 35188362806509769142723635)
          ·
            refine ⟨52782544209764653714085453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35188362806509769142723635 52782544209764653714085453)
            ·
              refine ⟨19793454078661745142782045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52782544209764653714085453 19793454078661745142782045)
              ·
                refine ⟨7422545279498154428543267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19793454078661745142782045 7422545279498154428543267)
                ·
                  refine ⟨11133817919247231642814901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7422545279498154428543267 11133817919247231642814901)
                  ·
                    refine ⟨1043795429929427966513897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11133817919247231642814901 1043795429929427966513897)
                    ·
                      rfl

theorem cell23_6098353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 5].length) (baseStart_6098353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098353 prefixEnd_6098353 := by exact prefixLift 6098353
  have htrace : WordTrace (prefixWord ++ tailWord_6098353) baseStart_6098353 baseEnd_6098353 := by
    simpa [prefixWord, tailWord_6098353, baseEnd_6098353] using wordTrace_append hprefix tailTrace_6098353
  have hstable : (prefixWord ++ tailWord_6098353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098353).length < 2 ^ (prefixWord ++ tailWord_6098353).sum := by decide
  have hdescent : baseEnd_6098353 < baseStart_6098353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098383 : List Nat := [1, 1, 2, 1, 1, 4, 2, 5, 2, 4]
def baseStart_6098383 : Nat := 118140960795 + 6098383 * 2 ^ 59
def prefixEnd_6098383 : Nat := 4983230072969 + 3 ^ 40 * 6098383 * 2
def baseEnd_6098383 : Nat := 1043800564735972927388851

theorem tailTrace_6098383 : CollatzResearch.WordTrace tailWord_6098383 prefixEnd_6098383 1043800564735972927388851 := by
  unfold tailWord_6098383
  simp only [CollatzResearch.WordTrace]
  refine ⟨222426301065607386741795803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148284200710404924494530535 222426301065607386741795803)
  ·
    refine ⟨333639451598411080112693705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222426301065607386741795803 333639451598411080112693705)
    ·
      refine ⟨250229588698808310084520279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333639451598411080112693705 250229588698808310084520279)
      ·
        refine ⟨375344383048212465126780419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250229588698808310084520279 375344383048212465126780419)
        ·
          refine ⟨563016574572318697690170629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375344383048212465126780419 563016574572318697690170629)
          ·
            refine ⟨105565607732309755816906993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 563016574572318697690170629 105565607732309755816906993)
            ·
              refine ⟨79174205799232316862680245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105565607732309755816906993 79174205799232316862680245)
              ·
                refine ⟨7422581793678029705876273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79174205799232316862680245 7422581793678029705876273)
                ·
                  refine ⟨5566936345258522279407205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7422581793678029705876273 5566936345258522279407205)
                  ·
                    refine ⟨1043800564735972927388851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5566936345258522279407205 1043800564735972927388851)
                    ·
                      rfl

theorem cell23_6098383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 4].length) (baseStart_6098383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098383 prefixEnd_6098383 := by exact prefixLift 6098383
  have htrace : WordTrace (prefixWord ++ tailWord_6098383) baseStart_6098383 baseEnd_6098383 := by
    simpa [prefixWord, tailWord_6098383, baseEnd_6098383] using wordTrace_append hprefix tailTrace_6098383
  have hstable : (prefixWord ++ tailWord_6098383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098383).length < 2 ^ (prefixWord ++ tailWord_6098383).sum := by decide
  have hdescent : baseEnd_6098383 < baseStart_6098383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098410 : List Nat := [3, 1, 3, 1, 4, 1, 2, 1, 1, 1, 5]
def baseStart_6098410 : Nat := 118140960795 + 6098410 * 2 ^ 59
def prefixEnd_6098410 : Nat := 4983230072969 + 3 ^ 40 * 6098410 * 2
def baseEnd_6098410 : Nat := 3131415558185590176528929

theorem tailTrace_6098410 : CollatzResearch.WordTrace tailWord_6098410 prefixEnd_6098410 3131415558185590176528929 := by
  unfold tailWord_6098410
  simp only [CollatzResearch.WordTrace]
  refine ⟨55606821459127392588257171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148284857224339713568685789 55606821459127392588257171)
  ·
    refine ⟨83410232188691088882385757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55606821459127392588257171 83410232188691088882385757)
    ·
      refine ⟨31278837070759158330894659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83410232188691088882385757 31278837070759158330894659)
      ·
        refine ⟨46918255606138737496341989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31278837070759158330894659 46918255606138737496341989)
        ·
          refine ⟨8797172926151013280564123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46918255606138737496341989 8797172926151013280564123)
          ·
            refine ⟨13195759389226519920846185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8797172926151013280564123 13195759389226519920846185)
            ·
              refine ⟨9896819541919889940634639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13195759389226519920846185 9896819541919889940634639)
              ·
                refine ⟨14845229312879834910951959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9896819541919889940634639 14845229312879834910951959)
                ·
                  refine ⟨22267843969319752366427939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14845229312879834910951959 22267843969319752366427939)
                  ·
                    refine ⟨33401765953979628549641909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22267843969319752366427939 33401765953979628549641909)
                    ·
                      refine ⟨3131415558185590176528929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33401765953979628549641909 3131415558185590176528929)
                      ·
                        rfl

theorem cell23_6098410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_6098410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098410 prefixEnd_6098410 := by exact prefixLift 6098410
  have htrace : WordTrace (prefixWord ++ tailWord_6098410) baseStart_6098410 baseEnd_6098410 := by
    simpa [prefixWord, tailWord_6098410, baseEnd_6098410] using wordTrace_append hprefix tailTrace_6098410
  have hstable : (prefixWord ++ tailWord_6098410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098410).length < 2 ^ (prefixWord ++ tailWord_6098410).sum := by decide
  have hdescent : baseEnd_6098410 < baseStart_6098410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098426 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 2, 7]
def baseStart_6098426 : Nat := 118140960795 + 6098426 * 2 ^ 59
def prefixEnd_6098426 : Nat := 4983230072969 + 3 ^ 40 * 6098426 * 2
def baseEnd_6098426 : Nat := 1043807924625354037976285

theorem tailTrace_6098426 : CollatzResearch.WordTrace tailWord_6098426 prefixEnd_6098426 1043807924625354037976285 := by
  unfold tailWord_6098426
  simp only [CollatzResearch.WordTrace]
  refine ⟨55606967351112901271402783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148285246269634403390407421 55606967351112901271402783)
  ·
    refine ⟨83410451026669351907104175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55606967351112901271402783 83410451026669351907104175)
    ·
      refine ⟨125115676540004027860656263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83410451026669351907104175 125115676540004027860656263)
      ·
        refine ⟨187673514810006041790984395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125115676540004027860656263 187673514810006041790984395)
        ·
          refine ⟨281510272215009062686476593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187673514810006041790984395 281510272215009062686476593)
          ·
            refine ⟨211132704161256797014857445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281510272215009062686476593 211132704161256797014857445)
            ·
              refine ⟨39587382030235649440285771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 211132704161256797014857445 39587382030235649440285771)
              ·
                refine ⟨59381073045353474160428657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39587382030235649440285771 59381073045353474160428657)
                ·
                  refine ⟨44535804784015105620321493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59381073045353474160428657 44535804784015105620321493)
                  ·
                    refine ⟨1043807924625354037976285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44535804784015105620321493 1043807924625354037976285)
                    ·
                      rfl

theorem cell23_6098426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_6098426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098426 prefixEnd_6098426 := by exact prefixLift 6098426
  have htrace : WordTrace (prefixWord ++ tailWord_6098426) baseStart_6098426 baseEnd_6098426 := by
    simpa [prefixWord, tailWord_6098426, baseEnd_6098426] using wordTrace_append hprefix tailTrace_6098426
  have hstable : (prefixWord ++ tailWord_6098426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098426).length < 2 ^ (prefixWord ++ tailWord_6098426).sum := by decide
  have hdescent : baseEnd_6098426 < baseStart_6098426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098434 : List Nat := [3, 4, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_6098434 : Nat := 118140960795 + 6098434 * 2 ^ 59
def prefixEnd_6098434 : Nat := 4983230072969 + 3 ^ 40 * 6098434 * 2
def baseEnd_6098434 : Nat := 1043809293907099360876273

theorem tailTrace_6098434 : CollatzResearch.WordTrace tailWord_6098434 prefixEnd_6098434 1043809293907099360876273 := by
  unfold tailWord_6098434
  simp only [CollatzResearch.WordTrace]
  refine ⟨55607040297105655612975589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148285440792281748301268237 55607040297105655612975589)
  ·
    refine ⟨10426320055707310427432923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55607040297105655612975589 10426320055707310427432923)
    ·
      refine ⟨15639480083560965641149385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10426320055707310427432923 15639480083560965641149385)
      ·
        refine ⟨11729610062670724230862039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15639480083560965641149385 11729610062670724230862039)
        ·
          refine ⟨17594415094006086346293059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11729610062670724230862039 17594415094006086346293059)
          ·
            refine ⟨26391622641009129519439589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17594415094006086346293059 26391622641009129519439589)
            ·
              refine ⟨4948429245189211784894923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26391622641009129519439589 4948429245189211784894923)
              ·
                refine ⟨7422643867783817677342385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4948429245189211784894923 7422643867783817677342385)
                ·
                  refine ⟨5566982900837863258006789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7422643867783817677342385 5566982900837863258006789)
                  ·
                    refine ⟨1043809293907099360876273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5566982900837863258006789 1043809293907099360876273)
                    ·
                      rfl

theorem cell23_6098434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_6098434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098434 prefixEnd_6098434 := by exact prefixLift 6098434
  have htrace : WordTrace (prefixWord ++ tailWord_6098434) baseStart_6098434 baseEnd_6098434 := by
    simpa [prefixWord, tailWord_6098434, baseEnd_6098434] using wordTrace_append hprefix tailTrace_6098434
  have hstable : (prefixWord ++ tailWord_6098434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098434).length < 2 ^ (prefixWord ++ tailWord_6098434).sum := by decide
  have hdescent : baseEnd_6098434 < baseStart_6098434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098438 : List Nat := [6, 2, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_6098438 : Nat := 118140960795 + 6098438 * 2 ^ 59
def prefixEnd_6098438 : Nat := 4983230072969 + 3 ^ 40 * 6098438 * 2
def baseEnd_6098438 : Nat := 1043809978547972022326267

theorem tailTrace_6098438 : CollatzResearch.WordTrace tailWord_6098438 prefixEnd_6098438 1043809978547972022326267 := by
  unfold tailWord_6098438
  simp only [CollatzResearch.WordTrace]
  refine ⟨6950884596262754097970249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 148285538053605420756698645 6950884596262754097970249)
  ·
    refine ⟨5213163447197065573477687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6950884596262754097970249 5213163447197065573477687)
    ·
      refine ⟨7819745170795598360216531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5213163447197065573477687 7819745170795598360216531)
      ·
        refine ⟨11729617756193397540324797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7819745170795598360216531 11729617756193397540324797)
        ·
          refine ⟨4398606658572524077621799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11729617756193397540324797 4398606658572524077621799)
          ·
            refine ⟨6597909987858786116432699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4398606658572524077621799 6597909987858786116432699)
            ·
              refine ⟨9896864981788179174649049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6597909987858786116432699 9896864981788179174649049)
              ·
                refine ⟨7422648736341134380986787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9896864981788179174649049 7422648736341134380986787)
                ·
                  refine ⟨11133973104511701571480181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7422648736341134380986787 11133973104511701571480181)
                  ·
                    refine ⟨1043809978547972022326267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11133973104511701571480181 1043809978547972022326267)
                    ·
                      rfl

theorem cell23_6098438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_6098438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098438 prefixEnd_6098438 := by exact prefixLift 6098438
  have htrace : WordTrace (prefixWord ++ tailWord_6098438) baseStart_6098438 baseEnd_6098438 := by
    simpa [prefixWord, tailWord_6098438, baseEnd_6098438] using wordTrace_append hprefix tailTrace_6098438
  have hstable : (prefixWord ++ tailWord_6098438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098438).length < 2 ^ (prefixWord ++ tailWord_6098438).sum := by decide
  have hdescent : baseEnd_6098438 < baseStart_6098438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098444 : List Nat := [2, 2, 1, 2, 6, 1, 1, 2, 1, 2, 3]
def baseStart_6098444 : Nat := 118140960795 + 6098444 * 2 ^ 59
def prefixEnd_6098444 : Nat := 4983230072969 + 3 ^ 40 * 6098444 * 2
def baseEnd_6098444 : Nat := 3131433016527843043503773

theorem tailTrace_6098444 : CollatzResearch.WordTrace tailWord_6098444 prefixEnd_6098444 3131433016527843043503773 := by
  unfold tailWord_6098444
  simp only [CollatzResearch.WordTrace]
  refine ⟨111214262959193197079883193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148285683945590929439844257 111214262959193197079883193)
  ·
    refine ⟨83410697219394897809912395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111214262959193197079883193 83410697219394897809912395)
    ·
      refine ⟨125116045829092346714868593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83410697219394897809912395 125116045829092346714868593)
      ·
        refine ⟨93837034371819260036151445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125116045829092346714868593 93837034371819260036151445)
        ·
          refine ⟨4398610986179027814194599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 93837034371819260036151445 4398610986179027814194599)
          ·
            refine ⟨6597916479268541721291899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4398610986179027814194599 6597916479268541721291899)
            ·
              refine ⟨9896874718902812581937849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6597916479268541721291899 9896874718902812581937849)
              ·
                refine ⟨7422656039177109436453387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9896874718902812581937849 7422656039177109436453387)
                ·
                  refine ⟨11133984058765664154680081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7422656039177109436453387 11133984058765664154680081)
                  ·
                    refine ⟨8350488044074248116010061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11133984058765664154680081 8350488044074248116010061)
                    ·
                      refine ⟨3131433016527843043503773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8350488044074248116010061 3131433016527843043503773)
                      ·
                        rfl

theorem cell23_6098444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 1, 2, 3].length) (baseStart_6098444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098444 prefixEnd_6098444 := by exact prefixLift 6098444
  have htrace : WordTrace (prefixWord ++ tailWord_6098444) baseStart_6098444 baseEnd_6098444 := by
    simpa [prefixWord, tailWord_6098444, baseEnd_6098444] using wordTrace_append hprefix tailTrace_6098444
  have hstable : (prefixWord ++ tailWord_6098444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098444).length < 2 ^ (prefixWord ++ tailWord_6098444).sum := by decide
  have hdescent : baseEnd_6098444 < baseStart_6098444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098476 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 6]
def baseStart_6098476 : Nat := 118140960795 + 6098476 * 2 ^ 59
def prefixEnd_6098476 : Nat := 4983230072969 + 3 ^ 40 * 6098476 * 2
def baseEnd_6098476 : Nat := 3131449447908786918303625

theorem tailTrace_6098476 : CollatzResearch.WordTrace tailWord_6098476 prefixEnd_6098476 3131449447908786918303625 := by
  unfold tailWord_6098476
  simp only [CollatzResearch.WordTrace]
  refine ⟨111214846527135231812465641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148286462036180309083287521 111214846527135231812465641)
  ·
    refine ⟨83411134895351423859349231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111214846527135231812465641 83411134895351423859349231)
    ·
      refine ⟨125116702343027135789023847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83411134895351423859349231 125116702343027135789023847)
      ·
        refine ⟨187675053514540703683535771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125116702343027135789023847 187675053514540703683535771)
        ·
          refine ⟨281512580271811055525303657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187675053514540703683535771 281512580271811055525303657)
          ·
            refine ⟨211134435203858291643977743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281512580271811055525303657 211134435203858291643977743)
            ·
              refine ⟨316701652805787437465966615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211134435203858291643977743 316701652805787437465966615)
              ·
                refine ⟨475052479208681156198949923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316701652805787437465966615 475052479208681156198949923)
                ·
                  refine ⟨712578718813021734298424885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 475052479208681156198949923 712578718813021734298424885)
                  ·
                    refine ⟨66804254888720787590477333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 712578718813021734298424885 66804254888720787590477333)
                    ·
                      refine ⟨3131449447908786918303625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66804254888720787590477333 3131449447908786918303625)
                      ·
                        rfl

theorem cell23_6098476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_6098476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098476 prefixEnd_6098476 := by exact prefixLift 6098476
  have htrace : WordTrace (prefixWord ++ tailWord_6098476) baseStart_6098476 baseEnd_6098476 := by
    simpa [prefixWord, tailWord_6098476, baseEnd_6098476] using wordTrace_append hprefix tailTrace_6098476
  have hstable : (prefixWord ++ tailWord_6098476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098476).length < 2 ^ (prefixWord ++ tailWord_6098476).sum := by decide
  have hdescent : baseEnd_6098476 < baseStart_6098476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098483 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 3]
def baseStart_6098483 : Nat := 118140960795 + 6098483 * 2 ^ 59
def prefixEnd_6098483 : Nat := 4983230072969 + 3 ^ 40 * 6098483 * 2
def baseEnd_6098483 : Nat := 3131453042273368390916093

theorem tailTrace_6098483 : CollatzResearch.WordTrace tailWord_6098483 prefixEnd_6098483 3131453042273368390916093 := by
  unfold tailWord_6098483
  simp only [CollatzResearch.WordTrace]
  refine ⟨222429948365245103820436103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148286632243496735880290735 222429948365245103820436103)
  ·
    refine ⟨333644922547867655730654155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222429948365245103820436103 333644922547867655730654155)
    ·
      refine ⟨500467383821801483595981233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333644922547867655730654155 500467383821801483595981233)
      ·
        refine ⟨375350537866351112696985925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 500467383821801483595981233 375350537866351112696985925)
        ·
          refine ⟨70378225849940833630684861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 375350537866351112696985925 70378225849940833630684861)
          ·
            refine ⟨26391834693727812611506823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70378225849940833630684861 26391834693727812611506823)
            ·
              refine ⟨39587752040591718917260235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26391834693727812611506823 39587752040591718917260235)
              ·
                refine ⟨59381628060887578375890353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39587752040591718917260235 59381628060887578375890353)
                ·
                  refine ⟨44536221045665683781917765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59381628060887578375890353 44536221045665683781917765)
                  ·
                    refine ⟨8350541446062315709109581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44536221045665683781917765 8350541446062315709109581)
                    ·
                      refine ⟨3131453042273368390916093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8350541446062315709109581 3131453042273368390916093)
                      ·
                        rfl

theorem cell23_6098483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 3].length) (baseStart_6098483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098483 prefixEnd_6098483 := by exact prefixLift 6098483
  have htrace : WordTrace (prefixWord ++ tailWord_6098483) baseStart_6098483 baseEnd_6098483 := by
    simpa [prefixWord, tailWord_6098483, baseEnd_6098483] using wordTrace_append hprefix tailTrace_6098483
  have hstable : (prefixWord ++ tailWord_6098483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098483).length < 2 ^ (prefixWord ++ tailWord_6098483).sum := by decide
  have hdescent : baseEnd_6098483 < baseStart_6098483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098497 : List Nat := [1, 2, 5, 1, 1, 1, 4, 1, 1, 4, 2]
def baseStart_6098497 : Nat := 118140960795 + 6098497 * 2 ^ 59
def prefixEnd_6098497 : Nat := 4983230072969 + 3 ^ 40 * 6098497 * 2
def baseEnd_6098497 : Nat := 3131460231002531336141029

theorem tailTrace_6098497 : CollatzResearch.WordTrace tailWord_6098497 prefixEnd_6098497 3131460231002531336141029 := by
  unfold tailWord_6098497
  simp only [CollatzResearch.WordTrace]
  refine ⟨222430458987194384211445745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148286972658129589474297163 222430458987194384211445745)
  ·
    refine ⟨166822844240395788158584309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222430458987194384211445745 166822844240395788158584309)
    ·
      refine ⟨15639641647537105139867279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166822844240395788158584309 15639641647537105139867279)
      ·
        refine ⟨23459462471305657709800919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15639641647537105139867279 23459462471305657709800919)
        ·
          refine ⟨35189193706958486564701379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23459462471305657709800919 35189193706958486564701379)
          ·
            refine ⟨52783790560437729847052069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35189193706958486564701379 52783790560437729847052069)
            ·
              refine ⟨9896960730082074346322263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52783790560437729847052069 9896960730082074346322263)
              ·
                refine ⟨14845441095123111519483395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9896960730082074346322263 14845441095123111519483395)
                ·
                  refine ⟨22268161642684667279225093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14845441095123111519483395 22268161642684667279225093)
                  ·
                    refine ⟨4175280308003375114854705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22268161642684667279225093 4175280308003375114854705)
                    ·
                      refine ⟨3131460231002531336141029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4175280308003375114854705 3131460231002531336141029)
                      ·
                        rfl

theorem cell23_6098497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_6098497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098497 prefixEnd_6098497 := by exact prefixLift 6098497
  have htrace : WordTrace (prefixWord ++ tailWord_6098497) baseStart_6098497 baseEnd_6098497 := by
    simpa [prefixWord, tailWord_6098497, baseEnd_6098497] using wordTrace_append hprefix tailTrace_6098497
  have hstable : (prefixWord ++ tailWord_6098497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098497).length < 2 ^ (prefixWord ++ tailWord_6098497).sum := by decide
  have hdescent : baseEnd_6098497 < baseStart_6098497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098513 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 1, 5, 3]
def baseStart_6098513 : Nat := 118140960795 + 6098513 * 2 ^ 59
def prefixEnd_6098513 : Nat := 4983230072969 + 3 ^ 40 * 6098513 * 2
def baseEnd_6098513 : Nat := 3131468446693003273540955

theorem tailTrace_6098513 : CollatzResearch.WordTrace tailWord_6098513 prefixEnd_6098513 3131468446693003273540955 := by
  unfold tailWord_6098513
  simp only [CollatzResearch.WordTrace]
  refine ⟨222431042555136418944028193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148287361703424279296018795 222431042555136418944028193)
  ·
    refine ⟨166823281916352314208021145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222431042555136418944028193 166823281916352314208021145)
    ·
      refine ⟨125117461437264235656015859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166823281916352314208021145 125117461437264235656015859)
      ·
        refine ⟨187676192155896353484023789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125117461437264235656015859 187676192155896353484023789)
        ·
          refine ⟨70378572058461132556508921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187676192155896353484023789 70378572058461132556508921)
          ·
            refine ⟨52783929043845849417381691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70378572058461132556508921 52783929043845849417381691)
            ·
              refine ⟨79175893565768774126072537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52783929043845849417381691 79175893565768774126072537)
              ·
                refine ⟨59381920174326580594554403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79175893565768774126072537 59381920174326580594554403)
                ·
                  refine ⟨89072880261489870891831605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59381920174326580594554403 89072880261489870891831605)
                  ·
                    refine ⟨8350582524514675396109213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89072880261489870891831605 8350582524514675396109213)
                    ·
                      refine ⟨3131468446693003273540955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8350582524514675396109213 3131468446693003273540955)
                      ·
                        rfl

theorem cell23_6098513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 5, 3].length) (baseStart_6098513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098513 prefixEnd_6098513 := by exact prefixLift 6098513
  have htrace : WordTrace (prefixWord ++ tailWord_6098513) baseStart_6098513 baseEnd_6098513 := by
    simpa [prefixWord, tailWord_6098513, baseEnd_6098513] using wordTrace_append hprefix tailTrace_6098513
  have hstable : (prefixWord ++ tailWord_6098513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098513).length < 2 ^ (prefixWord ++ tailWord_6098513).sum := by decide
  have hdescent : baseEnd_6098513 < baseStart_6098513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098518 : List Nat := [5, 2, 2, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_6098518 : Nat := 118140960795 + 6098518 * 2 ^ 59
def prefixEnd_6098518 : Nat := 4983230072969 + 3 ^ 40 * 6098518 * 2
def baseEnd_6098518 : Nat := 3131471014096275753978433

theorem tailTrace_6098518 : CollatzResearch.WordTrace tailWord_6098518 prefixEnd_6098518 3131471014096275753978433 := by
  unfold tailWord_6098518
  simp only [CollatzResearch.WordTrace]
  refine ⟨13901951557507394049872513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148287483280078869865306805 13901951557507394049872513)
  ·
    refine ⟨10426463668130545537404385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13901951557507394049872513 10426463668130545537404385)
    ·
      refine ⟨7819847751097909153053289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10426463668130545537404385 7819847751097909153053289)
      ·
        refine ⟨5864885813323431864789967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7819847751097909153053289 5864885813323431864789967)
        ·
          refine ⟨8797328719985147797184951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5864885813323431864789967 8797328719985147797184951)
          ·
            refine ⟨13195993079977721695777427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8797328719985147797184951 13195993079977721695777427)
            ·
              refine ⟨19793989619966582543666141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13195993079977721695777427 19793989619966582543666141)
              ·
                refine ⟨7422746107487468453874803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19793989619966582543666141 7422746107487468453874803)
                ·
                  refine ⟨11134119161231202680812205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7422746107487468453874803 11134119161231202680812205)
                  ·
                    refine ⟨4175294685461701005304577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11134119161231202680812205 4175294685461701005304577)
                    ·
                      refine ⟨3131471014096275753978433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4175294685461701005304577 3131471014096275753978433)
                      ·
                        rfl

theorem cell23_6098518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_6098518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098518 prefixEnd_6098518 := by exact prefixLift 6098518
  have htrace : WordTrace (prefixWord ++ tailWord_6098518) baseStart_6098518 baseEnd_6098518 := by
    simpa [prefixWord, tailWord_6098518, baseEnd_6098518] using wordTrace_append hprefix tailTrace_6098518
  have hstable : (prefixWord ++ tailWord_6098518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098518).length < 2 ^ (prefixWord ++ tailWord_6098518).sum := by decide
  have hdescent : baseEnd_6098518 < baseStart_6098518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098550 : List Nat := [5, 1, 1, 2, 2, 1, 1, 2, 1, 7]
def baseStart_6098550 : Nat := 118140960795 + 6098550 * 2 ^ 59
def prefixEnd_6098550 : Nat := 4983230072969 + 3 ^ 40 * 6098550 * 2
def baseEnd_6098550 : Nat := 1043829148492406542926095

theorem tailTrace_6098550 : CollatzResearch.WordTrace tailWord_6098550 prefixEnd_6098550 1043829148492406542926095 := by
  unfold tailWord_6098550
  simp only [CollatzResearch.WordTrace]
  refine ⟨13902024503500148391445319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148288261370668249508750069 13902024503500148391445319)
  ·
    refine ⟨20853036755250222587167979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13902024503500148391445319 20853036755250222587167979)
    ·
      refine ⟨31279555132875333880751969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20853036755250222587167979 31279555132875333880751969)
      ·
        refine ⟨23459666349656500410563977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31279555132875333880751969 23459666349656500410563977)
        ·
          refine ⟨17594749762242375307922983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23459666349656500410563977 17594749762242375307922983)
          ·
            refine ⟨26392124643363562961884475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17594749762242375307922983 26392124643363562961884475)
            ·
              refine ⟨39588186965045344442826713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26392124643363562961884475 39588186965045344442826713)
              ·
                refine ⟨29691140223784008332120035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39588186965045344442826713 29691140223784008332120035)
                ·
                  refine ⟨44536710335676012498180053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29691140223784008332120035 44536710335676012498180053)
                  ·
                    refine ⟨1043829148492406542926095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44536710335676012498180053 1043829148492406542926095)
                    ·
                      rfl

theorem cell23_6098550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_6098550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098550 prefixEnd_6098550 := by exact prefixLift 6098550
  have htrace : WordTrace (prefixWord ++ tailWord_6098550) baseStart_6098550 baseEnd_6098550 := by
    simpa [prefixWord, tailWord_6098550, baseEnd_6098550] using wordTrace_append hprefix tailTrace_6098550
  have hstable : (prefixWord ++ tailWord_6098550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098550).length < 2 ^ (prefixWord ++ tailWord_6098550).sum := by decide
  have hdescent : baseEnd_6098550 < baseStart_6098550 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098553 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 3, 3, 4]
def baseStart_6098553 : Nat := 118140960795 + 6098553 * 2 ^ 59
def prefixEnd_6098553 : Nat := 4983230072969 + 3 ^ 40 * 6098553 * 2
def baseEnd_6098553 : Nat := 3131488985919183117040771

theorem tailTrace_6098553 : CollatzResearch.WordTrace tailWord_6098553 prefixEnd_6098553 3131488985919183117040771 := by
  unfold tailWord_6098553
  simp only [CollatzResearch.WordTrace]
  refine ⟨222432501474991505775484313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148288334316661003850322875 222432501474991505775484313)
  ·
    refine ⟨166824376106243629331613235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222432501474991505775484313 166824376106243629331613235)
    ·
      refine ⟨250236564159365443997419853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166824376106243629331613235 250236564159365443997419853)
      ·
        refine ⟨93838711559762041499032445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250236564159365443997419853 93838711559762041499032445)
        ·
          refine ⟨35189516834910765562137167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93838711559762041499032445 35189516834910765562137167)
          ·
            refine ⟨52784275252366148343205751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35189516834910765562137167 52784275252366148343205751)
            ·
              refine ⟨79176412878549222514808627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52784275252366148343205751 79176412878549222514808627)
              ·
                refine ⟨118764619317823833772212941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79176412878549222514808627 118764619317823833772212941)
                ·
                  refine ⟨44536732244183937664579853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118764619317823833772212941 44536732244183937664579853)
                  ·
                    refine ⟨16701274591568976624217445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44536732244183937664579853 16701274591568976624217445)
                    ·
                      refine ⟨3131488985919183117040771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16701274591568976624217445 3131488985919183117040771)
                      ·
                        rfl

theorem cell23_6098553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_6098553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098553 prefixEnd_6098553 := by exact prefixLift 6098553
  have htrace : WordTrace (prefixWord ++ tailWord_6098553) baseStart_6098553 baseEnd_6098553 := by
    simpa [prefixWord, tailWord_6098553, baseEnd_6098553] using wordTrace_append hprefix tailTrace_6098553
  have hstable : (prefixWord ++ tailWord_6098553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098553).length < 2 ^ (prefixWord ++ tailWord_6098553).sum := by decide
  have hdescent : baseEnd_6098553 < baseStart_6098553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098570 : List Nat := [3, 1, 2, 3, 2, 1, 2, 1, 1, 3, 4]
def baseStart_6098570 : Nat := 118140960795 + 6098570 * 2 ^ 59
def prefixEnd_6098570 : Nat := 4983230072969 + 3 ^ 40 * 6098570 * 2
def baseEnd_6098570 : Nat := 3131497715090309550528193

theorem tailTrace_6098570 : CollatzResearch.WordTrace tailWord_6098570 prefixEnd_6098570 3131497715090309550528193 := by
  unfold tailWord_6098570
  simp only [CollatzResearch.WordTrace]
  refine ⟨55608280378982479419713291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148288747677286611785902109 55608280378982479419713291)
  ·
    refine ⟨83412420568473719129569937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55608280378982479419713291 83412420568473719129569937)
    ·
      refine ⟨62559315426355289347177453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83412420568473719129569937 62559315426355289347177453)
      ·
        refine ⟨23459743284883233505191545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62559315426355289347177453 23459743284883233505191545)
        ·
          refine ⟨17594807463662425128893659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23459743284883233505191545 17594807463662425128893659)
          ·
            refine ⟨26392211195493637693340489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17594807463662425128893659 26392211195493637693340489)
            ·
              refine ⟨19794158396620228270005367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26392211195493637693340489 19794158396620228270005367)
              ·
                refine ⟨29691237594930342405008051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19794158396620228270005367 29691237594930342405008051)
                ·
                  refine ⟨44536856392395513607512077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29691237594930342405008051 44536856392395513607512077)
                  ·
                    refine ⟨16701321147148317602817029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44536856392395513607512077 16701321147148317602817029)
                    ·
                      refine ⟨3131497715090309550528193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16701321147148317602817029 3131497715090309550528193)
                      ·
                        rfl

theorem cell23_6098570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_6098570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098570 prefixEnd_6098570 := by exact prefixLift 6098570
  have htrace : WordTrace (prefixWord ++ tailWord_6098570) baseStart_6098570 baseEnd_6098570 := by
    simpa [prefixWord, tailWord_6098570, baseEnd_6098570] using wordTrace_append hprefix tailTrace_6098570
  have hstable : (prefixWord ++ tailWord_6098570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098570).length < 2 ^ (prefixWord ++ tailWord_6098570).sum := by decide
  have hdescent : baseEnd_6098570 < baseStart_6098570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098597 : List Nat := [1, 3, 1, 2, 1, 2, 2, 6, 1, 4]
def baseStart_6098597 : Nat := 118140960795 + 6098597 * 2 ^ 59
def prefixEnd_6098597 : Nat := 4983230072969 + 3 ^ 40 * 6098597 * 2
def baseEnd_6098597 : Nat := 1043837193022660314963523

theorem tailTrace_6098597 : CollatzResearch.WordTrace tailWord_6098597 prefixEnd_6098597 1043837193022660314963523 := by
  unfold tailWord_6098597
  simp only [CollatzResearch.WordTrace]
  refine ⟨222434106286832101290086045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148289404191221400860057363 222434106286832101290086045)
  ·
    refine ⟨83412789857562037983782267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222434106286832101290086045 83412789857562037983782267)
    ·
      refine ⟨125119184786343056975673401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83412789857562037983782267 125119184786343056975673401)
      ·
        refine ⟨93839388589757292731755051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125119184786343056975673401 93839388589757292731755051)
        ·
          refine ⟨140759082884635939097632577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93839388589757292731755051 140759082884635939097632577)
          ·
            refine ⟨105569312163476954323224433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140759082884635939097632577 105569312163476954323224433)
            ·
              refine ⟨79176984122607715742418325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105569312163476954323224433 79176984122607715742418325)
              ·
                refine ⟨3711421130747236675425859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79176984122607715742418325 3711421130747236675425859)
                ·
                  refine ⟨5567131696120855013138789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3711421130747236675425859 5567131696120855013138789)
                  ·
                    refine ⟨1043837193022660314963523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5567131696120855013138789 1043837193022660314963523)
                    ·
                      rfl

theorem cell23_6098597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 1, 4].length) (baseStart_6098597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098597 prefixEnd_6098597 := by exact prefixLift 6098597
  have htrace : WordTrace (prefixWord ++ tailWord_6098597) baseStart_6098597 baseEnd_6098597 := by
    simpa [prefixWord, tailWord_6098597, baseEnd_6098597] using wordTrace_append hprefix tailTrace_6098597
  have hstable : (prefixWord ++ tailWord_6098597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098597).length < 2 ^ (prefixWord ++ tailWord_6098597).sum := by decide
  have hdescent : baseEnd_6098597 < baseStart_6098597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098643 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 4]
def baseStart_6098643 : Nat := 118140960795 + 6098643 * 2 ^ 59
def prefixEnd_6098643 : Nat := 4983230072969 + 3 ^ 40 * 6098643 * 2
def baseEnd_6098643 : Nat := 3131535199178087764915357

theorem tailTrace_6098643 : CollatzResearch.WordTrace tailWord_6098643 prefixEnd_6098643 3131535199178087764915357 := by
  unfold tailWord_6098643
  simp only [CollatzResearch.WordTrace]
  refine ⟨222435784044665451146260583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148290522696443634097507055 222435784044665451146260583)
  ·
    refine ⟨333653676066998176719390875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222435784044665451146260583 333653676066998176719390875)
    ·
      refine ⟨500480514100497265079086313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333653676066998176719390875 500480514100497265079086313)
      ·
        refine ⟨375360385575372948809314735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 500480514100497265079086313 375360385575372948809314735)
        ·
          refine ⟨563040578363059423213972103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375360385575372948809314735 563040578363059423213972103)
          ·
            refine ⟨844560867544589134820958155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563040578363059423213972103 844560867544589134820958155)
            ·
              refine ⟨1266841301316883702231437233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 844560867544589134820958155 1266841301316883702231437233)
              ·
                refine ⟨950130975987662776673577925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1266841301316883702231437233 950130975987662776673577925)
                ·
                  refine ⟨178149557997686770626295861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 950130975987662776673577925 178149557997686770626295861)
                  ·
                    refine ⟨16701521062283134746215237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 178149557997686770626295861 16701521062283134746215237)
                    ·
                      refine ⟨3131535199178087764915357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16701521062283134746215237 3131535199178087764915357)
                      ·
                        rfl

theorem cell23_6098643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 4].length) (baseStart_6098643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098643 prefixEnd_6098643 := by exact prefixLift 6098643
  have htrace : WordTrace (prefixWord ++ tailWord_6098643) baseStart_6098643 baseEnd_6098643 := by
    simpa [prefixWord, tailWord_6098643, baseEnd_6098643] using wordTrace_append hprefix tailTrace_6098643
  have hstable : (prefixWord ++ tailWord_6098643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098643).length < 2 ^ (prefixWord ++ tailWord_6098643).sum := by decide
  have hdescent : baseEnd_6098643 < baseStart_6098643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098647 : List Nat := [1, 1, 3, 2, 1, 3, 1, 4, 2, 3, 2]
def baseStart_6098647 : Nat := 118140960795 + 6098647 * 2 ^ 59
def prefixEnd_6098647 : Nat := 4983230072969 + 3 ^ 40 * 6098647 * 2
def baseEnd_6098647 : Nat := 3131537253100705749265339

theorem tailTrace_6098647 : CollatzResearch.WordTrace tailWord_6098647 prefixEnd_6098647 3131537253100705749265339 := by
  unfold tailWord_6098647
  simp only [CollatzResearch.WordTrace]
  refine ⟨222435929936650959829406195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148290619957767306552937463 222435929936650959829406195)
  ·
    refine ⟨333653894904976439744109293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222435929936650959829406195 333653894904976439744109293)
    ·
      refine ⟨125120210589366164904040985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333653894904976439744109293 125120210589366164904040985)
      ·
        refine ⟨93840157942024623678030739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125120210589366164904040985 93840157942024623678030739)
        ·
          refine ⟨140760236913036935517046109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93840157942024623678030739 140760236913036935517046109)
          ·
            refine ⟨52785088842388850818892291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140760236913036935517046109 52785088842388850818892291)
            ·
              refine ⟨79177633263583276228338437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52785088842388850818892291 79177633263583276228338437)
              ·
                refine ⟨14845806236921864292813457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79177633263583276228338437 14845806236921864292813457)
                ·
                  refine ⟨11134354677691398219610093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14845806236921864292813457 11134354677691398219610093)
                  ·
                    refine ⟨4175383004134274332353785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11134354677691398219610093 4175383004134274332353785)
                    ·
                      refine ⟨3131537253100705749265339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4175383004134274332353785 3131537253100705749265339)
                      ·
                        rfl

theorem cell23_6098647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 3, 2].length) (baseStart_6098647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098647 prefixEnd_6098647 := by exact prefixLift 6098647
  have htrace : WordTrace (prefixWord ++ tailWord_6098647) baseStart_6098647 baseEnd_6098647 := by
    simpa [prefixWord, tailWord_6098647, baseEnd_6098647] using wordTrace_append hprefix tailTrace_6098647
  have hstable : (prefixWord ++ tailWord_6098647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098647).length < 2 ^ (prefixWord ++ tailWord_6098647).sum := by decide
  have hdescent : baseEnd_6098647 < baseStart_6098647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098660 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 5, 1, 4]
def baseStart_6098660 : Nat := 118140960795 + 6098660 * 2 ^ 59
def prefixEnd_6098660 : Nat := 4983230072969 + 3 ^ 40 * 6098660 * 2
def baseEnd_6098660 : Nat := 3131543928349214198402779

theorem tailTrace_6098660 : CollatzResearch.WordTrace tailWord_6098660 prefixEnd_6098660 3131543928349214198402779 := by
  unfold tailWord_6098660
  simp only [CollatzResearch.WordTrace]
  refine ⟨111218202042801931524814717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148290936057069242033086289 111218202042801931524814717)
  ·
    refine ⟨41706825766050724321805519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111218202042801931524814717 41706825766050724321805519)
    ·
      refine ⟨62560238649076086482708279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41706825766050724321805519 62560238649076086482708279)
      ·
        refine ⟨93840357973614129724062419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62560238649076086482708279 93840357973614129724062419)
        ·
          refine ⟨140760536960421194586093629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93840357973614129724062419 140760536960421194586093629)
          ·
            refine ⟨52785201360157947969785111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140760536960421194586093629 52785201360157947969785111)
            ·
              refine ⟨79177802040236921954677667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52785201360157947969785111 79177802040236921954677667)
              ·
                refine ⟨118766703060355382932016501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79177802040236921954677667 118766703060355382932016501)
                ·
                  refine ⟨11134378411908317149876547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118766703060355382932016501 11134378411908317149876547)
                  ·
                    refine ⟨16701567617862475724814821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11134378411908317149876547 16701567617862475724814821)
                    ·
                      refine ⟨3131543928349214198402779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16701567617862475724814821 3131543928349214198402779)
                      ·
                        rfl

theorem cell23_6098660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_6098660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098660 prefixEnd_6098660 := by exact prefixLift 6098660
  have htrace : WordTrace (prefixWord ++ tailWord_6098660) baseStart_6098660 baseEnd_6098660 := by
    simpa [prefixWord, tailWord_6098660, baseEnd_6098660] using wordTrace_append hprefix tailTrace_6098660
  have hstable : (prefixWord ++ tailWord_6098660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098660).length < 2 ^ (prefixWord ++ tailWord_6098660).sum := by decide
  have hdescent : baseEnd_6098660 < baseStart_6098660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098711 : List Nat := [1, 1, 3, 4, 2, 2, 2, 1, 3, 2, 2]
def baseStart_6098711 : Nat := 118140960795 + 6098711 * 2 ^ 59
def prefixEnd_6098711 : Nat := 4983230072969 + 3 ^ 40 * 6098711 * 2
def baseEnd_6098711 : Nat := 3131570115862593498865045

theorem tailTrace_6098711 : CollatzResearch.WordTrace tailWord_6098711 prefixEnd_6098711 3131570115862593498865045 := by
  unfold tailWord_6098711
  simp only [CollatzResearch.WordTrace]
  refine ⟨222438264208419098759735987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148292176138946065839823991 222438264208419098759735987)
  ·
    refine ⟨333657396312628648139603981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222438264208419098759735987 333657396312628648139603981)
    ·
      refine ⟨125121523617235743052351493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333657396312628648139603981 125121523617235743052351493)
      ·
        refine ⟨23460285678231701822315905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125121523617235743052351493 23460285678231701822315905)
        ·
          refine ⟨17595214258673776366736929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23460285678231701822315905 17595214258673776366736929)
          ·
            refine ⟨13196410694005332275052697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17595214258673776366736929 13196410694005332275052697)
            ·
              refine ⟨9897308020503999206289523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13196410694005332275052697 9897308020503999206289523)
              ·
                refine ⟨14845962030755998809434285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9897308020503999206289523 14845962030755998809434285)
                ·
                  refine ⟨5567235761533499553537857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14845962030755998809434285 5567235761533499553537857)
                  ·
                    refine ⟨4175426821150124665153393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5567235761533499553537857 4175426821150124665153393)
                    ·
                      refine ⟨3131570115862593498865045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4175426821150124665153393 3131570115862593498865045)
                      ·
                        rfl

theorem cell23_6098711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_6098711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098711 prefixEnd_6098711 := by exact prefixLift 6098711
  have htrace : WordTrace (prefixWord ++ tailWord_6098711) baseStart_6098711 baseEnd_6098711 := by
    simpa [prefixWord, tailWord_6098711, baseEnd_6098711] using wordTrace_append hprefix tailTrace_6098711
  have hstable : (prefixWord ++ tailWord_6098711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098711).length < 2 ^ (prefixWord ++ tailWord_6098711).sum := by decide
  have hdescent : baseEnd_6098711 < baseStart_6098711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098724 : List Nat := [2, 3, 1, 3, 2, 3, 1, 1, 1, 2, 4]
def baseStart_6098724 : Nat := 118140960795 + 6098724 * 2 ^ 59
def prefixEnd_6098724 : Nat := 4983230072969 + 3 ^ 40 * 6098724 * 2
def baseEnd_6098724 : Nat := 3131576791111101948002485

theorem tailTrace_6098724 : CollatzResearch.WordTrace tailWord_6098724 prefixEnd_6098724 3131576791111101948002485 := by
  unfold tailWord_6098724
  simp only [CollatzResearch.WordTrace]
  refine ⟨111219369178686000989979613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148292492238248001319972817 111219369178686000989979613)
  ·
    refine ⟨41707263442007250371242355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111219369178686000989979613 41707263442007250371242355)
    ·
      refine ⟨62560895163010875556863533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41707263442007250371242355 62560895163010875556863533)
      ·
        refine ⟨23460335686129078333823825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62560895163010875556863533 23460335686129078333823825)
        ·
          refine ⟨17595251764596808750367869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23460335686129078333823825 17595251764596808750367869)
          ·
            refine ⟨6598219411723803281387951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17595251764596808750367869 6598219411723803281387951)
            ·
              refine ⟨9897329117585704922081927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6598219411723803281387951 9897329117585704922081927)
              ·
                refine ⟨14845993676378557383122891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9897329117585704922081927 14845993676378557383122891)
                ·
                  refine ⟨22268990514567836074684337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14845993676378557383122891 22268990514567836074684337)
                  ·
                    refine ⟨16701742885925877056013253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22268990514567836074684337 16701742885925877056013253)
                    ·
                      refine ⟨3131576791111101948002485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16701742885925877056013253 3131576791111101948002485)
                      ·
                        rfl

theorem cell23_6098724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_6098724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098724 prefixEnd_6098724 := by exact prefixLift 6098724
  have htrace : WordTrace (prefixWord ++ tailWord_6098724) baseStart_6098724 baseEnd_6098724 := by
    simpa [prefixWord, tailWord_6098724, baseEnd_6098724] using wordTrace_append hprefix tailTrace_6098724
  have hstable : (prefixWord ++ tailWord_6098724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098724).length < 2 ^ (prefixWord ++ tailWord_6098724).sum := by decide
  have hdescent : baseEnd_6098724 < baseStart_6098724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098788 : List Nat := [2, 3, 1, 1, 5, 2, 1, 2, 1, 3, 2]
def baseStart_6098788 : Nat := 118140960795 + 6098788 * 2 ^ 59
def prefixEnd_6098788 : Nat := 4983230072969 + 3 ^ 40 * 6098788 * 2
def baseEnd_6098788 : Nat := 3131609653872989697602191

theorem tailTrace_6098788 : CollatzResearch.WordTrace tailWord_6098788 prefixEnd_6098788 3131609653872989697602191 := by
  unfold tailWord_6098788
  simp only [CollatzResearch.WordTrace]
  refine ⟨111220536314570070455144509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148294048419426760606859345 111220536314570070455144509)
  ·
    refine ⟨41707701117963776420679191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111220536314570070455144509 41707701117963776420679191)
    ·
      refine ⟨62561551676945664631018787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41707701117963776420679191 62561551676945664631018787)
      ·
        refine ⟨93842327515418496946528181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62561551676945664631018787 93842327515418496946528181)
        ·
          refine ⟨8797718204570484088737017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93842327515418496946528181 8797718204570484088737017)
          ·
            refine ⟨6598288653427863066552763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8797718204570484088737017 6598288653427863066552763)
            ·
              refine ⟨9897432980141794599829145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6598288653427863066552763 9897432980141794599829145)
              ·
                refine ⟨7423074735106345949871859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9897432980141794599829145 7423074735106345949871859)
                ·
                  refine ⟨11134612102659518924807789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7423074735106345949871859 11134612102659518924807789)
                  ·
                    refine ⟨4175479538497319596802921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11134612102659518924807789 4175479538497319596802921)
                    ·
                      refine ⟨3131609653872989697602191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4175479538497319596802921 3131609653872989697602191)
                      ·
                        rfl

theorem cell23_6098788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 1, 3, 2].length) (baseStart_6098788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098788 prefixEnd_6098788 := by exact prefixLift 6098788
  have htrace : WordTrace (prefixWord ++ tailWord_6098788) baseStart_6098788 baseEnd_6098788 := by
    simpa [prefixWord, tailWord_6098788, baseEnd_6098788] using wordTrace_append hprefix tailTrace_6098788
  have hstable : (prefixWord ++ tailWord_6098788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098788).length < 2 ^ (prefixWord ++ tailWord_6098788).sum := by decide
  have hdescent : baseEnd_6098788 < baseStart_6098788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098834 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_6098834 : Nat := 118140960795 + 6098834 * 2 ^ 59
def prefixEnd_6098834 : Nat := 4983230072969 + 3 ^ 40 * 6098834 * 2
def baseEnd_6098834 : Nat := 3131633273983096517626979

theorem tailTrace_6098834 : CollatzResearch.WordTrace tailWord_6098834 prefixEnd_6098834 3131633273983096517626979 := by
  unfold tailWord_6098834
  simp only [CollatzResearch.WordTrace]
  refine ⟨55610687596743372691615889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148295166924648993844309037 55610687596743372691615889)
  ·
    refine ⟨41708015697557529518711917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55610687596743372691615889 41708015697557529518711917)
    ·
      refine ⟨15640505886584073569516969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41708015697557529518711917 15640505886584073569516969)
      ·
        refine ⟨11730379414938055177137727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15640505886584073569516969 11730379414938055177137727)
        ·
          refine ⟨17595569122407082765706591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11730379414938055177137727 17595569122407082765706591)
          ·
            refine ⟨26393353683610624148559887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17595569122407082765706591 26393353683610624148559887)
            ·
              refine ⟨39590030525415936222839831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26393353683610624148559887 39590030525415936222839831)
              ·
                refine ⟨59385045788123904334259747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39590030525415936222839831 59385045788123904334259747)
                ·
                  refine ⟨89077568682185856501389621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59385045788123904334259747 89077568682185856501389621)
                  ·
                    refine ⟨8351022063954924047005277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89077568682185856501389621 8351022063954924047005277)
                    ·
                      refine ⟨3131633273983096517626979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8351022063954924047005277 3131633273983096517626979)
                      ·
                        rfl

theorem cell23_6098834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_6098834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098834 prefixEnd_6098834 := by exact prefixLift 6098834
  have htrace : WordTrace (prefixWord ++ tailWord_6098834) baseStart_6098834 baseEnd_6098834 := by
    simpa [prefixWord, tailWord_6098834, baseEnd_6098834] using wordTrace_append hprefix tailTrace_6098834
  have hstable : (prefixWord ++ tailWord_6098834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098834).length < 2 ^ (prefixWord ++ tailWord_6098834).sum := by decide
  have hdescent : baseEnd_6098834 < baseStart_6098834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098857 : List Nat := [1, 2, 1, 1, 1, 1, 4, 5, 2, 1, 4]
def baseStart_6098857 : Nat := 118140960795 + 6098857 * 2 ^ 59
def prefixEnd_6098857 : Nat := 4983230072969 + 3 ^ 40 * 6098857 * 2
def baseEnd_6098857 : Nat := 3131645084038149927639373

theorem tailTrace_6098857 : CollatzResearch.WordTrace tailWord_6098857 prefixEnd_6098857 3131645084038149927639373 := by
  unfold tailWord_6098857
  simp only [CollatzResearch.WordTrace]
  refine ⟨222443589265890165694550825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148295726177260110463033883 222443589265890165694550825)
  ·
    refine ⟨166832691949417624270913119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222443589265890165694550825 166832691949417624270913119)
    ·
      refine ⟨250249037924126436406369679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166832691949417624270913119 250249037924126436406369679)
      ·
        refine ⟨375373556886189654609554519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250249037924126436406369679 375373556886189654609554519)
        ·
          refine ⟨563060335329284481914331779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375373556886189654609554519 563060335329284481914331779)
          ·
            refine ⟨844590502993926722871497669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563060335329284481914331779 844590502993926722871497669)
            ·
              refine ⟨158360719311361260538405813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 844590502993926722871497669 158360719311361260538405813)
              ·
                refine ⟨14846317435440118175475545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 158360719311361260538405813 14846317435440118175475545)
                ·
                  refine ⟨11134738076580088631606659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14846317435440118175475545 11134738076580088631606659)
                  ·
                    refine ⟨16702107114870132947409989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11134738076580088631606659 16702107114870132947409989)
                    ·
                      refine ⟨3131645084038149927639373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16702107114870132947409989 3131645084038149927639373)
                      ·
                        rfl

theorem cell23_6098857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 1, 4].length) (baseStart_6098857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098857 prefixEnd_6098857 := by exact prefixLift 6098857
  have htrace : WordTrace (prefixWord ++ tailWord_6098857) baseStart_6098857 baseEnd_6098857 := by
    simpa [prefixWord, tailWord_6098857, baseEnd_6098857] using wordTrace_append hprefix tailTrace_6098857
  have hstable : (prefixWord ++ tailWord_6098857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098857).length < 2 ^ (prefixWord ++ tailWord_6098857).sum := by decide
  have hdescent : baseEnd_6098857 < baseStart_6098857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098860 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 9]
def baseStart_6098860 : Nat := 118140960795 + 6098860 * 2 ^ 59
def prefixEnd_6098860 : Nat := 4983230072969 + 3 ^ 40 * 6098860 * 2
def baseEnd_6098860 : Nat := 3131646624480113415901859

theorem tailTrace_6098860 : CollatzResearch.WordTrace tailWord_6098860 prefixEnd_6098860 3131646624480113415901859 := by
  unfold tailWord_6098860
  simp only [CollatzResearch.WordTrace]
  refine ⟨111221849342439648603455017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148295799123252864804606689 111221849342439648603455017)
  ·
    refine ⟨83416387006829736452591263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111221849342439648603455017 83416387006829736452591263)
    ·
      refine ⟨125124580510244604678886895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83416387006829736452591263 125124580510244604678886895)
      ·
        refine ⟨187686870765366907018330343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125124580510244604678886895 187686870765366907018330343)
        ·
          refine ⟨281530306148050360527495515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187686870765366907018330343 281530306148050360527495515)
          ·
            refine ⟨422295459222075540791243273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281530306148050360527495515 422295459222075540791243273)
            ·
              refine ⟨316721594416556655593432455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 422295459222075540791243273 316721594416556655593432455)
              ·
                refine ⟨475082391624834983390148683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316721594416556655593432455 475082391624834983390148683)
                ·
                  refine ⟨712623587437252475085223025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 475082391624834983390148683 712623587437252475085223025)
                  ·
                    refine ⟨534467690577939356313917269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 712623587437252475085223025 534467690577939356313917269)
                    ·
                      refine ⟨3131646624480113415901859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 534467690577939356313917269 3131646624480113415901859)
                      ·
                        rfl

theorem cell23_6098860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_6098860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098860 prefixEnd_6098860 := by exact prefixLift 6098860
  have htrace : WordTrace (prefixWord ++ tailWord_6098860) baseStart_6098860 baseEnd_6098860 := by
    simpa [prefixWord, tailWord_6098860, baseEnd_6098860] using wordTrace_append hprefix tailTrace_6098860
  have hstable : (prefixWord ++ tailWord_6098860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098860).length < 2 ^ (prefixWord ++ tailWord_6098860).sum := by decide
  have hdescent : baseEnd_6098860 < baseStart_6098860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098867 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 5, 4]
def baseStart_6098867 : Nat := 118140960795 + 6098867 * 2 ^ 59
def prefixEnd_6098867 : Nat := 4983230072969 + 3 ^ 40 * 6098867 * 2
def baseEnd_6098867 : Nat := 1043883406281564962838109

theorem tailTrace_6098867 : CollatzResearch.WordTrace tailWord_6098867 prefixEnd_6098867 1043883406281564962838109 := by
  unfold tailWord_6098867
  simp only [CollatzResearch.WordTrace]
  refine ⟨222443953995853937402414855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148295969330569291601609903 222443953995853937402414855)
  ·
    refine ⟨333665930993780906103622283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222443953995853937402414855 333665930993780906103622283)
    ·
      refine ⟨500498896490671359155433425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333665930993780906103622283 500498896490671359155433425)
      ·
        refine ⟨375374172368003519366575069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 500498896490671359155433425 375374172368003519366575069)
        ·
          refine ⟨140765314638001319762465651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 375374172368003519366575069 140765314638001319762465651)
          ·
            refine ⟨211147971957001979643698477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140765314638001319762465651 211147971957001979643698477)
            ·
              refine ⟨79180489483875742366386929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211147971957001979643698477 79180489483875742366386929)
              ·
                refine ⟨59385367112906806774790197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79180489483875742366386929 59385367112906806774790197)
                ·
                  refine ⟨5567378166835013135136581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59385367112906806774790197 5567378166835013135136581)
                  ·
                    refine ⟨1043883406281564962838109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5567378166835013135136581 1043883406281564962838109)
                    ·
                      rfl

theorem cell23_6098867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 4].length) (baseStart_6098867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098867 prefixEnd_6098867 := by exact prefixLift 6098867
  have htrace : WordTrace (prefixWord ++ tailWord_6098867) baseStart_6098867 baseEnd_6098867 := by
    simpa [prefixWord, tailWord_6098867, baseEnd_6098867] using wordTrace_append hprefix tailTrace_6098867
  have hstable : (prefixWord ++ tailWord_6098867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098867).length < 2 ^ (prefixWord ++ tailWord_6098867).sum := by decide
  have hdescent : baseEnd_6098867 < baseStart_6098867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098924 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 3]
def baseStart_6098924 : Nat := 118140960795 + 6098924 * 2 ^ 59
def prefixEnd_6098924 : Nat := 4983230072969 + 3 ^ 40 * 6098924 * 2
def baseEnd_6098924 : Nat := 3131679487242001165501565

theorem tailTrace_6098924 : CollatzResearch.WordTrace tailWord_6098924 prefixEnd_6098924 3131679487242001165501565 := by
  unfold tailWord_6098924
  simp only [CollatzResearch.WordTrace]
  refine ⟨111223016478323718068619913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148297355304431624091493217 111223016478323718068619913)
  ·
    refine ⟨83417262358742788551464935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111223016478323718068619913 83417262358742788551464935)
    ·
      refine ⟨125125893538114182827197403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83417262358742788551464935 125125893538114182827197403)
      ·
        refine ⟨187688840307171274240796105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125125893538114182827197403 187688840307171274240796105)
        ·
          refine ⟨140766630230378455680597079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187688840307171274240796105 140766630230378455680597079)
          ·
            refine ⟨211149945345567683520895619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140766630230378455680597079 211149945345567683520895619)
            ·
              refine ⟨316724918018351525281343429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211149945345567683520895619 316724918018351525281343429)
              ·
                refine ⟨59385922128440910990251893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 316724918018351525281343429 59385922128440910990251893)
                ·
                  refine ⟨5567430199541335405336115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59385922128440910990251893 5567430199541335405336115)
                  ·
                    refine ⟨8351145299312003108004173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5567430199541335405336115 8351145299312003108004173)
                    ·
                      refine ⟨3131679487242001165501565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8351145299312003108004173 3131679487242001165501565)
                      ·
                        rfl

theorem cell23_6098924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 3].length) (baseStart_6098924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098924 prefixEnd_6098924 := by exact prefixLift 6098924
  have htrace : WordTrace (prefixWord ++ tailWord_6098924) baseStart_6098924 baseEnd_6098924 := by
    simpa [prefixWord, tailWord_6098924, baseEnd_6098924] using wordTrace_append hprefix tailTrace_6098924
  have hstable : (prefixWord ++ tailWord_6098924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098924).length < 2 ^ (prefixWord ++ tailWord_6098924).sum := by decide
  have hdescent : baseEnd_6098924 < baseStart_6098924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6098941 : List Nat := [1, 4, 1, 1, 1, 2, 5, 1, 3, 1, 3]
def baseStart_6098941 : Nat := 118140960795 + 6098941 * 2 ^ 59
def prefixEnd_6098941 : Nat := 4983230072969 + 3 ^ 40 * 6098941 * 2
def baseEnd_6098941 : Nat := 3131688216413127598988987

theorem tailTrace_6098941 : CollatzResearch.WordTrace tailWord_6098941 prefixEnd_6098941 3131688216413127598988987 := by
  unfold tailWord_6098941
  simp only [CollatzResearch.WordTrace]
  refine ⟨222446652997585848040608677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148297768665057232027072451 222446652997585848040608677)
  ·
    refine ⟨41708747437047346507614127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222446652997585848040608677 41708747437047346507614127)
    ·
      refine ⟨62563121155571019761421191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41708747437047346507614127 62563121155571019761421191)
      ·
        refine ⟨93844681733356529642131787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62563121155571019761421191 93844681733356529642131787)
        ·
          refine ⟨140767022600034794463197681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93844681733356529642131787 140767022600034794463197681)
          ·
            refine ⟨105575266950026095847398261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140767022600034794463197681 105575266950026095847398261)
            ·
              refine ⟨9897681276564946485693587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105575266950026095847398261 9897681276564946485693587)
              ·
                refine ⟨14846521914847419728540381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9897681276564946485693587 14846521914847419728540381)
                ·
                  refine ⟨5567445718067782398202643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14846521914847419728540381 5567445718067782398202643)
                  ·
                    refine ⟨8351168577101673597303965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5567445718067782398202643 8351168577101673597303965)
                    ·
                      refine ⟨3131688216413127598988987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8351168577101673597303965 3131688216413127598988987)
                      ·
                        rfl

theorem cell23_6098941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_6098941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6098941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6098941 prefixEnd_6098941 := by exact prefixLift 6098941
  have htrace : WordTrace (prefixWord ++ tailWord_6098941) baseStart_6098941 baseEnd_6098941 := by
    simpa [prefixWord, tailWord_6098941, baseEnd_6098941] using wordTrace_append hprefix tailTrace_6098941
  have hstable : (prefixWord ++ tailWord_6098941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6098941).length < 2 ^ (prefixWord ++ tailWord_6098941).sum := by decide
  have hdescent : baseEnd_6098941 < baseStart_6098941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6098941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099007 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 6]
def baseStart_6099007 : Nat := 118140960795 + 6099007 * 2 ^ 59
def prefixEnd_6099007 : Nat := 4983230072969 + 3 ^ 40 * 6099007 * 2
def baseEnd_6099007 : Nat := 3131722106136324340763683

theorem tailTrace_6099007 : CollatzResearch.WordTrace tailWord_6099007 prefixEnd_6099007 3131722106136324340763683 := by
  unfold tailWord_6099007
  simp only [CollatzResearch.WordTrace]
  refine ⟨222449060215346741312511275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148299373476897827541674183 222449060215346741312511275)
  ·
    refine ⟨333673590323020111968766913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222449060215346741312511275 333673590323020111968766913)
    ·
      refine ⟨250255192742265083976575185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333673590323020111968766913 250255192742265083976575185)
      ·
        refine ⟨187691394556698812982431389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250255192742265083976575185 187691394556698812982431389)
        ·
          refine ⟨70384272958762054868411771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187691394556698812982431389 70384272958762054868411771)
          ·
            refine ⟨105576409438143082302617657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70384272958762054868411771 105576409438143082302617657)
            ·
              refine ⟨79182307078607311726963243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105576409438143082302617657 79182307078607311726963243)
              ·
                refine ⟨118773460617910967590444865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79182307078607311726963243 118773460617910967590444865)
                ·
                  refine ⟨89080095463433225692833649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118773460617910967590444865 89080095463433225692833649)
                  ·
                    refine ⟨66810071597574919269625237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89080095463433225692833649 66810071597574919269625237)
                    ·
                      refine ⟨3131722106136324340763683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66810071597574919269625237 3131722106136324340763683)
                      ·
                        rfl

theorem cell23_6099007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_6099007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099007 prefixEnd_6099007 := by exact prefixLift 6099007
  have htrace : WordTrace (prefixWord ++ tailWord_6099007) baseStart_6099007 baseEnd_6099007 := by
    simpa [prefixWord, tailWord_6099007, baseEnd_6099007] using wordTrace_append hprefix tailTrace_6099007
  have hstable : (prefixWord ++ tailWord_6099007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099007).length < 2 ^ (prefixWord ++ tailWord_6099007).sum := by decide
  have hdescent : baseEnd_6099007 < baseStart_6099007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099017 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 2, 7]
def baseStart_6099017 : Nat := 118140960795 + 6099017 * 2 ^ 59
def prefixEnd_6099017 : Nat := 4983230072969 + 3 ^ 40 * 6099017 * 2
def baseEnd_6099017 : Nat := 1043909080314289767212879

theorem tailTrace_6099017 : CollatzResearch.WordTrace tailWord_6099017 prefixEnd_6099017 1043909080314289767212879 := by
  unfold tailWord_6099017
  simp only [CollatzResearch.WordTrace]
  refine ⟨222449424945310513020375305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148299616630207008680250203 222449424945310513020375305)
  ·
    refine ⟨166837068708982884765281479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222449424945310513020375305 166837068708982884765281479)
    ·
      refine ⟨250255603063474327147922219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166837068708982884765281479 250255603063474327147922219)
      ·
        refine ⟨375383404595211490721883329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250255603063474327147922219 375383404595211490721883329)
        ·
          refine ⟨281537553446408618041412497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375383404595211490721883329 281537553446408618041412497)
          ·
            refine ⟨211153165084806463531059373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281537553446408618041412497 211153165084806463531059373)
            ·
              refine ⟨79182436906802423824147265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211153165084806463531059373 79182436906802423824147265)
              ·
                refine ⟨59386827680101817868110449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79182436906802423824147265 59386827680101817868110449)
                ·
                  refine ⟨44540120760076363401082837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59386827680101817868110449 44540120760076363401082837)
                  ·
                    refine ⟨1043909080314289767212879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44540120760076363401082837 1043909080314289767212879)
                    ·
                      rfl

theorem cell23_6099017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 7].length) (baseStart_6099017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099017 prefixEnd_6099017 := by exact prefixLift 6099017
  have htrace : WordTrace (prefixWord ++ tailWord_6099017) baseStart_6099017 baseEnd_6099017 := by
    simpa [prefixWord, tailWord_6099017, baseEnd_6099017] using wordTrace_append hprefix tailTrace_6099017
  have hstable : (prefixWord ++ tailWord_6099017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099017).length < 2 ^ (prefixWord ++ tailWord_6099017).sum := by decide
  have hdescent : baseEnd_6099017 < baseStart_6099017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099021 : List Nat := [1, 6, 1, 1, 1, 1, 5, 7]
def baseStart_6099021 : Nat := 118140960795 + 6099021 * 2 ^ 59
def prefixEnd_6099021 : Nat := 4983230072969 + 3 ^ 40 * 6099021 * 2
def baseEnd_6099021 : Nat := 115989973883906936518097

theorem tailTrace_6099021 : CollatzResearch.WordTrace tailWord_6099021 prefixEnd_6099021 115989973883906936518097 := by
  unfold tailWord_6099021
  simp only [CollatzResearch.WordTrace]
  refine ⟨222449570837296021703520917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148299713891530681135680611 222449570837296021703520917)
  ·
    refine ⟨10427323632998251017352543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 222449570837296021703520917 10427323632998251017352543)
    ·
      refine ⟨15640985449497376526028815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10427323632998251017352543 15640985449497376526028815)
      ·
        refine ⟨23461478174246064789043223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15640985449497376526028815 23461478174246064789043223)
        ·
          refine ⟨35192217261369097183564835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23461478174246064789043223 35192217261369097183564835)
          ·
            refine ⟨52788325892053645775347253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35192217261369097183564835 52788325892053645775347253)
            ·
              refine ⟨4948905552380029291438805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52788325892053645775347253 4948905552380029291438805)
              ·
                refine ⟨115989973883906936518097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4948905552380029291438805 115989973883906936518097)
                ·
                  rfl

theorem cell23_6099021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 7].length) (baseStart_6099021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099021 prefixEnd_6099021 := by exact prefixLift 6099021
  have htrace : WordTrace (prefixWord ++ tailWord_6099021) baseStart_6099021 baseEnd_6099021 := by
    simpa [prefixWord, tailWord_6099021, baseEnd_6099021] using wordTrace_append hprefix tailTrace_6099021
  have hstable : (prefixWord ++ tailWord_6099021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099021).length < 2 ^ (prefixWord ++ tailWord_6099021).sum := by decide
  have hdescent : baseEnd_6099021 < baseStart_6099021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099038 : List Nat := [4, 4, 1, 1, 2, 1, 10]
def baseStart_6099038 : Nat := 118140960795 + 6099038 * 2 ^ 59
def prefixEnd_6099038 : Nat := 4983230072969 + 3 ^ 40 * 6099038 * 2
def baseEnd_6099038 : Nat := 38663432395513749623161

theorem tailTrace_6099038 : CollatzResearch.WordTrace tailWord_6099038 prefixEnd_6099038 38663432395513749623161 := by
  unfold tailWord_6099038
  simp only [CollatzResearch.WordTrace]
  refine ⟨27806273859779304200861221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148300127252156289071259845 27806273859779304200861221)
  ·
    refine ⟨5213676348708619537661479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27806273859779304200861221 5213676348708619537661479)
    ·
      refine ⟨7820514523062929306492219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5213676348708619537661479 7820514523062929306492219)
      ·
        refine ⟨11730771784594393959738329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7820514523062929306492219 11730771784594393959738329)
        ·
          refine ⟨8798078838445795469803747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11730771784594393959738329 8798078838445795469803747)
          ·
            refine ⟨13197118257668693204705621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8798078838445795469803747 13197118257668693204705621)
            ·
              refine ⟨38663432395513749623161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13197118257668693204705621 38663432395513749623161)
              ·
                rfl

theorem cell23_6099038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 10].length) (baseStart_6099038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099038 prefixEnd_6099038 := by exact prefixLift 6099038
  have htrace : WordTrace (prefixWord ++ tailWord_6099038) baseStart_6099038 baseEnd_6099038 := by
    simpa [prefixWord, tailWord_6099038, baseEnd_6099038] using wordTrace_append hprefix tailTrace_6099038
  have hstable : (prefixWord ++ tailWord_6099038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099038).length < 2 ^ (prefixWord ++ tailWord_6099038).sum := by decide
  have hdescent : baseEnd_6099038 < baseStart_6099038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099042 : List Nat := [3, 3, 2, 2, 3, 1, 1, 2, 2, 4]
def baseStart_6099042 : Nat := 118140960795 + 6099042 * 2 ^ 59
def prefixEnd_6099042 : Nat := 4983230072969 + 3 ^ 40 * 6099042 * 2
def baseEnd_6099042 : Nat := 1043913359319743901275341

theorem tailTrace_6099042 : CollatzResearch.WordTrace tailWord_6099042 prefixEnd_6099042 1043913359319743901275341 := by
  unfold tailWord_6099042
  simp only [CollatzResearch.WordTrace]
  refine ⟨55612584192554985572508845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148300224513479961526690253 55612584192554985572508845)
  ·
    refine ⟨20854719072208119589690817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55612584192554985572508845 20854719072208119589690817)
    ·
      refine ⟨15641039304156089692268113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20854719072208119589690817 15641039304156089692268113)
      ·
        refine ⟨11730779478117067269201085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15641039304156089692268113 11730779478117067269201085)
        ·
          refine ⟨4399042304293900225950407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11730779478117067269201085 4399042304293900225950407)
          ·
            refine ⟨6598563456440850338925611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4399042304293900225950407 6598563456440850338925611)
            ·
              refine ⟨9897845184661275508388417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6598563456440850338925611 9897845184661275508388417)
              ·
                refine ⟨7423383888495956631291313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9897845184661275508388417 7423383888495956631291313)
                ·
                  refine ⟨5567537916371967473468485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7423383888495956631291313 5567537916371967473468485)
                  ·
                    refine ⟨1043913359319743901275341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5567537916371967473468485 1043913359319743901275341)
                    ·
                      rfl

theorem cell23_6099042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_6099042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099042 prefixEnd_6099042 := by exact prefixLift 6099042
  have htrace : WordTrace (prefixWord ++ tailWord_6099042) baseStart_6099042 baseEnd_6099042 := by
    simpa [prefixWord, tailWord_6099042, baseEnd_6099042] using wordTrace_append hprefix tailTrace_6099042
  have hstable : (prefixWord ++ tailWord_6099042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099042).length < 2 ^ (prefixWord ++ tailWord_6099042).sum := by decide
  have hdescent : baseEnd_6099042 < baseStart_6099042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099065 : List Nat := [1, 2, 1, 3, 4, 2, 3, 1, 2, 1, 3]
def baseStart_6099065 : Nat := 118140960795 + 6099065 * 2 ^ 59
def prefixEnd_6099065 : Nat := 4983230072969 + 3 ^ 40 * 6099065 * 2
def baseEnd_6099065 : Nat := 3131751888014285113838417

theorem tailTrace_6099065 : CollatzResearch.WordTrace tailWord_6099065 prefixEnd_6099065 3131751888014285113838417 := by
  unfold tailWord_6099065
  simp only [CollatzResearch.WordTrace]
  refine ⟨222451175649136617218122649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148300783766091078145415099 222451175649136617218122649)
  ·
    refine ⟨166838381736852462913591987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222451175649136617218122649 166838381736852462913591987)
    ·
      refine ⟨250257572605278694370387981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166838381736852462913591987 250257572605278694370387981)
      ·
        refine ⟨93846589726979510388895493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250257572605278694370387981 93846589726979510388895493)
        ·
          refine ⟨17596235573808658197917905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93846589726979510388895493 17596235573808658197917905)
          ·
            refine ⟨13197176680356493648438429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17596235573808658197917905 13197176680356493648438429)
            ·
              refine ⟨4948941255133685118164411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13197176680356493648438429 4948941255133685118164411)
              ·
                refine ⟨7423411882700527677246617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4948941255133685118164411 7423411882700527677246617)
                ·
                  refine ⟨5567558912025395757934963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7423411882700527677246617 5567558912025395757934963)
                  ·
                    refine ⟨8351338368038093636902445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5567558912025395757934963 8351338368038093636902445)
                    ·
                      refine ⟨3131751888014285113838417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8351338368038093636902445 3131751888014285113838417)
                      ·
                        rfl

theorem cell23_6099065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 2, 1, 3].length) (baseStart_6099065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099065 prefixEnd_6099065 := by exact prefixLift 6099065
  have htrace : WordTrace (prefixWord ++ tailWord_6099065) baseStart_6099065 baseEnd_6099065 := by
    simpa [prefixWord, tailWord_6099065, baseEnd_6099065] using wordTrace_append hprefix tailTrace_6099065
  have hstable : (prefixWord ++ tailWord_6099065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099065).length < 2 ^ (prefixWord ++ tailWord_6099065).sum := by decide
  have hdescent : baseEnd_6099065 < baseStart_6099065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099161 : List Nat := [1, 2, 1, 2, 3, 1, 4, 2, 2, 1, 4]
def baseStart_6099161 : Nat := 118140960795 + 6099161 * 2 ^ 59
def prefixEnd_6099161 : Nat := 4983230072969 + 3 ^ 40 * 6099161 * 2
def baseEnd_6099161 : Nat := 3131801182157116738237975

theorem tailTrace_6099161 : CollatzResearch.WordTrace tailWord_6099161 prefixEnd_6099161 3131801182157116738237975 := by
  unfold tailWord_6099161
  simp only [CollatzResearch.WordTrace]
  refine ⟨222454677056788825613617337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148303118037859217075744891 222454677056788825613617337)
  ·
    refine ⟨166841007792591619210213003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222454677056788825613617337 166841007792591619210213003)
    ·
      refine ⟨250261511688887428815319505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166841007792591619210213003 250261511688887428815319505)
      ·
        refine ⟨187696133766665571611489629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250261511688887428815319505 187696133766665571611489629)
        ·
          refine ⟨70386050162499589354308611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187696133766665571611489629 70386050162499589354308611)
          ·
            refine ⟨105579075243749384031462917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70386050162499589354308611 105579075243749384031462917)
            ·
              refine ⟨19796076608203009505899297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105579075243749384031462917 19796076608203009505899297)
              ·
                refine ⟨14847057456152257129424473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19796076608203009505899297 14847057456152257129424473)
                ·
                  refine ⟨11135293092114192847068355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14847057456152257129424473 11135293092114192847068355)
                  ·
                    refine ⟨16702939638171289270602533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11135293092114192847068355 16702939638171289270602533)
                    ·
                      refine ⟨3131801182157116738237975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16702939638171289270602533 3131801182157116738237975)
                      ·
                        rfl

theorem cell23_6099161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_6099161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099161 prefixEnd_6099161 := by exact prefixLift 6099161
  have htrace : WordTrace (prefixWord ++ tailWord_6099161) baseStart_6099161 baseEnd_6099161 := by
    simpa [prefixWord, tailWord_6099161, baseEnd_6099161] using wordTrace_append hprefix tailTrace_6099161
  have hstable : (prefixWord ++ tailWord_6099161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099161).length < 2 ^ (prefixWord ++ tailWord_6099161).sum := by decide
  have hdescent : baseEnd_6099161 < baseStart_6099161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099178 : List Nat := [3, 1, 3, 1, 1, 2, 3, 1, 2, 4, 2]
def baseStart_6099178 : Nat := 118140960795 + 6099178 * 2 ^ 59
def prefixEnd_6099178 : Nat := 4983230072969 + 3 ^ 40 * 6099178 * 2
def baseEnd_6099178 : Nat := 3131809911328243171725397

theorem tailTrace_6099178 : CollatzResearch.WordTrace tailWord_6099178 prefixEnd_6099178 3131809911328243171725397 := by
  unfold tailWord_6099178
  simp only [CollatzResearch.WordTrace]
  refine ⟨55613824274431809379246547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148303531398484825011324125 55613824274431809379246547)
  ·
    refine ⟨83420736411647714068869821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55613824274431809379246547 83420736411647714068869821)
    ·
      refine ⟨31282776154367892775826183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83420736411647714068869821 31282776154367892775826183)
      ·
        refine ⟨46924164231551839163739275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31282776154367892775826183 46924164231551839163739275)
        ·
          refine ⟨70386246347327758745608913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46924164231551839163739275 70386246347327758745608913)
          ·
            refine ⟨52789684760495819059206685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70386246347327758745608913 52789684760495819059206685)
            ·
              refine ⟨19796131785185932147202507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52789684760495819059206685 19796131785185932147202507)
              ·
                refine ⟨29694197677778898220803761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19796131785185932147202507 29694197677778898220803761)
                ·
                  refine ⟨22270648258334173665602821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29694197677778898220803761 22270648258334173665602821)
                  ·
                    refine ⟨4175746548437657562300529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22270648258334173665602821 4175746548437657562300529)
                    ·
                      refine ⟨3131809911328243171725397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4175746548437657562300529 3131809911328243171725397)
                      ·
                        rfl

theorem cell23_6099178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_6099178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099178 prefixEnd_6099178 := by exact prefixLift 6099178
  have htrace : WordTrace (prefixWord ++ tailWord_6099178) baseStart_6099178 baseEnd_6099178 := by
    simpa [prefixWord, tailWord_6099178, baseEnd_6099178] using wordTrace_append hprefix tailTrace_6099178
  have hstable : (prefixWord ++ tailWord_6099178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099178).length < 2 ^ (prefixWord ++ tailWord_6099178).sum := by decide
  have hdescent : baseEnd_6099178 < baseStart_6099178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099198 : List Nat := [4, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_6099198 : Nat := 118140960795 + 6099198 * 2 ^ 59
def prefixEnd_6099198 : Nat := 4983230072969 + 3 ^ 40 * 6099198 * 2
def baseEnd_6099198 : Nat := 3131820180941333093475305

theorem tailTrace_6099198 : CollatzResearch.WordTrace tailWord_6099198 prefixEnd_6099198 3131820180941333093475305 := by
  unfold tailWord_6099198
  simp only [CollatzResearch.WordTrace]
  refine ⟨27807003319706847616589281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148304017705103187288476165 27807003319706847616589281)
  ·
    refine ⟨20855252489780135712441961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27807003319706847616589281 20855252489780135712441961)
    ·
      refine ⟨15641439367335101784331471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20855252489780135712441961 15641439367335101784331471)
      ·
        refine ⟨23462159051002652676497207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15641439367335101784331471 23462159051002652676497207)
        ·
          refine ⟨35193238576503979014745811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23462159051002652676497207 35193238576503979014745811)
          ·
            refine ⟨52789857864755968522118717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35193238576503979014745811 52789857864755968522118717)
            ·
              refine ⟨19796196699283488195794519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52789857864755968522118717 19796196699283488195794519)
              ·
                refine ⟨29694295048925232293691779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19796196699283488195794519 29694295048925232293691779)
                ·
                  refine ⟨44541442573387848440537669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29694295048925232293691779 44541442573387848440537669)
                  ·
                    refine ⟨8351520482510221582600813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44541442573387848440537669 8351520482510221582600813)
                    ·
                      refine ⟨3131820180941333093475305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8351520482510221582600813 3131820180941333093475305)
                      ·
                        rfl

theorem cell23_6099198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_6099198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099198 prefixEnd_6099198 := by exact prefixLift 6099198
  have htrace : WordTrace (prefixWord ++ tailWord_6099198) baseStart_6099198 baseEnd_6099198 := by
    simpa [prefixWord, tailWord_6099198, baseEnd_6099198] using wordTrace_append hprefix tailTrace_6099198
  have hstable : (prefixWord ++ tailWord_6099198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099198).length < 2 ^ (prefixWord ++ tailWord_6099198).sum := by decide
  have hdescent : baseEnd_6099198 < baseStart_6099198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099281 : List Nat := [1, 2, 2, 1, 4, 2, 1, 2, 1, 1, 6]
def baseStart_6099281 : Nat := 118140960795 + 6099281 * 2 ^ 59
def prefixEnd_6099281 : Nat := 4983230072969 + 3 ^ 40 * 6099281 * 2
def baseEnd_6099281 : Nat := 3131862799835656268737423

theorem tailTrace_6099281 : CollatzResearch.WordTrace tailWord_6099281 prefixEnd_6099281 3131862799835656268737423 := by
  unfold tailWord_6099281
  simp only [CollatzResearch.WordTrace]
  refine ⟨222459053816354086107985697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148306035877569390738657131 222459053816354086107985697)
  ·
    refine ⟨166844290362265564580989273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222459053816354086107985697 166844290362265564580989273)
    ·
      refine ⟨125133217771699173435741955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166844290362265564580989273 125133217771699173435741955)
      ·
        refine ⟨187699826657548760153612933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125133217771699173435741955 187699826657548760153612933)
        ·
          refine ⟨35193717498290392528802425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187699826657548760153612933 35193717498290392528802425)
          ·
            refine ⟨26395288123717794396601819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35193717498290392528802425 26395288123717794396601819)
            ·
              refine ⟨39592932185576691594902729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26395288123717794396601819 39592932185576691594902729)
              ·
                refine ⟨29694699139182518696177047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39592932185576691594902729 29694699139182518696177047)
                ·
                  refine ⟨44542048708773778044265571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29694699139182518696177047 44542048708773778044265571)
                  ·
                    refine ⟨66813073063160667066398357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44542048708773778044265571 66813073063160667066398357)
                    ·
                      refine ⟨3131862799835656268737423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66813073063160667066398357 3131862799835656268737423)
                      ·
                        rfl

theorem cell23_6099281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_6099281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099281 prefixEnd_6099281 := by exact prefixLift 6099281
  have htrace : WordTrace (prefixWord ++ tailWord_6099281) baseStart_6099281 baseEnd_6099281 := by
    simpa [prefixWord, tailWord_6099281, baseEnd_6099281] using wordTrace_append hprefix tailTrace_6099281
  have hstable : (prefixWord ++ tailWord_6099281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099281).length < 2 ^ (prefixWord ++ tailWord_6099281).sum := by decide
  have hdescent : baseEnd_6099281 < baseStart_6099281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099295 : List Nat := [1, 1, 2, 3, 1, 2, 6, 1, 2, 4]
def baseStart_6099295 : Nat := 118140960795 + 6099295 * 2 ^ 59
def prefixEnd_6099295 : Nat := 4983230072969 + 3 ^ 40 * 6099295 * 2
def baseEnd_6099295 : Nat := 1043956662854939737987453

theorem tailTrace_6099295 : CollatzResearch.WordTrace tailWord_6099295 prefixEnd_6099295 1043956662854939737987453 := by
  unfold tailWord_6099295
  simp only [CollatzResearch.WordTrace]
  refine ⟨222459564438303366498995339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148306376292202244332663559 222459564438303366498995339)
  ·
    refine ⟨333689346657455049748493009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222459564438303366498995339 333689346657455049748493009)
    ·
      refine ⟨250267009993091287311369757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333689346657455049748493009 250267009993091287311369757)
      ·
        refine ⟨93850128747409232741763659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250267009993091287311369757 93850128747409232741763659)
        ·
          refine ⟨140775193121113849112645489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93850128747409232741763659 140775193121113849112645489)
          ·
            refine ⟨105581394840835386834484117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140775193121113849112645489 105581394840835386834484117)
            ·
              refine ⟨4949127883164158757866443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 105581394840835386834484117 4949127883164158757866443)
              ·
                refine ⟨7423691824746238136799665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4949127883164158757866443 7423691824746238136799665)
                ·
                  refine ⟨5567768868559678602599749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7423691824746238136799665 5567768868559678602599749)
                  ·
                    refine ⟨1043956662854939737987453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5567768868559678602599749 1043956662854939737987453)
                    ·
                      rfl

theorem cell23_6099295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 2, 4].length) (baseStart_6099295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099295 prefixEnd_6099295 := by exact prefixLift 6099295
  have htrace : WordTrace (prefixWord ++ tailWord_6099295) baseStart_6099295 baseEnd_6099295 := by
    simpa [prefixWord, tailWord_6099295, baseEnd_6099295] using wordTrace_append hprefix tailTrace_6099295
  have hstable : (prefixWord ++ tailWord_6099295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099295).length < 2 ^ (prefixWord ++ tailWord_6099295).sum := by decide
  have hdescent : baseEnd_6099295 < baseStart_6099295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099298 : List Nat := [3, 3, 2, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_6099298 : Nat := 118140960795 + 6099298 * 2 ^ 59
def prefixEnd_6099298 : Nat := 4983230072969 + 3 ^ 40 * 6099298 * 2
def baseEnd_6099298 : Nat := 3131871529006782702224845

theorem tailTrace_6099298 : CollatzResearch.WordTrace tailWord_6099298 prefixEnd_6099298 3131871529006782702224845 := by
  unfold tailWord_6099298
  simp only [CollatzResearch.WordTrace]
  refine ⟨55614918464323124502838637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148306449238194998674236365 55614918464323124502838637)
  ·
    refine ⟨20855594424121171688564489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55614918464323124502838637 20855594424121171688564489)
    ·
      refine ⟨15641695818090878766423367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20855594424121171688564489 15641695818090878766423367)
      ·
        refine ⟨23462543727136318149635051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15641695818090878766423367 23462543727136318149635051)
        ·
          refine ⟨35193815590704477224452577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23462543727136318149635051 35193815590704477224452577)
          ·
            refine ⟨26395361693028357918339433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35193815590704477224452577 26395361693028357918339433)
            ·
              refine ⟨19796521269771268438754575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26395361693028357918339433 19796521269771268438754575)
              ·
                refine ⟨29694781904656902658131863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19796521269771268438754575 29694781904656902658131863)
                ·
                  refine ⟨44542172856985353987197795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29694781904656902658131863 44542172856985353987197795)
                  ·
                    refine ⟨66813259285478030980796693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44542172856985353987197795 66813259285478030980796693)
                    ·
                      refine ⟨3131871529006782702224845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66813259285478030980796693 3131871529006782702224845)
                      ·
                        rfl

theorem cell23_6099298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_6099298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099298 prefixEnd_6099298 := by exact prefixLift 6099298
  have htrace : WordTrace (prefixWord ++ tailWord_6099298) baseStart_6099298 baseEnd_6099298 := by
    simpa [prefixWord, tailWord_6099298, baseEnd_6099298] using wordTrace_append hprefix tailTrace_6099298
  have hstable : (prefixWord ++ tailWord_6099298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099298).length < 2 ^ (prefixWord ++ tailWord_6099298).sum := by decide
  have hdescent : baseEnd_6099298 < baseStart_6099298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099330 : List Nat := [3, 4, 2, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_6099330 : Nat := 118140960795 + 6099330 * 2 ^ 59
def prefixEnd_6099330 : Nat := 4983230072969 + 3 ^ 40 * 6099330 * 2
def baseEnd_6099330 : Nat := 3131887960387726577024699

theorem tailTrace_6099330 : CollatzResearch.WordTrace tailWord_6099330 prefixEnd_6099330 3131887960387726577024699 := by
  unfold tailWord_6099330
  simp only [CollatzResearch.WordTrace]
  refine ⟨55615210248294141869129861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148307227328784378317679629 55615210248294141869129861)
  ·
    refine ⟨10427851921555151600461849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55615210248294141869129861 10427851921555151600461849)
    ·
      refine ⟨7820888941166363700346387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10427851921555151600461849 7820888941166363700346387)
      ·
        refine ⟨11731333411749545550519581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7820888941166363700346387 11731333411749545550519581)
        ·
          refine ⟨4399250029406079581444843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11731333411749545550519581 4399250029406079581444843)
          ·
            refine ⟨6598875044109119372167265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4399250029406079581444843 6598875044109119372167265)
            ·
              refine ⟨4949156283081839529125449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6598875044109119372167265 4949156283081839529125449)
              ·
                refine ⟨3711867212311379646844087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4949156283081839529125449 3711867212311379646844087)
                ·
                  refine ⟨5567800818467069470266131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3711867212311379646844087 5567800818467069470266131)
                  ·
                    refine ⟨8351701227700604205399197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5567800818467069470266131 8351701227700604205399197)
                    ·
                      refine ⟨3131887960387726577024699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8351701227700604205399197 3131887960387726577024699)
                      ·
                        rfl

theorem cell23_6099330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_6099330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099330 prefixEnd_6099330 := by exact prefixLift 6099330
  have htrace : WordTrace (prefixWord ++ tailWord_6099330) baseStart_6099330 baseEnd_6099330 := by
    simpa [prefixWord, tailWord_6099330, baseEnd_6099330] using wordTrace_append hprefix tailTrace_6099330
  have hstable : (prefixWord ++ tailWord_6099330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099330).length < 2 ^ (prefixWord ++ tailWord_6099330).sum := by decide
  have hdescent : baseEnd_6099330 < baseStart_6099330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099351 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 1, 8]
def baseStart_6099351 : Nat := 118140960795 + 6099351 * 2 ^ 59
def prefixEnd_6099351 : Nat := 4983230072969 + 3 ^ 40 * 6099351 * 2
def baseEnd_6099351 : Nat := 1043966247827156998287367

theorem tailTrace_6099351 : CollatzResearch.WordTrace tailWord_6099351 prefixEnd_6099351 1043966247827156998287367 := by
  unfold tailWord_6099351
  simp only [CollatzResearch.WordTrace]
  refine ⟨222461606926100488063033907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148307737950733658708689271 222461606926100488063033907)
  ·
    refine ⟨333692410389150732094550861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222461606926100488063033907 333692410389150732094550861)
    ·
      refine ⟨125134653895931524535456573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333692410389150732094550861 125134653895931524535456573)
      ·
        refine ⟨46925495210974321700796215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125134653895931524535456573 46925495210974321700796215)
        ·
          refine ⟨70388242816461482551194323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46925495210974321700796215 70388242816461482551194323)
          ·
            refine ⟨105582364224692223826791485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70388242816461482551194323 105582364224692223826791485)
            ·
              refine ⟨39593386584259583935046807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105582364224692223826791485 39593386584259583935046807)
              ·
                refine ⟨59390079876389375902570211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39593386584259583935046807 59390079876389375902570211)
                ·
                  refine ⟨89085119814584063853855317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59390079876389375902570211 89085119814584063853855317)
                  ·
                    refine ⟨1043966247827156998287367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89085119814584063853855317 1043966247827156998287367)
                    ·
                      rfl

theorem cell23_6099351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_6099351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099351 prefixEnd_6099351 := by exact prefixLift 6099351
  have htrace : WordTrace (prefixWord ++ tailWord_6099351) baseStart_6099351 baseEnd_6099351 := by
    simpa [prefixWord, tailWord_6099351, baseEnd_6099351] using wordTrace_append hprefix tailTrace_6099351
  have hstable : (prefixWord ++ tailWord_6099351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099351).length < 2 ^ (prefixWord ++ tailWord_6099351).sum := by decide
  have hdescent : baseEnd_6099351 < baseStart_6099351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099352 : List Nat := [2, 1, 2, 5, 1, 1, 2, 3, 2, 1, 3]
def baseStart_6099352 : Nat := 118140960795 + 6099352 * 2 ^ 59
def prefixEnd_6099352 : Nat := 4983230072969 + 3 ^ 40 * 6099352 * 2
def baseEnd_6099352 : Nat := 3131899256962125490949597

theorem tailTrace_6099352 : CollatzResearch.WordTrace tailWord_6099352 prefixEnd_6099352 3131899256962125490949597 := by
  unfold tailWord_6099352
  simp only [CollatzResearch.WordTrace]
  refine ⟨111230821699548432616910155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148307762266064576822546873 111230821699548432616910155)
  ·
    refine ⟨166846232549322648925365233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111230821699548432616910155 166846232549322648925365233)
    ·
      refine ⟨125134674411991986694023925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166846232549322648925365233 125134674411991986694023925)
      ·
        refine ⟨11731375726124248752564743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125134674411991986694023925 11731375726124248752564743)
        ·
          refine ⟨17597063589186373128847115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11731375726124248752564743 17597063589186373128847115)
          ·
            refine ⟨26395595383779559693270673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17597063589186373128847115 26395595383779559693270673)
            ·
              refine ⟨19796696537834669769953005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26395595383779559693270673 19796696537834669769953005)
              ·
                refine ⟨7423761201688001163732377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19796696537834669769953005 7423761201688001163732377)
                ·
                  refine ⟨5567820901266000872799283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7423761201688001163732377 5567820901266000872799283)
                  ·
                    refine ⟨8351731351899001309198925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5567820901266000872799283 8351731351899001309198925)
                    ·
                      refine ⟨3131899256962125490949597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8351731351899001309198925 3131899256962125490949597)
                      ·
                        rfl

theorem cell23_6099352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_6099352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099352 prefixEnd_6099352 := by exact prefixLift 6099352
  have htrace : WordTrace (prefixWord ++ tailWord_6099352) baseStart_6099352 baseEnd_6099352 := by
    simpa [prefixWord, tailWord_6099352, baseEnd_6099352] using wordTrace_append hprefix tailTrace_6099352
  have hstable : (prefixWord ++ tailWord_6099352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099352).length < 2 ^ (prefixWord ++ tailWord_6099352).sum := by decide
  have hdescent : baseEnd_6099352 < baseStart_6099352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099362 : List Nat := [3, 3, 1, 2, 1, 1, 2, 4, 1, 3, 2]
def baseStart_6099362 : Nat := 118140960795 + 6099362 * 2 ^ 59
def prefixEnd_6099362 : Nat := 4983230072969 + 3 ^ 40 * 6099362 * 2
def baseEnd_6099362 : Nat := 3131904391768670451824551

theorem tailTrace_6099362 : CollatzResearch.WordTrace tailWord_6099362 prefixEnd_6099362 3131904391768670451824551 := by
  unfold tailWord_6099362
  simp only [CollatzResearch.WordTrace]
  refine ⟨55615502032265159235421085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148308005419373757961122893 55615502032265159235421085)
  ·
    refine ⟨20855813262099434713282907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55615502032265159235421085 20855813262099434713282907)
    ·
      refine ⟨31283719893149152069924361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20855813262099434713282907 31283719893149152069924361)
      ·
        refine ⟨23462789919861864052443271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31283719893149152069924361 23462789919861864052443271)
        ·
          refine ⟨35194184879792796078664907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23462789919861864052443271 35194184879792796078664907)
          ·
            refine ⟨52791277319689194117997361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35194184879792796078664907 52791277319689194117997361)
            ·
              refine ⟨39593457989766895588498021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52791277319689194117997361 39593457989766895588498021)
              ·
                refine ⟨7423773373081292922843379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39593457989766895588498021 7423773373081292922843379)
                ·
                  refine ⟨11135660059621939384265069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7423773373081292922843379 11135660059621939384265069)
                  ·
                    refine ⟨4175872522358227269099401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11135660059621939384265069 4175872522358227269099401)
                    ·
                      refine ⟨3131904391768670451824551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4175872522358227269099401 3131904391768670451824551)
                      ·
                        rfl

theorem cell23_6099362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_6099362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099362 prefixEnd_6099362 := by exact prefixLift 6099362
  have htrace : WordTrace (prefixWord ++ tailWord_6099362) baseStart_6099362 baseEnd_6099362 := by
    simpa [prefixWord, tailWord_6099362, baseEnd_6099362] using wordTrace_append hprefix tailTrace_6099362
  have hstable : (prefixWord ++ tailWord_6099362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099362).length < 2 ^ (prefixWord ++ tailWord_6099362).sum := by decide
  have hdescent : baseEnd_6099362 < baseStart_6099362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099370 : List Nat := [3, 1, 6, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_6099370 : Nat := 118140960795 + 6099370 * 2 ^ 59
def prefixEnd_6099370 : Nat := 4983230072969 + 3 ^ 40 * 6099370 * 2
def baseEnd_6099370 : Nat := 3131908499613906420524515

theorem tailTrace_6099370 : CollatzResearch.WordTrace tailWord_6099370 prefixEnd_6099370 3131908499613906420524515 := by
  unfold tailWord_6099370
  simp only [CollatzResearch.WordTrace]
  refine ⟨55615574978257913576993891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148308199942021102871983709 55615574978257913576993891)
  ·
    refine ⟨83423362467386870365490837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55615574978257913576993891 83423362467386870365490837)
    ·
      refine ⟨3910470115658759548382383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83423362467386870365490837 3910470115658759548382383)
      ·
        refine ⟨5865705173488139322573575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3910470115658759548382383 5865705173488139322573575)
        ·
          refine ⟨8798557760232208983860363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5865705173488139322573575 8798557760232208983860363)
          ·
            refine ⟨13197836640348313475790545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8798557760232208983860363 13197836640348313475790545)
            ·
              refine ⟨9898377480261235106842909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13197836640348313475790545 9898377480261235106842909)
              ·
                refine ⟨3711891555097963165066091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9898377480261235106842909 3711891555097963165066091)
                ·
                  refine ⟨5567837332646944747599137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3711891555097963165066091 5567837332646944747599137)
                  ·
                    refine ⟨4175877999485208560699353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5567837332646944747599137 4175877999485208560699353)
                    ·
                      refine ⟨3131908499613906420524515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4175877999485208560699353 3131908499613906420524515)
                      ·
                        rfl

theorem cell23_6099370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_6099370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099370 prefixEnd_6099370 := by exact prefixLift 6099370
  have htrace : WordTrace (prefixWord ++ tailWord_6099370) baseStart_6099370 baseEnd_6099370 := by
    simpa [prefixWord, tailWord_6099370, baseEnd_6099370] using wordTrace_append hprefix tailTrace_6099370
  have hstable : (prefixWord ++ tailWord_6099370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099370).length < 2 ^ (prefixWord ++ tailWord_6099370).sum := by decide
  have hdescent : baseEnd_6099370 < baseStart_6099370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099432 : List Nat := [2, 1, 4, 1, 1, 5, 1, 3, 5]
def baseStart_6099432 : Nat := 118140960795 + 6099432 * 2 ^ 59
def prefixEnd_6099432 : Nat := 4983230072969 + 3 ^ 40 * 6099432 * 2
def baseEnd_6099432 : Nat := 347993370601609464216581

theorem tailTrace_6099432 : CollatzResearch.WordTrace tailWord_6099432 prefixEnd_6099432 347993370601609464216581 := by
  unfold tailWord_6099432
  simp only [CollatzResearch.WordTrace]
  refine ⟨111232280619403519448366275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148309707492538025931155033 111232280619403519448366275)
  ·
    refine ⟨166848420929105279172549413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111232280619403519448366275 166848420929105279172549413)
    ·
      refine ⟨31284078924207239844853015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166848420929105279172549413 31284078924207239844853015)
      ·
        refine ⟨46926118386310859767279523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31284078924207239844853015 46926118386310859767279523)
        ·
          refine ⟨70389177579466289650919285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46926118386310859767279523 70389177579466289650919285)
          ·
            refine ⟨6598985398074964654773683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70389177579466289650919285 6598985398074964654773683)
            ·
              refine ⟨9898478097112446982160525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6598985398074964654773683 9898478097112446982160525)
              ·
                refine ⟨3711929286417167618310197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9898478097112446982160525 3711929286417167618310197)
                ·
                  refine ⟨347993370601609464216581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3711929286417167618310197 347993370601609464216581)
                  ·
                    rfl

theorem cell23_6099432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 5].length) (baseStart_6099432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099432 prefixEnd_6099432 := by exact prefixLift 6099432
  have htrace : WordTrace (prefixWord ++ tailWord_6099432) baseStart_6099432 baseEnd_6099432 := by
    simpa [prefixWord, tailWord_6099432, baseEnd_6099432] using wordTrace_append hprefix tailTrace_6099432
  have hstable : (prefixWord ++ tailWord_6099432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099432).length < 2 ^ (prefixWord ++ tailWord_6099432).sum := by decide
  have hdescent : baseEnd_6099432 < baseStart_6099432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099532 : List Nat := [2, 2, 1, 3, 1, 2, 3, 2, 3, 1, 3]
def baseStart_6099532 : Nat := 118140960795 + 6099532 * 2 ^ 59
def prefixEnd_6099532 : Nat := 4983230072969 + 3 ^ 40 * 6099532 * 2
def baseEnd_6099532 : Nat := 3131991683479934786698769

theorem tailTrace_6099532 : CollatzResearch.WordTrace tailWord_6099532 prefixEnd_6099532 3131991683479934786698769 := by
  unfold tailWord_6099532
  simp only [CollatzResearch.WordTrace]
  refine ⟨111234104269222377987686425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148312139025629837316915233 111234104269222377987686425)
  ·
    refine ⟨83425578201916783490764819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111234104269222377987686425 83425578201916783490764819)
    ·
      refine ⟨125138367302875175236147229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83425578201916783490764819 125138367302875175236147229)
      ·
        refine ⟨46926887738578190713555211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125138367302875175236147229 46926887738578190713555211)
        ·
          refine ⟨70390331607867286070332817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46926887738578190713555211 70390331607867286070332817)
          ·
            refine ⟨52792748705900464552749613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70390331607867286070332817 52792748705900464552749613)
            ·
              refine ⟨19797280764712674207281105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52792748705900464552749613 19797280764712674207281105)
              ·
                refine ⟨14847960573534505655460829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19797280764712674207281105 14847960573534505655460829)
                ·
                  refine ⟨5567985215075439620797811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14847960573534505655460829 5567985215075439620797811)
                  ·
                    refine ⟨8351977822613159431196717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5567985215075439620797811 8351977822613159431196717)
                    ·
                      refine ⟨3131991683479934786698769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8351977822613159431196717 3131991683479934786698769)
                      ·
                        rfl

theorem cell23_6099532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_6099532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099532 prefixEnd_6099532 := by exact prefixLift 6099532
  have htrace : WordTrace (prefixWord ++ tailWord_6099532) baseStart_6099532 baseEnd_6099532 := by
    simpa [prefixWord, tailWord_6099532, baseEnd_6099532] using wordTrace_append hprefix tailTrace_6099532
  have hstable : (prefixWord ++ tailWord_6099532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099532).length < 2 ^ (prefixWord ++ tailWord_6099532).sum := by decide
  have hdescent : baseEnd_6099532 < baseStart_6099532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099552 : List Nat := [2, 1, 1, 3, 2, 1, 6, 1, 1, 5]
def baseStart_6099552 : Nat := 118140960795 + 6099552 * 2 ^ 59
def prefixEnd_6099552 : Nat := 4983230072969 + 3 ^ 40 * 6099552 * 2
def baseEnd_6099552 : Nat := 1044000651031008236149559

theorem tailTrace_6099552 : CollatzResearch.WordTrace tailWord_6099552 prefixEnd_6099552 1044000651031008236149559 := by
  unfold tailWord_6099552
  simp only [CollatzResearch.WordTrace]
  refine ⟨111234468999186149695550455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148312625332248199594067273 111234468999186149695550455)
  ·
    refine ⟨166851703498779224543325683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111234468999186149695550455 166851703498779224543325683)
    ·
      refine ⟨250277555248168836814988525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166851703498779224543325683 250277555248168836814988525)
      ·
        refine ⟨93854083218063313805620697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250277555248168836814988525 93854083218063313805620697)
        ·
          refine ⟨70390562413547485354215523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93854083218063313805620697 70390562413547485354215523)
          ·
            refine ⟨105585843620321228031323285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70390562413547485354215523 105585843620321228031323285)
            ·
              refine ⟨4949336419702557563968279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 105585843620321228031323285 4949336419702557563968279)
              ·
                refine ⟨7424004629553836345952419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4949336419702557563968279 7424004629553836345952419)
                ·
                  refine ⟨11136006944330754518928629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7424004629553836345952419 11136006944330754518928629)
                  ·
                    refine ⟨1044000651031008236149559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11136006944330754518928629 1044000651031008236149559)
                    ·
                      rfl

theorem cell23_6099552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 1, 5].length) (baseStart_6099552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099552 prefixEnd_6099552 := by exact prefixLift 6099552
  have htrace : WordTrace (prefixWord ++ tailWord_6099552) baseStart_6099552 baseEnd_6099552 := by
    simpa [prefixWord, tailWord_6099552, baseEnd_6099552] using wordTrace_append hprefix tailTrace_6099552
  have hstable : (prefixWord ++ tailWord_6099552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099552).length < 2 ^ (prefixWord ++ tailWord_6099552).sum := by decide
  have hdescent : baseEnd_6099552 < baseStart_6099552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099566 : List Nat := [4, 1, 2, 2, 2, 1, 2, 4, 1, 1, 3]
def baseStart_6099566 : Nat := 118140960795 + 6099566 * 2 ^ 59
def prefixEnd_6099566 : Nat := 4983230072969 + 3 ^ 40 * 6099566 * 2
def baseEnd_6099566 : Nat := 3132009141822187653673613

theorem tailTrace_6099566 : CollatzResearch.WordTrace tailWord_6099566 prefixEnd_6099566 3132009141822187653673613 := by
  unfold tailWord_6099566
  simp only [CollatzResearch.WordTrace]
  refine ⟨27808681077540197472763819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148312965746881053188073701 27808681077540197472763819)
  ·
    refine ⟨41713021616310296209145729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27808681077540197472763819 41713021616310296209145729)
    ·
      refine ⟨31284766212232722156859297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41713021616310296209145729 31284766212232722156859297)
      ·
        refine ⟨23463574659174541617644473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31284766212232722156859297 23463574659174541617644473)
        ·
          refine ⟨17597680994380906213233355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23463574659174541617644473 17597680994380906213233355)
          ·
            refine ⟨26396521491571359319850033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17597680994380906213233355 26396521491571359319850033)
            ·
              refine ⟨19797391118678519489887525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26396521491571359319850033 19797391118678519489887525)
              ·
                refine ⟨3712010834752222404353911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19797391118678519489887525 3712010834752222404353911)
                ·
                  refine ⟨5568016252128333606530867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3712010834752222404353911 5568016252128333606530867)
                  ·
                    refine ⟨8352024378192500409796301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5568016252128333606530867 8352024378192500409796301)
                    ·
                      refine ⟨3132009141822187653673613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8352024378192500409796301 3132009141822187653673613)
                      ·
                        rfl

theorem cell23_6099566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_6099566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099566 prefixEnd_6099566 := by exact prefixLift 6099566
  have htrace : WordTrace (prefixWord ++ tailWord_6099566) baseStart_6099566 baseEnd_6099566 := by
    simpa [prefixWord, tailWord_6099566, baseEnd_6099566] using wordTrace_append hprefix tailTrace_6099566
  have hstable : (prefixWord ++ tailWord_6099566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099566).length < 2 ^ (prefixWord ++ tailWord_6099566).sum := by decide
  have hdescent : baseEnd_6099566 < baseStart_6099566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099575 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 3]
def baseStart_6099575 : Nat := 118140960795 + 6099575 * 2 ^ 59
def prefixEnd_6099575 : Nat := 4983230072969 + 3 ^ 40 * 6099575 * 2
def baseEnd_6099575 : Nat := 3132013763148078118461071

theorem tailTrace_6099575 : CollatzResearch.WordTrace tailWord_6099575 prefixEnd_6099575 3132013763148078118461071 := by
  unfold tailWord_6099575
  simp only [CollatzResearch.WordTrace]
  refine ⟨222469776877288974319188179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148313184584859316212792119 222469776877288974319188179)
  ·
    refine ⟨333704665315933461478782269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222469776877288974319188179 333704665315933461478782269)
    ·
      refine ⟨125139249493475048054543351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333704665315933461478782269 125139249493475048054543351)
      ·
        refine ⟨187708874240212572081815027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125139249493475048054543351 187708874240212572081815027)
        ·
          refine ⟨281563311360318858122722541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187708874240212572081815027 281563311360318858122722541)
          ·
            refine ⟨105586241760119571796020953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281563311360318858122722541 105586241760119571796020953)
            ·
              refine ⟨79189681320089678847015715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105586241760119571796020953 79189681320089678847015715)
              ·
                refine ⟨118784521980134518270523573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79189681320089678847015715 118784521980134518270523573)
                ·
                  refine ⟨11136048935637611087861585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118784521980134518270523573 11136048935637611087861585)
                  ·
                    refine ⟨8352036701728208315896189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11136048935637611087861585 8352036701728208315896189)
                    ·
                      refine ⟨3132013763148078118461071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8352036701728208315896189 3132013763148078118461071)
                      ·
                        rfl

theorem cell23_6099575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 3].length) (baseStart_6099575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099575 prefixEnd_6099575 := by exact prefixLift 6099575
  have htrace : WordTrace (prefixWord ++ tailWord_6099575) baseStart_6099575 baseEnd_6099575 := by
    simpa [prefixWord, tailWord_6099575, baseEnd_6099575] using wordTrace_append hprefix tailTrace_6099575
  have hstable : (prefixWord ++ tailWord_6099575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099575).length < 2 ^ (prefixWord ++ tailWord_6099575).sum := by decide
  have hdescent : baseEnd_6099575 < baseStart_6099575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099585 : List Nat := [1, 2, 4, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_6099585 : Nat := 118140960795 + 6099585 * 2 ^ 59
def prefixEnd_6099585 : Nat := 4983230072969 + 3 ^ 40 * 6099585 * 2
def baseEnd_6099585 : Nat := 3132018897954623079336025

theorem tailTrace_6099585 : CollatzResearch.WordTrace tailWord_6099585 prefixEnd_6099585 3132018897954623079336025 := by
  unfold tailWord_6099585
  simp only [CollatzResearch.WordTrace]
  refine ⟨222470141607252746027052209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148313427738168497351368139 222470141607252746027052209)
  ·
    refine ⟨166852606205439559520289157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222470141607252746027052209 166852606205439559520289157)
    ·
      refine ⟨31284863663519917410054217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166852606205439559520289157 31284863663519917410054217)
      ·
        refine ⟨23463647747639938057540663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31284863663519917410054217 23463647747639938057540663)
        ·
          refine ⟨35195471621459907086310995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23463647747639938057540663 35195471621459907086310995)
          ·
            refine ⟨52793207432189860629466493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35195471621459907086310995 52793207432189860629466493)
            ·
              refine ⟨19797452787071197736049935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52793207432189860629466493 19797452787071197736049935)
              ·
                refine ⟨29696179180606796604074903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19797452787071197736049935 29696179180606796604074903)
                ·
                  refine ⟨44544268770910194906112355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29696179180606796604074903 44544268770910194906112355)
                  ·
                    refine ⟨66816403156365292359168533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44544268770910194906112355 66816403156365292359168533)
                    ·
                      refine ⟨3132018897954623079336025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66816403156365292359168533 3132018897954623079336025)
                      ·
                        rfl

theorem cell23_6099585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_6099585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099585 prefixEnd_6099585 := by exact prefixLift 6099585
  have htrace : WordTrace (prefixWord ++ tailWord_6099585) baseStart_6099585 baseEnd_6099585 := by
    simpa [prefixWord, tailWord_6099585, baseEnd_6099585] using wordTrace_append hprefix tailTrace_6099585
  have hstable : (prefixWord ++ tailWord_6099585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099585).length < 2 ^ (prefixWord ++ tailWord_6099585).sum := by decide
  have hdescent : baseEnd_6099585 < baseStart_6099585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099589 : List Nat := [1, 3, 1, 1, 4, 2, 2, 2, 3, 2, 2]
def baseStart_6099589 : Nat := 118140960795 + 6099589 * 2 ^ 59
def prefixEnd_6099589 : Nat := 4983230072969 + 3 ^ 40 * 6099589 * 2
def baseEnd_6099589 : Nat := 3132020951877241063686007

theorem tailTrace_6099589 : CollatzResearch.WordTrace tailWord_6099589 prefixEnd_6099589 3132020951877241063686007 := by
  unfold tailWord_6099589
  simp only [CollatzResearch.WordTrace]
  refine ⟨222470287499238254710197821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148313524999492169806798547 222470287499238254710197821)
  ·
    refine ⟨83426357812214345516324183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222470287499238254710197821 83426357812214345516324183)
    ·
      refine ⟨125139536718321518274486275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83426357812214345516324183 125139536718321518274486275)
      ·
        refine ⟨187709305077482277411729413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125139536718321518274486275 187709305077482277411729413)
        ·
          refine ⟨35195494702027927014699265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187709305077482277411729413 35195494702027927014699265)
          ·
            refine ⟨26396621026520945261024449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35195494702027927014699265 26396621026520945261024449)
            ·
              refine ⟨19797465769890708945768337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26396621026520945261024449 19797465769890708945768337)
              ·
                refine ⟨14848099327418031709326253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19797465769890708945768337 14848099327418031709326253)
                ·
                  refine ⟨5568037247781761890997345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14848099327418031709326253 5568037247781761890997345)
                  ·
                    refine ⟨4176027935836321418248009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5568037247781761890997345 4176027935836321418248009)
                    ·
                      refine ⟨3132020951877241063686007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4176027935836321418248009 3132020951877241063686007)
                      ·
                        rfl

theorem cell23_6099589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 2, 2].length) (baseStart_6099589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099589 prefixEnd_6099589 := by exact prefixLift 6099589
  have htrace : WordTrace (prefixWord ++ tailWord_6099589) baseStart_6099589 baseEnd_6099589 := by
    simpa [prefixWord, tailWord_6099589, baseEnd_6099589] using wordTrace_append hprefix tailTrace_6099589
  have hstable : (prefixWord ++ tailWord_6099589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099589).length < 2 ^ (prefixWord ++ tailWord_6099589).sum := by decide
  have hdescent : baseEnd_6099589 < baseStart_6099589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099632 : List Nat := [2, 1, 1, 1, 2, 1, 3, 4, 3, 3, 2]
def baseStart_6099632 : Nat := 118140960795 + 6099632 * 2 ^ 59
def prefixEnd_6099632 : Nat := 4983230072969 + 3 ^ 40 * 6099632 * 2
def baseEnd_6099632 : Nat := 3132043031545384395448309

theorem tailTrace_6099632 : CollatzResearch.WordTrace tailWord_6099632 prefixEnd_6099632 3132043031545384395448309 := by
  unfold tailWord_6099632
  simp only [CollatzResearch.WordTrace]
  refine ⟨111235927919041236527006575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148314570558721648702675433 111235927919041236527006575)
  ·
    refine ⟨166853891878561854790509863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111235927919041236527006575 166853891878561854790509863)
    ·
      refine ⟨250280837817842782185764795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166853891878561854790509863 250280837817842782185764795)
      ·
        refine ⟨375421256726764173278647193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250280837817842782185764795 375421256726764173278647193)
        ·
          refine ⟨281565942545073129958985395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375421256726764173278647193 281565942545073129958985395)
          ·
            refine ⟨422348913817609694938478093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281565942545073129958985395 422348913817609694938478093)
            ·
              refine ⟨158380842681603635601929285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 422348913817609694938478093 158380842681603635601929285)
              ·
                refine ⟨29696408002800681675361741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158380842681603635601929285 29696408002800681675361741)
                ·
                  refine ⟨11136153001050255628260653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29696408002800681675361741 11136153001050255628260653)
                  ·
                    refine ⟨4176057375393845860597745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11136153001050255628260653 4176057375393845860597745)
                    ·
                      refine ⟨3132043031545384395448309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4176057375393845860597745 3132043031545384395448309)
                      ·
                        rfl

theorem cell23_6099632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 3, 3, 2].length) (baseStart_6099632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099632 prefixEnd_6099632 := by exact prefixLift 6099632
  have htrace : WordTrace (prefixWord ++ tailWord_6099632) baseStart_6099632 baseEnd_6099632 := by
    simpa [prefixWord, tailWord_6099632, baseEnd_6099632] using wordTrace_append hprefix tailTrace_6099632
  have hstable : (prefixWord ++ tailWord_6099632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099632).length < 2 ^ (prefixWord ++ tailWord_6099632).sum := by decide
  have hdescent : baseEnd_6099632 < baseStart_6099632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099633 : List Nat := [1, 2, 2, 6, 1, 2, 2, 1, 2, 4]
def baseStart_6099633 : Nat := 118140960795 + 6099633 * 2 ^ 59
def prefixEnd_6099633 : Nat := 4983230072969 + 3 ^ 40 * 6099633 * 2
def baseEnd_6099633 : Nat := 1044014515008679630511935

theorem tailTrace_6099633 : CollatzResearch.WordTrace tailWord_6099633 prefixEnd_6099633 1044014515008679630511935 := by
  unfold tailWord_6099633
  simp only [CollatzResearch.WordTrace]
  refine ⟨222471892311078850224799553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148314594874052566816533035 222471892311078850224799553)
  ·
    refine ⟨166853919233309137668599665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222471892311078850224799553 166853919233309137668599665)
    ·
      refine ⟨125140439424981853251449749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166853919233309137668599665 125140439424981853251449749)
      ·
        refine ⟨5865958098046024371161707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 125140439424981853251449749 5865958098046024371161707)
        ·
          refine ⟨8798937147069036556742561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5865958098046024371161707 8798937147069036556742561)
          ·
            refine ⟨6599202860301777417556921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8798937147069036556742561 6599202860301777417556921)
            ·
              refine ⟨4949402145226333063167691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6599202860301777417556921 4949402145226333063167691)
              ·
                refine ⟨7424103217839499594751537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4949402145226333063167691 7424103217839499594751537)
                ·
                  refine ⟨5568077413379624696063653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7424103217839499594751537 5568077413379624696063653)
                  ·
                    refine ⟨1044014515008679630511935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5568077413379624696063653 1044014515008679630511935)
                    ·
                      rfl

theorem cell23_6099633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 2, 4].length) (baseStart_6099633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099633 prefixEnd_6099633 := by exact prefixLift 6099633
  have htrace : WordTrace (prefixWord ++ tailWord_6099633) baseStart_6099633 baseEnd_6099633 := by
    simpa [prefixWord, tailWord_6099633, baseEnd_6099633] using wordTrace_append hprefix tailTrace_6099633
  have hstable : (prefixWord ++ tailWord_6099633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099633).length < 2 ^ (prefixWord ++ tailWord_6099633).sum := by decide
  have hdescent : baseEnd_6099633 < baseStart_6099633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099665 : List Nat := [1, 2, 2, 1, 2, 3, 1, 3, 2, 1, 5]
def baseStart_6099665 : Nat := 118140960795 + 6099665 * 2 ^ 59
def prefixEnd_6099665 : Nat := 4983230072969 + 3 ^ 40 * 6099665 * 2
def baseEnd_6099665 : Nat := 3132059976406982766335657

theorem tailTrace_6099665 : CollatzResearch.WordTrace tailWord_6099665 prefixEnd_6099665 3132059976406982766335657 := by
  unfold tailWord_6099665
  simp only [CollatzResearch.WordTrace]
  refine ⟨222473059446962919689964449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148315372964641946459976299 222473059446962919689964449)
  ·
    refine ⟨166854794585222189767473337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222473059446962919689964449 166854794585222189767473337)
    ·
      refine ⟨125141095938916642325605003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166854794585222189767473337 125141095938916642325605003)
      ·
        refine ⟨187711643908374963488407505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125141095938916642325605003 187711643908374963488407505)
        ·
          refine ⟨140783732931281222616305629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187711643908374963488407505 140783732931281222616305629)
          ·
            refine ⟨52793899849230458481114611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140783732931281222616305629 52793899849230458481114611)
            ·
              refine ⟨79190849773845687721671917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52793899849230458481114611 79190849773845687721671917)
              ·
                refine ⟨29696568665192132895626969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79190849773845687721671917 29696568665192132895626969)
                ·
                  refine ⟨22272426498894099671720227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29696568665192132895626969 22272426498894099671720227)
                  ·
                    refine ⟨33408639748341149507580341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22272426498894099671720227 33408639748341149507580341)
                    ·
                      refine ⟨3132059976406982766335657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33408639748341149507580341 3132059976406982766335657)
                      ·
                        rfl

theorem cell23_6099665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_6099665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099665 prefixEnd_6099665 := by exact prefixLift 6099665
  have htrace : WordTrace (prefixWord ++ tailWord_6099665) baseStart_6099665 baseEnd_6099665 := by
    simpa [prefixWord, tailWord_6099665, baseEnd_6099665] using wordTrace_append hprefix tailTrace_6099665
  have hstable : (prefixWord ++ tailWord_6099665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099665).length < 2 ^ (prefixWord ++ tailWord_6099665).sum := by decide
  have hdescent : baseEnd_6099665 < baseStart_6099665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099702 : List Nat := [5, 1, 1, 1, 1, 2, 3, 2, 7]
def baseStart_6099702 : Nat := 118140960795 + 6099702 * 2 ^ 59
def prefixEnd_6099702 : Nat := 4983230072969 + 3 ^ 40 * 6099702 * 2
def baseEnd_6099702 : Nat := 348008775021244346841443

theorem tailTrace_6099702 : CollatzResearch.WordTrace tailWord_6099702 prefixEnd_6099702 348008775021244346841443 := by
  unfold tailWord_6099702
  simp only [CollatzResearch.WordTrace]
  refine ⟨13904650559239304688066335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148316272631885916672707573 13904650559239304688066335)
  ·
    refine ⟨20856975838858957032099503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13904650559239304688066335 20856975838858957032099503)
    ·
      refine ⟨31285463758288435548149255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20856975838858957032099503 31285463758288435548149255)
      ·
        refine ⟨46928195637432653322223883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31285463758288435548149255 46928195637432653322223883)
        ·
          refine ⟨70392293456148979983335825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46928195637432653322223883 70392293456148979983335825)
          ·
            refine ⟨52794220092111734987501869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70392293456148979983335825 52794220092111734987501869)
            ·
              refine ⟨19797832534541900620313201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52794220092111734987501869 19797832534541900620313201)
              ·
                refine ⟨14848374400906425465234901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19797832534541900620313201 14848374400906425465234901)
                ·
                  refine ⟨348008775021244346841443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14848374400906425465234901 348008775021244346841443)
                  ·
                    rfl

theorem cell23_6099702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_6099702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099702 prefixEnd_6099702 := by exact prefixLift 6099702
  have htrace : WordTrace (prefixWord ++ tailWord_6099702) baseStart_6099702 baseEnd_6099702 := by
    simpa [prefixWord, tailWord_6099702, baseEnd_6099702] using wordTrace_append hprefix tailTrace_6099702
  have hstable : (prefixWord ++ tailWord_6099702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099702).length < 2 ^ (prefixWord ++ tailWord_6099702).sum := by decide
  have hdescent : baseEnd_6099702 < baseStart_6099702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099719 : List Nat := [1, 1, 4, 4, 1, 1, 1, 5, 5]
def baseStart_6099719 : Nat := 118140960795 + 6099719 * 2 ^ 59
def prefixEnd_6099719 : Nat := 4983230072969 + 3 ^ 40 * 6099719 * 2
def baseEnd_6099719 : Nat := 348009744929147283895601

theorem tailTrace_6099719 : CollatzResearch.WordTrace tailWord_6099719 prefixEnd_6099719 348009744929147283895601 := by
  unfold tailWord_6099719
  simp only [CollatzResearch.WordTrace]
  refine ⟨222475028988767286912430211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148316685992511524608286807 222475028988767286912430211)
  ·
    refine ⟨333712543483150930368645317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222475028988767286912430211 333712543483150930368645317)
    ·
      refine ⟨62571101903090799444120997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 333712543483150930368645317 62571101903090799444120997)
      ·
        refine ⟨11732081606829524895772687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62571101903090799444120997 11732081606829524895772687)
        ·
          refine ⟨17598122410244287343659031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11732081606829524895772687 17598122410244287343659031)
          ·
            refine ⟨26397183615366431015488547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17598122410244287343659031 26397183615366431015488547)
            ·
              refine ⟨39595775423049646523232821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26397183615366431015488547 39595775423049646523232821)
              ·
                refine ⟨3712103945910904361553077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39595775423049646523232821 3712103945910904361553077)
                ·
                  refine ⟨348009744929147283895601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3712103945910904361553077 348009744929147283895601)
                  ·
                    rfl

theorem cell23_6099719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 5].length) (baseStart_6099719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099719 prefixEnd_6099719 := by exact prefixLift 6099719
  have htrace : WordTrace (prefixWord ++ tailWord_6099719) baseStart_6099719 baseEnd_6099719 := by
    simpa [prefixWord, tailWord_6099719, baseEnd_6099719] using wordTrace_append hprefix tailTrace_6099719
  have hstable : (prefixWord ++ tailWord_6099719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099719).length < 2 ^ (prefixWord ++ tailWord_6099719).sum := by decide
  have hdescent : baseEnd_6099719 < baseStart_6099719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099752 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_6099752 : Nat := 118140960795 + 6099752 * 2 ^ 59
def prefixEnd_6099752 : Nat := 4983230072969 + 3 ^ 40 * 6099752 * 2
def baseEnd_6099752 : Nat := 3132104649223923925947757

theorem tailTrace_6099752 : CollatzResearch.WordTrace tailWord_6099752 prefixEnd_6099752 3132104649223923925947757 := by
  unfold tailWord_6099752
  simp only [CollatzResearch.WordTrace]
  refine ⟨111238116298823866774190755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148317488398431822365587673 111238116298823866774190755)
  ·
    refine ⟨166857174448235800161286133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111238116298823866774190755 166857174448235800161286133)
    ·
      refine ⟨15642860104522106265120575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166857174448235800161286133 15642860104522106265120575)
      ·
        refine ⟨23464290156783159397680863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15642860104522106265120575 23464290156783159397680863)
        ·
          refine ⟨35196435235174739096521295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23464290156783159397680863 35196435235174739096521295)
          ·
            refine ⟨52794652852762108644781943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35196435235174739096521295 52794652852762108644781943)
            ·
              refine ⟨79191979279143162967172915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52794652852762108644781943 79191979279143162967172915)
              ·
                refine ⟨118787968918714744450759373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79191979279143162967172915 118787968918714744450759373)
                ·
                  refine ⟨44545488344518029169034765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118787968918714744450759373 44545488344518029169034765)
                  ·
                    refine ⟨16704558129194260938388037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44545488344518029169034765 16704558129194260938388037)
                    ·
                      refine ⟨3132104649223923925947757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16704558129194260938388037 3132104649223923925947757)
                      ·
                        rfl

theorem cell23_6099752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_6099752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099752 prefixEnd_6099752 := by exact prefixLift 6099752
  have htrace : WordTrace (prefixWord ++ tailWord_6099752) baseStart_6099752 baseEnd_6099752 := by
    simpa [prefixWord, tailWord_6099752, baseEnd_6099752] using wordTrace_append hprefix tailTrace_6099752
  have hstable : (prefixWord ++ tailWord_6099752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099752).length < 2 ^ (prefixWord ++ tailWord_6099752).sum := by decide
  have hdescent : baseEnd_6099752 < baseStart_6099752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099795 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 8]
def baseStart_6099795 : Nat := 118140960795 + 6099795 * 2 ^ 59
def prefixEnd_6099795 : Nat := 4983230072969 + 3 ^ 40 * 6099795 * 2
def baseEnd_6099795 : Nat := 3132126728892067257710059

theorem tailTrace_6099795 : CollatzResearch.WordTrace tailWord_6099795 prefixEnd_6099795 3132126728892067257710059 := by
  unfold tailWord_6099795
  simp only [CollatzResearch.WordTrace]
  refine ⟨222477800936491951892196839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148318533957661301261464559 222477800936491951892196839)
  ·
    refine ⟨333716701404737927838295259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222477800936491951892196839 333716701404737927838295259)
    ·
      refine ⟨500575052107106891757442889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333716701404737927838295259 500575052107106891757442889)
      ·
        refine ⟨375431289080330168818082167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 500575052107106891757442889 375431289080330168818082167)
        ·
          refine ⟨563146933620495253227123251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375431289080330168818082167 563146933620495253227123251)
          ·
            refine ⟨844720400430742879840684877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563146933620495253227123251 844720400430742879840684877)
            ·
              refine ⟨316770150161528579940256829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 844720400430742879840684877 316770150161528579940256829)
              ·
                refine ⟨118788806310573217477596311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 316770150161528579940256829 118788806310573217477596311)
                ·
                  refine ⟨178183209465859826216394467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118788806310573217477596311 178183209465859826216394467)
                  ·
                    refine ⟨267274814198789739324591701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 178183209465859826216394467 267274814198789739324591701)
                    ·
                      refine ⟨3132126728892067257710059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 267274814198789739324591701 3132126728892067257710059)
                      ·
                        rfl

theorem cell23_6099795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_6099795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099795 prefixEnd_6099795 := by exact prefixLift 6099795
  have htrace : WordTrace (prefixWord ++ tailWord_6099795) baseStart_6099795 baseEnd_6099795 := by
    simpa [prefixWord, tailWord_6099795, baseEnd_6099795] using wordTrace_append hprefix tailTrace_6099795
  have hstable : (prefixWord ++ tailWord_6099795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099795).length < 2 ^ (prefixWord ++ tailWord_6099795).sum := by decide
  have hdescent : baseEnd_6099795 < baseStart_6099795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099819 : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 3, 1, 3]
def baseStart_6099819 : Nat := 118140960795 + 6099819 * 2 ^ 59
def prefixEnd_6099819 : Nat := 4983230072969 + 3 ^ 40 * 6099819 * 2
def baseEnd_6099819 : Nat := 3132139052427775163809949

theorem tailTrace_6099819 : CollatzResearch.WordTrace tailWord_6099819 prefixEnd_6099819 3132139052427775163809949 := by
  unfold tailWord_6099819
  simp only [CollatzResearch.WordTrace]
  refine ⟨222478676288405003991070511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148319117525603335994047007 222478676288405003991070511)
  ·
    refine ⟨333718014432607505986605767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222478676288405003991070511 333718014432607505986605767)
    ·
      refine ⟨500577021648911258979908651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333718014432607505986605767 500577021648911258979908651)
      ·
        refine ⟨750865532473366888469862977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500577021648911258979908651 750865532473366888469862977)
        ·
          refine ⟨563149149355025166352397233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 750865532473366888469862977 563149149355025166352397233)
          ·
            refine ⟨422361862016268874764297925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 563149149355025166352397233 422361862016268874764297925)
            ·
              refine ⟨79192849128050414018305861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 422361862016268874764297925 79192849128050414018305861)
              ·
                refine ⟨14848659211509452628432349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79192849128050414018305861 14848659211509452628432349)
                ·
                  refine ⟨5568247204316044735662131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14848659211509452628432349 5568247204316044735662131)
                  ·
                    refine ⟨8352370806474067103493197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5568247204316044735662131 8352370806474067103493197)
                    ·
                      refine ⟨3132139052427775163809949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8352370806474067103493197 3132139052427775163809949)
                      ·
                        rfl

theorem cell23_6099819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 1, 3].length) (baseStart_6099819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099819 prefixEnd_6099819 := by exact prefixLift 6099819
  have htrace : WordTrace (prefixWord ++ tailWord_6099819) baseStart_6099819 baseEnd_6099819 := by
    simpa [prefixWord, tailWord_6099819, baseEnd_6099819] using wordTrace_append hprefix tailTrace_6099819
  have hstable : (prefixWord ++ tailWord_6099819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099819).length < 2 ^ (prefixWord ++ tailWord_6099819).sum := by decide
  have hdescent : baseEnd_6099819 < baseStart_6099819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099869 : List Nat := [1, 4, 2, 1, 2, 1, 4, 1, 1, 6]
def baseStart_6099869 : Nat := 118140960795 + 6099869 * 2 ^ 59
def prefixEnd_6099869 : Nat := 4983230072969 + 3 ^ 40 * 6099869 * 2
def baseEnd_6099869 : Nat := 1044054908820166656061573

theorem tailTrace_6099869 : CollatzResearch.WordTrace tailWord_6099869 prefixEnd_6099869 1044054908820166656061573 := by
  unfold tailWord_6099869
  simp only [CollatzResearch.WordTrace]
  refine ⟨222480499938223862530390661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148320333292149241686927107 222480499938223862530390661)
  ·
    refine ⟨41715093738416974224448249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222480499938223862530390661 41715093738416974224448249)
    ·
      refine ⟨31286320303812730668336187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41715093738416974224448249 31286320303812730668336187)
      ·
        refine ⟨46929480455719096002504281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31286320303812730668336187 46929480455719096002504281)
        ·
          refine ⟨35197110341789322001878211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46929480455719096002504281 35197110341789322001878211)
          ·
            refine ⟨52795665512683983002817317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35197110341789322001878211 52795665512683983002817317)
            ·
              refine ⟨9899187283628246813028247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52795665512683983002817317 9899187283628246813028247)
              ·
                refine ⟨14848780925442370219542371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9899187283628246813028247 14848780925442370219542371)
                ·
                  refine ⟨22273171388163555329313557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14848780925442370219542371 22273171388163555329313557)
                  ·
                    refine ⟨1044054908820166656061573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22273171388163555329313557 1044054908820166656061573)
                    ·
                      rfl

theorem cell23_6099869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_6099869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099869 prefixEnd_6099869 := by exact prefixLift 6099869
  have htrace : WordTrace (prefixWord ++ tailWord_6099869) baseStart_6099869 baseEnd_6099869 := by
    simpa [prefixWord, tailWord_6099869, baseEnd_6099869] using wordTrace_append hprefix tailTrace_6099869
  have hstable : (prefixWord ++ tailWord_6099869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099869).length < 2 ^ (prefixWord ++ tailWord_6099869).sum := by decide
  have hdescent : baseEnd_6099869 < baseStart_6099869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099872 : List Nat := [2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 6]
def baseStart_6099872 : Nat := 118140960795 + 6099872 * 2 ^ 59
def prefixEnd_6099872 : Nat := 4983230072969 + 3 ^ 40 * 6099872 * 2
def baseEnd_6099872 : Nat := 3132166266902463456447205

theorem tailTrace_6099872 : CollatzResearch.WordTrace tailWord_6099872 prefixEnd_6099872 3132166266902463456447205 := by
  unfold tailWord_6099872
  simp only [CollatzResearch.WordTrace]
  refine ⟨111240304678606497021374935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148320406238141996028499913 111240304678606497021374935)
  ·
    refine ⟨166860457017909745532062403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111240304678606497021374935 166860457017909745532062403)
    ·
      refine ⟨250290685526864618298093605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166860457017909745532062403 250290685526864618298093605)
      ·
        refine ⟨46929503536287115930892551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 250290685526864618298093605 46929503536287115930892551)
        ·
          refine ⟨70394255304430673896338827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46929503536287115930892551 70394255304430673896338827)
          ·
            refine ⟨105591382956646010844508241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70394255304430673896338827 105591382956646010844508241)
            ·
              refine ⟨79193537217484508133381181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105591382956646010844508241 79193537217484508133381181)
              ·
                refine ⟨29697576456556690550017943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79193537217484508133381181 29697576456556690550017943)
                ·
                  refine ⟨44546364684835035825026915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29697576456556690550017943 44546364684835035825026915)
                  ·
                    refine ⟨66819547027252553737540373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44546364684835035825026915 66819547027252553737540373)
                    ·
                      refine ⟨3132166266902463456447205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66819547027252553737540373 3132166266902463456447205)
                      ·
                        rfl

theorem cell23_6099872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_6099872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099872 prefixEnd_6099872 := by exact prefixLift 6099872
  have htrace : WordTrace (prefixWord ++ tailWord_6099872) baseStart_6099872 baseEnd_6099872 := by
    simpa [prefixWord, tailWord_6099872, baseEnd_6099872] using wordTrace_append hprefix tailTrace_6099872
  have hstable : (prefixWord ++ tailWord_6099872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099872).length < 2 ^ (prefixWord ++ tailWord_6099872).sum := by decide
  have hdescent : baseEnd_6099872 < baseStart_6099872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099896 : List Nat := [2, 1, 2, 1, 2, 5, 1, 3, 1, 2, 3]
def baseStart_6099896 : Nat := 118140960795 + 6099896 * 2 ^ 59
def prefixEnd_6099896 : Nat := 4983230072969 + 3 ^ 40 * 6099896 * 2
def baseEnd_6099896 : Nat := 3132178590438171362547095

theorem tailTrace_6099896 : CollatzResearch.WordTrace tailWord_6099896 prefixEnd_6099896 3132178590438171362547095 := by
  unfold tailWord_6099896
  simp only [CollatzResearch.WordTrace]
  refine ⟨111240742354563023070811771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148320989806084030761082361 111240742354563023070811771)
  ·
    refine ⟨166861113531844534606217657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111240742354563023070811771 166861113531844534606217657)
    ·
      refine ⟨125145835148883400954663243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166861113531844534606217657 125145835148883400954663243)
      ·
        refine ⟨187718752723325101431994865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125145835148883400954663243 187718752723325101431994865)
        ·
          refine ⟨140789064542493826073996149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187718752723325101431994865 140789064542493826073996149)
          ·
            refine ⟨13198974800858796194437139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140789064542493826073996149 13198974800858796194437139)
            ·
              refine ⟨19798462201288194291655709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13198974800858796194437139 19798462201288194291655709)
              ·
                refine ⟨7424423325483072859370891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19798462201288194291655709 7424423325483072859370891)
                ·
                  refine ⟨11136634988224609289056337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7424423325483072859370891 11136634988224609289056337)
                  ·
                    refine ⟨8352476241168456966792253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11136634988224609289056337 8352476241168456966792253)
                    ·
                      refine ⟨3132178590438171362547095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8352476241168456966792253 3132178590438171362547095)
                      ·
                        rfl

theorem cell23_6099896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 1, 2, 3].length) (baseStart_6099896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099896 prefixEnd_6099896 := by exact prefixLift 6099896
  have htrace : WordTrace (prefixWord ++ tailWord_6099896) baseStart_6099896 baseEnd_6099896 := by
    simpa [prefixWord, tailWord_6099896, baseEnd_6099896] using wordTrace_append hprefix tailTrace_6099896
  have hstable : (prefixWord ++ tailWord_6099896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099896).length < 2 ^ (prefixWord ++ tailWord_6099896).sum := by decide
  have hdescent : baseEnd_6099896 < baseStart_6099896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6099953 : List Nat := [1, 2, 2, 2, 4, 1, 2, 3, 1, 3, 2]
def baseStart_6099953 : Nat := 118140960795 + 6099953 * 2 ^ 59
def prefixEnd_6099953 : Nat := 4983230072969 + 3 ^ 40 * 6099953 * 2
def baseEnd_6099953 : Nat := 3132207858835477639534333

theorem tailTrace_6099953 : CollatzResearch.WordTrace tailWord_6099953 prefixEnd_6099953 3132207858835477639534333 := by
  unfold tailWord_6099953
  simp only [CollatzResearch.WordTrace]
  refine ⟨222483563669919544876448513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148322375779946363250965675 222483563669919544876448513)
  ·
    refine ⟨166862672752439658657336385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222483563669919544876448513 166862672752439658657336385)
    ·
      refine ⟨125147004564329743993002289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166862672752439658657336385 125147004564329743993002289)
      ·
        refine ⟨93860253423247307994751717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125147004564329743993002289 93860253423247307994751717)
        ·
          refine ⟨17598797516858870249015947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93860253423247307994751717 17598797516858870249015947)
          ·
            refine ⟨26398196275288305373523921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17598797516858870249015947 26398196275288305373523921)
            ·
              refine ⟨19798647206466229030142941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26398196275288305373523921 19798647206466229030142941)
              ·
                refine ⟨7424492702424835886303603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19798647206466229030142941 7424492702424835886303603)
                ·
                  refine ⟨11136739053637253829455405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7424492702424835886303603 11136739053637253829455405)
                  ·
                    refine ⟨4176277145113970186045777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11136739053637253829455405 4176277145113970186045777)
                    ·
                      refine ⟨3132207858835477639534333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4176277145113970186045777 3132207858835477639534333)
                      ·
                        rfl

theorem cell23_6099953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 3, 2].length) (baseStart_6099953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6099953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6099953 prefixEnd_6099953 := by exact prefixLift 6099953
  have htrace : WordTrace (prefixWord ++ tailWord_6099953) baseStart_6099953 baseEnd_6099953 := by
    simpa [prefixWord, tailWord_6099953, baseEnd_6099953] using wordTrace_append hprefix tailTrace_6099953
  have hstable : (prefixWord ++ tailWord_6099953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6099953).length < 2 ^ (prefixWord ++ tailWord_6099953).sum := by decide
  have hdescent : baseEnd_6099953 < baseStart_6099953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6099953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100000 : List Nat := [2, 1, 1, 7, 1, 1, 1, 2, 1, 4, 2]
def baseStart_6100000 : Nat := 118140960795 + 6100000 * 2 ^ 59
def prefixEnd_6100000 : Nat := 4983230072969 + 3 ^ 40 * 6100000 * 2
def baseEnd_6100000 : Nat := 3132231992426238955646617

theorem tailTrace_6100000 : CollatzResearch.WordTrace tailWord_6100000 prefixEnd_6100000 3132231992426238955646617 := by
  unfold tailWord_6100000
  simp only [CollatzResearch.WordTrace]
  refine ⟨111242638950374635951704727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148323518600499514602272969 111242638950374635951704727)
  ·
    refine ⟨166863958425561953927557091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111242638950374635951704727 166863958425561953927557091)
    ·
      refine ⟨250295937638342930891335637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166863958425561953927557091 250295937638342930891335637)
      ·
        refine ⟨5866311038398662442765679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 250295937638342930891335637 5866311038398662442765679)
        ·
          refine ⟨8799466557597993664148519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5866311038398662442765679 8799466557597993664148519)
          ·
            refine ⟨13199199836396990496222779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8799466557597993664148519 13199199836396990496222779)
            ·
              refine ⟨19798799754595485744334169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13199199836396990496222779 19798799754595485744334169)
              ·
                refine ⟨14849099815946614308250627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19798799754595485744334169 14849099815946614308250627)
                ·
                  refine ⟨22273649723919921462375941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14849099815946614308250627 22273649723919921462375941)
                  ·
                    refine ⟨4176309323234985274195489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22273649723919921462375941 4176309323234985274195489)
                    ·
                      refine ⟨3132231992426238955646617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4176309323234985274195489 3132231992426238955646617)
                      ·
                        rfl

theorem cell23_6100000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_6100000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100000 prefixEnd_6100000 := by exact prefixLift 6100000
  have htrace : WordTrace (prefixWord ++ tailWord_6100000) baseStart_6100000 baseEnd_6100000 := by
    simpa [prefixWord, tailWord_6100000, baseEnd_6100000] using wordTrace_append hprefix tailTrace_6100000
  have hstable : (prefixWord ++ tailWord_6100000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100000).length < 2 ^ (prefixWord ++ tailWord_6100000).sum := by decide
  have hdescent : baseEnd_6100000 < baseStart_6100000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100026 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2]
def baseStart_6100026 : Nat := 118140960795 + 6100026 * 2 ^ 59
def prefixEnd_6100026 : Nat := 4983230072969 + 3 ^ 40 * 6100026 * 2
def baseEnd_6100026 : Nat := 3132245342923255853921497

theorem tailTrace_6100026 : CollatzResearch.WordTrace tailWord_6100026 prefixEnd_6100026 3132245342923255853921497 := by
  unfold tailWord_6100026
  simp only [CollatzResearch.WordTrace]
  refine ⟨55621556549663769585963983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148324150799103385562570621 55621556549663769585963983)
  ·
    refine ⟨83432334824495654378945975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55621556549663769585963983 83432334824495654378945975)
    ·
      refine ⟨125148502236743481568418963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83432334824495654378945975 125148502236743481568418963)
      ·
        refine ⟨187722753355115222352628445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125148502236743481568418963 187722753355115222352628445)
        ·
          refine ⟨70396032508168208382235667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187722753355115222352628445 70396032508168208382235667)
          ·
            refine ⟨105594048762252312573353501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70396032508168208382235667 105594048762252312573353501)
            ·
              refine ⟨39597768285844617215007563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105594048762252312573353501 39597768285844617215007563)
              ·
                refine ⟨59396652428766925822511345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39597768285844617215007563 59396652428766925822511345)
                ·
                  refine ⟨44547489321575194366883509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59396652428766925822511345 44547489321575194366883509)
                  ·
                    refine ⟨4176327123897674471895329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44547489321575194366883509 4176327123897674471895329)
                    ·
                      refine ⟨3132245342923255853921497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4176327123897674471895329 3132245342923255853921497)
                      ·
                        rfl

theorem cell23_6100026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2].length) (baseStart_6100026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100026 prefixEnd_6100026 := by exact prefixLift 6100026
  have htrace : WordTrace (prefixWord ++ tailWord_6100026) baseStart_6100026 baseEnd_6100026 := by
    simpa [prefixWord, tailWord_6100026, baseEnd_6100026] using wordTrace_append hprefix tailTrace_6100026
  have hstable : (prefixWord ++ tailWord_6100026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100026).length < 2 ^ (prefixWord ++ tailWord_6100026).sum := by decide
  have hdescent : baseEnd_6100026 < baseStart_6100026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100033 : List Nat := [1, 2, 5, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_6100033 : Nat := 118140960795 + 6100033 * 2 ^ 59
def prefixEnd_6100033 : Nat := 4983230072969 + 3 ^ 40 * 6100033 * 2
def baseEnd_6100033 : Nat := 3132248937287837326533965

theorem tailTrace_6100033 : CollatzResearch.WordTrace tailWord_6100033 prefixEnd_6100033 3132248937287837326533965 := by
  unfold tailWord_6100033
  simp only [CollatzResearch.WordTrace]
  refine ⟨222486481509629718539360753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148324321006419812359573835 222486481509629718539360753)
  ·
    refine ⟨166864861132222288904520565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222486481509629718539360753 166864861132222288904520565)
    ·
      refine ⟨15643580731145839584798803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166864861132222288904520565 15643580731145839584798803)
      ·
        refine ⟨23465371096718759377198205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15643580731145839584798803 23465371096718759377198205)
        ·
          refine ⟨8799514161269534766449327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23465371096718759377198205 8799514161269534766449327)
          ·
            refine ⟨13199271241904302149673991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8799514161269534766449327 13199271241904302149673991)
            ·
              refine ⟨19798906862856453224510987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13199271241904302149673991 19798906862856453224510987)
              ·
                refine ⟨29698360294284679836766481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19798906862856453224510987 29698360294284679836766481)
                ·
                  refine ⟨22273770220713509877574861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29698360294284679836766481 22273770220713509877574861)
                  ·
                    refine ⟨8352663832767566204090573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22273770220713509877574861 8352663832767566204090573)
                    ·
                      refine ⟨3132248937287837326533965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8352663832767566204090573 3132248937287837326533965)
                      ·
                        rfl

theorem cell23_6100033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_6100033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100033 prefixEnd_6100033 := by exact prefixLift 6100033
  have htrace : WordTrace (prefixWord ++ tailWord_6100033) baseStart_6100033 baseEnd_6100033 := by
    simpa [prefixWord, tailWord_6100033, baseEnd_6100033] using wordTrace_append hprefix tailTrace_6100033
  have hstable : (prefixWord ++ tailWord_6100033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100033).length < 2 ^ (prefixWord ++ tailWord_6100033).sum := by decide
  have hdescent : baseEnd_6100033 < baseStart_6100033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100056 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 1, 6, 2]
def baseStart_6100056 : Nat := 118140960795 + 6100056 * 2 ^ 59
def prefixEnd_6100056 : Nat := 4983230072969 + 3 ^ 40 * 6100056 * 2
def baseEnd_6100056 : Nat := 3132260747342890736546359

theorem tailTrace_6100056 : CollatzResearch.WordTrace tailWord_6100056 prefixEnd_6100056 3132260747342890736546359 := by
  unfold tailWord_6100056
  simp only [CollatzResearch.WordTrace]
  refine ⟨111243660194273196733724011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148324880259030928978298681 111243660194273196733724011)
  ·
    refine ⟨166865490291409795100586017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111243660194273196733724011 166865490291409795100586017)
    ·
      refine ⟨125149117718557346325439513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166865490291409795100586017 125149117718557346325439513)
      ·
        refine ⟨93861838288918009744079635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125149117718557346325439513 93861838288918009744079635)
        ·
          refine ⟨140792757433377014616119453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93861838288918009744079635 140792757433377014616119453)
          ·
            refine ⟨52797284037516380481044795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140792757433377014616119453 52797284037516380481044795)
            ·
              refine ⟨79195926056274570721567193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52797284037516380481044795 79195926056274570721567193)
              ·
                refine ⟨59396944542205928041175395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79195926056274570721567193 59396944542205928041175395)
                ·
                  refine ⟨89095416813308892061763093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59396944542205928041175395 89095416813308892061763093)
                  ·
                    refine ⟨4176347663123854315395145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89095416813308892061763093 4176347663123854315395145)
                    ·
                      refine ⟨3132260747342890736546359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4176347663123854315395145 3132260747342890736546359)
                      ·
                        rfl

theorem cell23_6100056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 1, 6, 2].length) (baseStart_6100056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100056 prefixEnd_6100056 := by exact prefixLift 6100056
  have htrace : WordTrace (prefixWord ++ tailWord_6100056) baseStart_6100056 baseEnd_6100056 := by
    simpa [prefixWord, tailWord_6100056, baseEnd_6100056] using wordTrace_append hprefix tailTrace_6100056
  have hstable : (prefixWord ++ tailWord_6100056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100056).length < 2 ^ (prefixWord ++ tailWord_6100056).sum := by decide
  have hdescent : baseEnd_6100056 < baseStart_6100056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100069 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 1, 3, 6]
def baseStart_6100069 : Nat := 118140960795 + 6100069 * 2 ^ 59
def prefixEnd_6100069 : Nat := 4983230072969 + 3 ^ 40 * 6100069 * 2
def baseEnd_6100069 : Nat := 3132267422591399185683799

theorem tailTrace_6100069 : CollatzResearch.WordTrace tailWord_6100069 prefixEnd_6100069 3132267422591399185683799 := by
  unfold tailWord_6100069
  simp only [CollatzResearch.WordTrace]
  refine ⟨222487794537499296687671261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148325196358332864458447507 222487794537499296687671261)
  ·
    refine ⟨83432922951562236257876723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222487794537499296687671261 83432922951562236257876723)
    ·
      refine ⟨125149384427343354386815085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83432922951562236257876723 125149384427343354386815085)
      ·
        refine ⟨46931019160253757895055657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125149384427343354386815085 46931019160253757895055657)
        ·
          refine ⟨35198264370190318421291743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46931019160253757895055657 35198264370190318421291743)
          ·
            refine ⟨52797396555285477631937615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35198264370190318421291743 52797396555285477631937615)
            ·
              refine ⟨79196094832928216447906423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52797396555285477631937615 79196094832928216447906423)
              ·
                refine ⟨118794142249392324671859635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79196094832928216447906423 118794142249392324671859635)
                ·
                  refine ⟨178191213374088487007789453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118794142249392324671859635 178191213374088487007789453)
                  ·
                    refine ⟨66821705015283182627921045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 178191213374088487007789453 66821705015283182627921045)
                    ·
                      refine ⟨3132267422591399185683799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66821705015283182627921045 3132267422591399185683799)
                      ·
                        rfl

theorem cell23_6100069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_6100069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100069 prefixEnd_6100069 := by exact prefixLift 6100069
  have htrace : WordTrace (prefixWord ++ tailWord_6100069) baseStart_6100069 baseEnd_6100069 := by
    simpa [prefixWord, tailWord_6100069, baseEnd_6100069] using wordTrace_append hprefix tailTrace_6100069
  have hstable : (prefixWord ++ tailWord_6100069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100069).length < 2 ^ (prefixWord ++ tailWord_6100069).sum := by decide
  have hdescent : baseEnd_6100069 < baseStart_6100069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100076 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 3]
def baseStart_6100076 : Nat := 118140960795 + 6100076 * 2 ^ 59
def prefixEnd_6100076 : Nat := 4983230072969 + 3 ^ 40 * 6100076 * 2
def baseEnd_6100076 : Nat := 3132271016955980658296267

theorem tailTrace_6100076 : CollatzResearch.WordTrace tailWord_6100076 prefixEnd_6100076 3132271016955980658296267 := by
  unfold tailWord_6100076
  simp only [CollatzResearch.WordTrace]
  refine ⟨111244024924236968441588041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148325366565649291255450721 111244024924236968441588041)
  ·
    refine ⟨83433018693177726331191031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111244024924236968441588041 83433018693177726331191031)
    ·
      refine ⟨125149528039766589496786547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83433018693177726331191031 125149528039766589496786547)
      ·
        refine ⟨187724292059649884245179821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125149528039766589496786547 187724292059649884245179821)
        ·
          refine ⟨70396609522368706591942433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187724292059649884245179821 70396609522368706591942433)
          ·
            refine ⟨52797457141776529943956825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70396609522368706591942433 52797457141776529943956825)
            ·
              refine ⟨39598092856332397457967619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52797457141776529943956825 39598092856332397457967619)
              ·
                refine ⟨59397139284498596186951429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39598092856332397457967619 59397139284498596186951429)
                ·
                  refine ⟨11136963615843486785053393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59397139284498596186951429 11136963615843486785053393)
                  ·
                    refine ⟨8352722711882615088790045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11136963615843486785053393 8352722711882615088790045)
                    ·
                      refine ⟨3132271016955980658296267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8352722711882615088790045 3132271016955980658296267)
                      ·
                        rfl

theorem cell23_6100076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 3].length) (baseStart_6100076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100076 prefixEnd_6100076 := by exact prefixLift 6100076
  have htrace : WordTrace (prefixWord ++ tailWord_6100076) baseStart_6100076 baseEnd_6100076 := by
    simpa [prefixWord, tailWord_6100076, baseEnd_6100076] using wordTrace_append hprefix tailTrace_6100076
  have hstable : (prefixWord ++ tailWord_6100076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100076).length < 2 ^ (prefixWord ++ tailWord_6100076).sum := by decide
  have hdescent : baseEnd_6100076 < baseStart_6100076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100079 : List Nat := [1, 1, 2, 1, 3, 3, 3, 1, 8]
def baseStart_6100079 : Nat := 118140960795 + 6100079 * 2 ^ 59
def prefixEnd_6100079 : Nat := 4983230072969 + 3 ^ 40 * 6100079 * 2
def baseEnd_6100079 : Nat := 348030284155327127395417

theorem tailTrace_6100079 : CollatzResearch.WordTrace tailWord_6100079 prefixEnd_6100079 348030284155327127395417 := by
  unfold tailWord_6100079
  simp only [CollatzResearch.WordTrace]
  refine ⟨222488159267463068395535291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148325439511642045597023527 222488159267463068395535291)
  ·
    refine ⟨333732238901194602593302937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222488159267463068395535291 333732238901194602593302937)
    ·
      refine ⟨250299179175895951944977203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333732238901194602593302937 250299179175895951944977203)
      ·
        refine ⟨375448768763843927917465805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250299179175895951944977203 375448768763843927917465805)
        ·
          refine ⟨140793288286441472969049677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 375448768763843927917465805 140793288286441472969049677)
          ·
            refine ⟨52797483107415552363393629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140793288286441472969049677 52797483107415552363393629)
            ·
              refine ⟨19799056165280832136272611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52797483107415552363393629 19799056165280832136272611)
              ·
                refine ⟨29698584247921248204408917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19799056165280832136272611 29698584247921248204408917)
                ·
                  refine ⟨348030284155327127395417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29698584247921248204408917 348030284155327127395417)
                  ·
                    rfl

theorem cell23_6100079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 8].length) (baseStart_6100079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100079 prefixEnd_6100079 := by exact prefixLift 6100079
  have htrace : WordTrace (prefixWord ++ tailWord_6100079) baseStart_6100079 baseEnd_6100079 := by
    simpa [prefixWord, tailWord_6100079, baseEnd_6100079] using wordTrace_append hprefix tailTrace_6100079
  have hstable : (prefixWord ++ tailWord_6100079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100079).length < 2 ^ (prefixWord ++ tailWord_6100079).sum := by decide
  have hdescent : baseEnd_6100079 < baseStart_6100079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100086 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_6100086 : Nat := 118140960795 + 6100086 * 2 ^ 59
def prefixEnd_6100086 : Nat := 4983230072969 + 3 ^ 40 * 6100086 * 2
def baseEnd_6100086 : Nat := 3132276151762525619171221

theorem tailTrace_6100086 : CollatzResearch.WordTrace tailWord_6100086 prefixEnd_6100086 3132276151762525619171221 := by
  unfold tailWord_6100086
  simp only [CollatzResearch.WordTrace]
  refine ⟨13905525911152356786940007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148325609718958472394026741 13905525911152356786940007)
  ·
    refine ⟨20858288866728535180410011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13905525911152356786940007 20858288866728535180410011)
    ·
      refine ⟨31287433300092802770615017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20858288866728535180410011 31287433300092802770615017)
      ·
        refine ⟨23465574975069602077961263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31287433300092802770615017 23465574975069602077961263)
        ·
          refine ⟨35198362462604403116941895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23465574975069602077961263 35198362462604403116941895)
          ·
            refine ⟨52797543693906604675412843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35198362462604403116941895 52797543693906604675412843)
            ·
              refine ⟨79196315540859907013119265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52797543693906604675412843 79196315540859907013119265)
              ·
                refine ⟨59397236655644930259839449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79196315540859907013119265 59397236655644930259839449)
                ·
                  refine ⟨44547927491733697694879587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59397236655644930259839449 44547927491733697694879587)
                  ·
                    refine ⟨66821891237600546542319381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44547927491733697694879587 66821891237600546542319381)
                    ·
                      refine ⟨3132276151762525619171221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66821891237600546542319381 3132276151762525619171221)
                      ·
                        rfl

theorem cell23_6100086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_6100086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100086 prefixEnd_6100086 := by exact prefixLift 6100086
  have htrace : WordTrace (prefixWord ++ tailWord_6100086) baseStart_6100086 baseEnd_6100086 := by
    simpa [prefixWord, tailWord_6100086, baseEnd_6100086] using wordTrace_append hprefix tailTrace_6100086
  have hstable : (prefixWord ++ tailWord_6100086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100086).length < 2 ^ (prefixWord ++ tailWord_6100086).sum := by decide
  have hdescent : baseEnd_6100086 < baseStart_6100086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100099 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 6]
def baseStart_6100099 : Nat := 118140960795 + 6100099 * 2 ^ 59
def prefixEnd_6100099 : Nat := 4983230072969 + 3 ^ 40 * 6100099 * 2
def baseEnd_6100099 : Nat := 3132282827011034068308661

theorem tailTrace_6100099 : CollatzResearch.WordTrace tailWord_6100099 prefixEnd_6100099 3132282827011034068308661 := by
  unfold tailWord_6100099
  simp only [CollatzResearch.WordTrace]
  refine ⟨222488888727390611811263351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148325925818260407874175567 222488888727390611811263351)
  ·
    refine ⟨333733333091085917716895027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222488888727390611811263351 333733333091085917716895027)
    ·
      refine ⟨500599999636628876575342541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333733333091085917716895027 500599999636628876575342541)
      ·
        refine ⟨187724999863735828715753453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 500599999636628876575342541 187724999863735828715753453)
        ·
          refine ⟨70396874948900935768407545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187724999863735828715753453 70396874948900935768407545)
          ·
            refine ⟨52797656211675701826305659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70396874948900935768407545 52797656211675701826305659)
            ·
              refine ⟨79196484317513552739458489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52797656211675701826305659 79196484317513552739458489)
              ·
                refine ⟨59397363238135164554593867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79196484317513552739458489 59397363238135164554593867)
                ·
                  refine ⟨89096044857202746831890801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59397363238135164554593867 89096044857202746831890801)
                  ·
                    refine ⟨66822033642902060123918101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89096044857202746831890801 66822033642902060123918101)
                    ·
                      refine ⟨3132282827011034068308661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66822033642902060123918101 3132282827011034068308661)
                      ·
                        rfl

theorem cell23_6100099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_6100099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100099 prefixEnd_6100099 := by exact prefixLift 6100099
  have htrace : WordTrace (prefixWord ++ tailWord_6100099) baseStart_6100099 baseEnd_6100099 := by
    simpa [prefixWord, tailWord_6100099, baseEnd_6100099] using wordTrace_append hprefix tailTrace_6100099
  have hstable : (prefixWord ++ tailWord_6100099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100099).length < 2 ^ (prefixWord ++ tailWord_6100099).sum := by decide
  have hdescent : baseEnd_6100099 < baseStart_6100099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100106 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 2, 5, 3]
def baseStart_6100106 : Nat := 118140960795 + 6100106 * 2 ^ 59
def prefixEnd_6100106 : Nat := 4983230072969 + 3 ^ 40 * 6100106 * 2
def baseEnd_6100106 : Nat := 3132286421375615540921129

theorem tailTrace_6100106 : CollatzResearch.WordTrace tailWord_6100106 prefixEnd_6100106 3132286421375615540921129 := by
  unfold tailWord_6100106
  simp only [CollatzResearch.WordTrace]
  refine ⟨55622286009591313001692043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148326096025576834671178781 55622286009591313001692043)
  ·
    refine ⟨83433429014386969502538065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55622286009591313001692043 83433429014386969502538065)
    ·
      refine ⟨62575071760790227126903549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83433429014386969502538065 62575071760790227126903549)
      ·
        refine ⟨23465651910296335172588831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62575071760790227126903549 23465651910296335172588831)
        ·
          refine ⟨35198477865444502758883247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23465651910296335172588831 35198477865444502758883247)
          ·
            refine ⟨52797716798166754138324871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35198477865444502758883247 52797716798166754138324871)
            ·
              refine ⟨79196575197250131207487307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52797716798166754138324871 79196575197250131207487307)
              ·
                refine ⟨118794862795875196811230961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79196575197250131207487307 118794862795875196811230961)
                ·
                  refine ⟨89096147096906397608423221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118794862795875196811230961 89096147096906397608423221)
                  ·
                    refine ⟨8352763790334974775789677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89096147096906397608423221 8352763790334974775789677)
                    ·
                      refine ⟨3132286421375615540921129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8352763790334974775789677 3132286421375615540921129)
                      ·
                        rfl

theorem cell23_6100106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_6100106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100106 prefixEnd_6100106 := by exact prefixLift 6100106
  have htrace : WordTrace (prefixWord ++ tailWord_6100106) baseStart_6100106 baseEnd_6100106 := by
    simpa [prefixWord, tailWord_6100106, baseEnd_6100106] using wordTrace_append hprefix tailTrace_6100106
  have hstable : (prefixWord ++ tailWord_6100106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100106).length < 2 ^ (prefixWord ++ tailWord_6100106).sum := by decide
  have hdescent : baseEnd_6100106 < baseStart_6100106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100133 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 4, 3, 2]
def baseStart_6100133 : Nat := 118140960795 + 6100133 * 2 ^ 59
def prefixEnd_6100133 : Nat := 4983230072969 + 3 ^ 40 * 6100133 * 2
def baseEnd_6100133 : Nat := 3132300285353286935283505

theorem tailTrace_6100133 : CollatzResearch.WordTrace tailWord_6100133 prefixEnd_6100133 3132300285353286935283505 := by
  unfold tailWord_6100133
  simp only [CollatzResearch.WordTrace]
  refine ⟨222490128809267435618001053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148326752539511623745334035 222490128809267435618001053)
  ·
    refine ⟨83433798303475288356750395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222490128809267435618001053 83433798303475288356750395)
    ·
      refine ⟨125150697455212932535125593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83433798303475288356750395 125150697455212932535125593)
      ·
        refine ⟨93863023091409699401344195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125150697455212932535125593 93863023091409699401344195)
        ·
          refine ⟨140794534637114549102016293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93863023091409699401344195 140794534637114549102016293)
          ·
            refine ⟨26398975244458977956628055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140794534637114549102016293 26398975244458977956628055)
            ·
              refine ⟨39598462866688466934942083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26398975244458977956628055 39598462866688466934942083)
              ·
                refine ⟨59397694300032700402413125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39598462866688466934942083 59397694300032700402413125)
                ·
                  refine ⟨11137067681256131325452461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59397694300032700402413125 11137067681256131325452461)
                  ·
                    refine ⟨4176400380471049247044673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11137067681256131325452461 4176400380471049247044673)
                    ·
                      refine ⟨3132300285353286935283505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4176400380471049247044673 3132300285353286935283505)
                      ·
                        rfl

theorem cell23_6100133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 3, 2].length) (baseStart_6100133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100133 prefixEnd_6100133 := by exact prefixLift 6100133
  have htrace : WordTrace (prefixWord ++ tailWord_6100133) baseStart_6100133 baseEnd_6100133 := by
    simpa [prefixWord, tailWord_6100133, baseEnd_6100133] using wordTrace_append hprefix tailTrace_6100133
  have hstable : (prefixWord ++ tailWord_6100133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100133).length < 2 ^ (prefixWord ++ tailWord_6100133).sum := by decide
  have hdescent : baseEnd_6100133 < baseStart_6100133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100160 : List Nat := [2, 1, 1, 2, 6, 2, 1, 2, 1, 5]
def baseStart_6100160 : Nat := 118140960795 + 6100160 * 2 ^ 59
def prefixEnd_6100160 : Nat := 4983230072969 + 3 ^ 40 * 6100160 * 2
def baseEnd_6100160 : Nat := 1044104716443652776548627

theorem tailTrace_6100160 : CollatzResearch.WordTrace tailWord_6100160 prefixEnd_6100160 1044104716443652776548627 := by
  unfold tailWord_6100160
  simp only [CollatzResearch.WordTrace]
  refine ⟨111245556790084809614616967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148327409053446412819489289 111245556790084809614616967)
  ·
    refine ⟨166868335185127214421925451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111245556790084809614616967 166868335185127214421925451)
    ·
      refine ⟨250302502777690821632888177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166868335185127214421925451 250302502777690821632888177)
      ·
        refine ⟨187726877083268116224666133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250302502777690821632888177 187726877083268116224666133)
        ·
          refine ⟨8799697363278192948031225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 187726877083268116224666133 8799697363278192948031225)
          ·
            refine ⟨6599773022458644711023419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8799697363278192948031225 6599773022458644711023419)
            ·
              refine ⟨9899659533687967066535129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6599773022458644711023419 9899659533687967066535129)
              ·
                refine ⟨7424744650265975299901347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9899659533687967066535129 7424744650265975299901347)
                ·
                  refine ⟨11137116975398962949852021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7424744650265975299901347 11137116975398962949852021)
                  ·
                    refine ⟨1044104716443652776548627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11137116975398962949852021 1044104716443652776548627)
                    ·
                      rfl

theorem cell23_6100160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 1, 5].length) (baseStart_6100160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100160 prefixEnd_6100160 := by exact prefixLift 6100160
  have htrace : WordTrace (prefixWord ++ tailWord_6100160) baseStart_6100160 baseEnd_6100160 := by
    simpa [prefixWord, tailWord_6100160, baseEnd_6100160] using wordTrace_append hprefix tailTrace_6100160
  have hstable : (prefixWord ++ tailWord_6100160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100160).length < 2 ^ (prefixWord ++ tailWord_6100160).sum := by decide
  have hdescent : baseEnd_6100160 < baseStart_6100160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100183 : List Nat := [1, 1, 3, 2, 1, 2, 2, 5, 1, 2, 3]
def baseStart_6100183 : Nat := 118140960795 + 6100183 * 2 ^ 59
def prefixEnd_6100183 : Nat := 4983230072969 + 3 ^ 40 * 6100183 * 2
def baseEnd_6100183 : Nat := 3132325959386011739658275

theorem tailTrace_6100183 : CollatzResearch.WordTrace tailWord_6100183 prefixEnd_6100183 3132325959386011739658275 := by
  unfold tailWord_6100183
  simp only [CollatzResearch.WordTrace]
  refine ⟨222491952459086294157321203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148327968306057529438214135 222491952459086294157321203)
  ·
    refine ⟨333737928688629441235981805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222491952459086294157321203 333737928688629441235981805)
    ·
      refine ⟨125151723258236040463493177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333737928688629441235981805 125151723258236040463493177)
      ·
        refine ⟨93863792443677030347619883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125151723258236040463493177 93863792443677030347619883)
        ·
          refine ⟨140795688665515545521429825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93863792443677030347619883 140795688665515545521429825)
          ·
            refine ⟨105596766499136659141072369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140795688665515545521429825 105596766499136659141072369)
            ·
              refine ⟨79197574874352494355804277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105596766499136659141072369 79197574874352494355804277)
              ·
                refine ⟨7424772644470546345856651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79197574874352494355804277 7424772644470546345856651)
                ·
                  refine ⟨11137158966705819518784977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7424772644470546345856651 11137158966705819518784977)
                  ·
                    refine ⟨8352869225029364639088733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11137158966705819518784977 8352869225029364639088733)
                    ·
                      refine ⟨3132325959386011739658275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8352869225029364639088733 3132325959386011739658275)
                      ·
                        rfl

theorem cell23_6100183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_6100183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100183 prefixEnd_6100183 := by exact prefixLift 6100183
  have htrace : WordTrace (prefixWord ++ tailWord_6100183) baseStart_6100183 baseEnd_6100183 := by
    simpa [prefixWord, tailWord_6100183, baseEnd_6100183] using wordTrace_append hprefix tailTrace_6100183
  have hstable : (prefixWord ++ tailWord_6100183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100183).length < 2 ^ (prefixWord ++ tailWord_6100183).sum := by decide
  have hdescent : baseEnd_6100183 < baseStart_6100183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100206 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_6100206 : Nat := 118140960795 + 6100206 * 2 ^ 59
def prefixEnd_6100206 : Nat := 4983230072969 + 3 ^ 40 * 6100206 * 2
def baseEnd_6100206 : Nat := 3132337769441065149670669

theorem tailTrace_6100206 : CollatzResearch.WordTrace tailWord_6100206 prefixEnd_6100206 3132337769441065149670669 := by
  unfold tailWord_6100206
  simp only [CollatzResearch.WordTrace]
  refine ⟨27811598917250371135676059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148328527558668646056938981 27811598917250371135676059)
  ·
    refine ⟨41717398375875556703514089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27811598917250371135676059 41717398375875556703514089)
    ·
      refine ⟨31288048781906667527635567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41717398375875556703514089 31288048781906667527635567)
      ·
        refine ⟨46932073172860001291453351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31288048781906667527635567 46932073172860001291453351)
        ·
          refine ⟨70398109759290001937180027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46932073172860001291453351 70398109759290001937180027)
          ·
            refine ⟨105597164638935002905770041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70398109759290001937180027 105597164638935002905770041)
            ·
              refine ⟨79197873479201252179327531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105597164638935002905770041 79197873479201252179327531)
              ·
                refine ⟨118796810218801878268991297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79197873479201252179327531 118796810218801878268991297)
                ·
                  refine ⟨89097607664101408701743473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118796810218801878268991297 89097607664101408701743473)
                  ·
                    refine ⟨66823205748076056526307605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89097607664101408701743473 66823205748076056526307605)
                    ·
                      refine ⟨3132337769441065149670669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66823205748076056526307605 3132337769441065149670669)
                      ·
                        rfl

theorem cell23_6100206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_6100206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100206 prefixEnd_6100206 := by exact prefixLift 6100206
  have htrace : WordTrace (prefixWord ++ tailWord_6100206) baseStart_6100206 baseEnd_6100206 := by
    simpa [prefixWord, tailWord_6100206, baseEnd_6100206] using wordTrace_append hprefix tailTrace_6100206
  have hstable : (prefixWord ++ tailWord_6100206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100206).length < 2 ^ (prefixWord ++ tailWord_6100206).sum := by decide
  have hdescent : baseEnd_6100206 < baseStart_6100206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100210 : List Nat := [3, 2, 1, 3, 3, 1, 2, 1, 1, 2, 4]
def baseStart_6100210 : Nat := 118140960795 + 6100210 * 2 ^ 59
def prefixEnd_6100210 : Nat := 4983230072969 + 3 ^ 40 * 6100210 * 2
def baseEnd_6100210 : Nat := 3132339823363683134020651

theorem tailTrace_6100210 : CollatzResearch.WordTrace tailWord_6100210 prefixEnd_6100210 3132339823363683134020651 := by
  unfold tailWord_6100210
  simp only [CollatzResearch.WordTrace]
  refine ⟨55623234307497119442138521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148328624819992318512369389 55623234307497119442138521)
  ·
    refine ⟨41717425730622839581603891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55623234307497119442138521 41717425730622839581603891)
    ·
      refine ⟨62576138595934259372405837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41717425730622839581603891 62576138595934259372405837)
      ·
        refine ⟨23466051973475347264652189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62576138595934259372405837 23466051973475347264652189)
        ·
          refine ⟨8799769490053255224244571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23466051973475347264652189 8799769490053255224244571)
          ·
            refine ⟨13199654235079882836366857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8799769490053255224244571 13199654235079882836366857)
            ·
              refine ⟨9899740676309912127275143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13199654235079882836366857 9899740676309912127275143)
              ·
                refine ⟨14849611014464868190912715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9899740676309912127275143 14849611014464868190912715)
                ·
                  refine ⟨22274416521697302286369073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14849611014464868190912715 22274416521697302286369073)
                  ·
                    refine ⟨16705812391272976714776805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22274416521697302286369073 16705812391272976714776805)
                    ·
                      refine ⟨3132339823363683134020651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16705812391272976714776805 3132339823363683134020651)
                      ·
                        rfl

theorem cell23_6100210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_6100210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100210 prefixEnd_6100210 := by exact prefixLift 6100210
  have htrace : WordTrace (prefixWord ++ tailWord_6100210) baseStart_6100210 baseEnd_6100210 := by
    simpa [prefixWord, tailWord_6100210, baseEnd_6100210] using wordTrace_append hprefix tailTrace_6100210
  have hstable : (prefixWord ++ tailWord_6100210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100210).length < 2 ^ (prefixWord ++ tailWord_6100210).sum := by decide
  have hdescent : baseEnd_6100210 < baseStart_6100210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100264 : List Nat := [2, 1, 5, 1, 2, 2, 3, 1, 2, 1, 3]
def baseStart_6100264 : Nat := 118140960795 + 6100264 * 2 ^ 59
def prefixEnd_6100264 : Nat := 4983230072969 + 3 ^ 40 * 6100264 * 2
def baseEnd_6100264 : Nat := 3132367551319025922745403

theorem tailTrace_6100264 : CollatzResearch.WordTrace tailWord_6100264 prefixEnd_6100264 3132367551319025922745403 := by
  unfold tailWord_6100264
  simp only [CollatzResearch.WordTrace]
  refine ⟨111247453385896422495509923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148329937847861896660679897 111247453385896422495509923)
  ·
    refine ⟨166871180078844633743264885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111247453385896422495509923 166871180078844633743264885)
    ·
      refine ⟨15644173132391684413431083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166871180078844633743264885 15644173132391684413431083)
      ·
        refine ⟨23466259698587526620146625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15644173132391684413431083 23466259698587526620146625)
        ·
          refine ⟨17599694773940644965109969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23466259698587526620146625 17599694773940644965109969)
          ·
            refine ⟨13199771080455483723832477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17599694773940644965109969 13199771080455483723832477)
            ·
              refine ⟨4949914155170806396437179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13199771080455483723832477 4949914155170806396437179)
              ·
                refine ⟨7424871232756209594655769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4949914155170806396437179 7424871232756209594655769)
                ·
                  refine ⟨5568653424567157195991827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7424871232756209594655769 5568653424567157195991827)
                  ·
                    refine ⟨8352980136850735793987741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5568653424567157195991827 8352980136850735793987741)
                    ·
                      refine ⟨3132367551319025922745403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8352980136850735793987741 3132367551319025922745403)
                      ·
                        rfl

theorem cell23_6100264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_6100264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100264 prefixEnd_6100264 := by exact prefixLift 6100264
  have htrace : WordTrace (prefixWord ++ tailWord_6100264) baseStart_6100264 baseEnd_6100264 := by
    simpa [prefixWord, tailWord_6100264, baseEnd_6100264] using wordTrace_append hprefix tailTrace_6100264
  have hstable : (prefixWord ++ tailWord_6100264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100264).length < 2 ^ (prefixWord ++ tailWord_6100264).sum := by decide
  have hdescent : baseEnd_6100264 < baseStart_6100264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100360 : List Nat := [2, 1, 3, 3, 1, 2, 2, 2, 2, 1, 4]
def baseStart_6100360 : Nat := 118140960795 + 6100360 * 2 ^ 59
def prefixEnd_6100360 : Nat := 4983230072969 + 3 ^ 40 * 6100360 * 2
def baseEnd_6100360 : Nat := 3132416845461857547144961

theorem tailTrace_6100360 : CollatzResearch.WordTrace tailWord_6100360 prefixEnd_6100360 3132416845461857547144961 := by
  unfold tailWord_6100360
  simp only [CollatzResearch.WordTrace]
  refine ⟨111249204089722526693257267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148332272119630035591009689 111249204089722526693257267)
  ·
    refine ⟨166873806134583790039885901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111249204089722526693257267 166873806134583790039885901)
    ·
      refine ⟨62577677300468921264957213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166873806134583790039885901 62577677300468921264957213)
      ·
        refine ⟨23466628987675845474358955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62577677300468921264957213 23466628987675845474358955)
        ·
          refine ⟨35199943481513768211538433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23466628987675845474358955 35199943481513768211538433)
          ·
            refine ⟨26399957611135326158653825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35199943481513768211538433 26399957611135326158653825)
            ·
              refine ⟨19799968208351494618990369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26399957611135326158653825 19799968208351494618990369)
              ·
                refine ⟨14849976156263620964242777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19799968208351494618990369 14849976156263620964242777)
                ·
                  refine ⟨11137482117197715723182083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14849976156263620964242777 11137482117197715723182083)
                  ·
                    refine ⟨16706223175796573584773125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11137482117197715723182083 16706223175796573584773125)
                    ·
                      refine ⟨3132416845461857547144961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16706223175796573584773125 3132416845461857547144961)
                      ·
                        rfl

theorem cell23_6100360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_6100360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100360 prefixEnd_6100360 := by exact prefixLift 6100360
  have htrace : WordTrace (prefixWord ++ tailWord_6100360) baseStart_6100360 baseEnd_6100360 := by
    simpa [prefixWord, tailWord_6100360, baseEnd_6100360] using wordTrace_append hprefix tailTrace_6100360
  have hstable : (prefixWord ++ tailWord_6100360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100360).length < 2 ^ (prefixWord ++ tailWord_6100360).sum := by decide
  have hdescent : baseEnd_6100360 < baseStart_6100360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100397 : List Nat := [1, 5, 2, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_6100397 : Nat := 118140960795 + 6100397 * 2 ^ 59
def prefixEnd_6100397 : Nat := 4983230072969 + 3 ^ 40 * 6100397 * 2
def baseEnd_6100397 : Nat := 3132435844246073902382291

theorem tailTrace_6100397 : CollatzResearch.WordTrace tailWord_6100397 prefixEnd_6100397 3132435844246073902382291 := by
  unfold tailWord_6100397
  simp only [CollatzResearch.WordTrace]
  refine ⟨222499757680311008705611445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148333171786874005803740963 222499757680311008705611445)
  ·
    refine ⟨20859352282529157066151073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 222499757680311008705611445 20859352282529157066151073)
    ·
      refine ⟨15644514211896867799613305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20859352282529157066151073 15644514211896867799613305)
      ·
        refine ⟨11733385658922650849709979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15644514211896867799613305 11733385658922650849709979)
        ·
          refine ⟨17600078488383976274564969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11733385658922650849709979 17600078488383976274564969)
          ·
            refine ⟨13200058866287982205923727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17600078488383976274564969 13200058866287982205923727)
            ·
              refine ⟨19800088299431973308885591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13200058866287982205923727 19800088299431973308885591)
              ·
                refine ⟨29700132449147959963328387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19800088299431973308885591 29700132449147959963328387)
                ·
                  refine ⟨44550198673721939944992581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29700132449147959963328387 44550198673721939944992581)
                  ·
                    refine ⟨8353162251322863739686109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44550198673721939944992581 8353162251322863739686109)
                    ·
                      refine ⟨3132435844246073902382291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8353162251322863739686109 3132435844246073902382291)
                      ·
                        rfl

theorem cell23_6100397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_6100397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100397 prefixEnd_6100397 := by exact prefixLift 6100397
  have htrace : WordTrace (prefixWord ++ tailWord_6100397) baseStart_6100397 baseEnd_6100397 := by
    simpa [prefixWord, tailWord_6100397, baseEnd_6100397] using wordTrace_append hprefix tailTrace_6100397
  have hstable : (prefixWord ++ tailWord_6100397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100397).length < 2 ^ (prefixWord ++ tailWord_6100397).sum := by decide
  have hdescent : baseEnd_6100397 < baseStart_6100397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100420 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_6100420 : Nat := 118140960795 + 6100420 * 2 ^ 59
def prefixEnd_6100420 : Nat := 4983230072969 + 3 ^ 40 * 6100420 * 2
def baseEnd_6100420 : Nat := 3132447654301127312394685

theorem tailTrace_6100420 : CollatzResearch.WordTrace tailWord_6100420 prefixEnd_6100420 3132447654301127312394685 := by
  unfold tailWord_6100420
  simp only [CollatzResearch.WordTrace]
  refine ⟨111250298279613841816849357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148333731039485122422465809 111250298279613841816849357)
  ·
    refine ⟨41718861854855190681318509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111250298279613841816849357 41718861854855190681318509)
    ·
      refine ⟨15644573195570696505494441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41718861854855190681318509 15644573195570696505494441)
      ·
        refine ⟨11733429896678022379120831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15644573195570696505494441 11733429896678022379120831)
        ·
          refine ⟨17600144845017033568681247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11733429896678022379120831 17600144845017033568681247)
          ·
            refine ⟨26400217267525550353021871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17600144845017033568681247 26400217267525550353021871)
            ·
              refine ⟨39600325901288325529532807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26400217267525550353021871 39600325901288325529532807)
              ·
                refine ⟨59400488851932488294299211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39600325901288325529532807 59400488851932488294299211)
                ·
                  refine ⟨89100733277898732441448817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59400488851932488294299211 89100733277898732441448817)
                  ·
                    refine ⟨66825549958424049331086613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89100733277898732441448817 66825549958424049331086613)
                    ·
                      refine ⟨3132447654301127312394685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66825549958424049331086613 3132447654301127312394685)
                      ·
                        rfl

theorem cell23_6100420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_6100420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100420 prefixEnd_6100420 := by exact prefixLift 6100420
  have htrace : WordTrace (prefixWord ++ tailWord_6100420) baseStart_6100420 baseEnd_6100420 := by
    simpa [prefixWord, tailWord_6100420, baseEnd_6100420] using wordTrace_append hprefix tailTrace_6100420
  have hstable : (prefixWord ++ tailWord_6100420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100420).length < 2 ^ (prefixWord ++ tailWord_6100420).sum := by decide
  have hdescent : baseEnd_6100420 < baseStart_6100420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100478 : List Nat := [4, 2, 2, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_6100478 : Nat := 118140960795 + 6100478 * 2 ^ 59
def prefixEnd_6100478 : Nat := 4983230072969 + 3 ^ 40 * 6100478 * 2
def baseEnd_6100478 : Nat := 3132477436179088085469419

theorem tailTrace_6100478 : CollatzResearch.WordTrace tailWord_6100478 prefixEnd_6100478 3132477436179088085469419 := by
  unfold tailWord_6100478
  simp only [CollatzResearch.WordTrace]
  refine ⟨27812838999127194942413761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148335141328678373026206725 27812838999127194942413761)
  ·
    refine ⟨20859629249345396206810321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27812838999127194942413761 20859629249345396206810321)
    ·
      refine ⟨15644721937009047155107741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20859629249345396206810321 15644721937009047155107741)
      ·
        refine ⟨5866770726378392683165403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15644721937009047155107741 5866770726378392683165403)
        ·
          refine ⟨8800156089567589024748105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5866770726378392683165403 8800156089567589024748105)
          ·
            refine ⟨6600117067175691768561079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8800156089567589024748105 6600117067175691768561079)
            ·
              refine ⟨9900175600763537652841619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6600117067175691768561079 9900175600763537652841619)
              ·
                refine ⟨14850263401145306479262429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9900175600763537652841619 14850263401145306479262429)
                ·
                  refine ⟨5568848775429489929723411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14850263401145306479262429 5568848775429489929723411)
                  ·
                    refine ⟨8353273163144234894585117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5568848775429489929723411 8353273163144234894585117)
                    ·
                      refine ⟨3132477436179088085469419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8353273163144234894585117 3132477436179088085469419)
                      ·
                        rfl

theorem cell23_6100478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_6100478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100478 prefixEnd_6100478 := by exact prefixLift 6100478
  have htrace : WordTrace (prefixWord ++ tailWord_6100478) baseStart_6100478 baseEnd_6100478 := by
    simpa [prefixWord, tailWord_6100478, baseEnd_6100478] using wordTrace_append hprefix tailTrace_6100478
  have hstable : (prefixWord ++ tailWord_6100478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100478).length < 2 ^ (prefixWord ++ tailWord_6100478).sum := by decide
  have hdescent : baseEnd_6100478 < baseStart_6100478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100490 : List Nat := [3, 1, 2, 2, 2, 3, 2, 8]
def baseStart_6100490 : Nat := 118140960795 + 6100490 * 2 ^ 59
def prefixEnd_6100490 : Nat := 4983230072969 + 3 ^ 40 * 6100490 * 2
def baseEnd_6100490 : Nat := 116017911035071927352569

theorem tailTrace_6100490 : CollatzResearch.WordTrace tailWord_6100490 prefixEnd_6100490 116017911035071927352569 := by
  unfold tailWord_6100490
  simp only [CollatzResearch.WordTrace]
  refine ⟨55625787417243521397186731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148335433112649390392497949 55625787417243521397186731)
  ·
    refine ⟨83438681125865282095780097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55625787417243521397186731 83438681125865282095780097)
    ·
      refine ⟨62579010844398961571835073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83438681125865282095780097 62579010844398961571835073)
      ·
        refine ⟨46934258133299221178876305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62579010844398961571835073 46934258133299221178876305)
        ·
          refine ⟨35200693599974415884157229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46934258133299221178876305 35200693599974415884157229)
          ·
            refine ⟨13200260099990405956558961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35200693599974415884157229 13200260099990405956558961)
            ·
              refine ⟨9900195074992804467419221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13200260099990405956558961 9900195074992804467419221)
              ·
                refine ⟨116017911035071927352569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9900195074992804467419221 116017911035071927352569)
                ·
                  rfl

theorem cell23_6100490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 8].length) (baseStart_6100490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100490 prefixEnd_6100490 := by exact prefixLift 6100490
  have htrace : WordTrace (prefixWord ++ tailWord_6100490) baseStart_6100490 baseEnd_6100490 := by
    simpa [prefixWord, tailWord_6100490, baseEnd_6100490] using wordTrace_append hprefix tailTrace_6100490
  have hstable : (prefixWord ++ tailWord_6100490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100490).length < 2 ^ (prefixWord ++ tailWord_6100490).sum := by decide
  have hdescent : baseEnd_6100490 < baseStart_6100490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100494 : List Nat := [4, 1, 1, 2, 4, 1, 1, 3, 2, 4]
def baseStart_6100494 : Nat := 118140960795 + 6100494 * 2 ^ 59
def prefixEnd_6100494 : Nat := 4983230072969 + 3 ^ 40 * 6100494 * 2
def baseEnd_6100494 : Nat := 1044161883956520007623115

theorem tailTrace_6100494 : CollatzResearch.WordTrace tailWord_6100494 prefixEnd_6100494 1044161883956520007623115 := by
  unfold tailWord_6100494
  simp only [CollatzResearch.WordTrace]
  refine ⟨27812911945119949283986567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148335530373973062847928357 27812911945119949283986567)
  ·
    refine ⟨41719367917679923925979851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27812911945119949283986567 41719367917679923925979851)
    ·
      refine ⟨62579051876519885888969777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41719367917679923925979851 62579051876519885888969777)
      ·
        refine ⟨46934288907389914416727333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62579051876519885888969777 46934288907389914416727333)
        ·
          refine ⟨8800179170135608953136375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46934288907389914416727333 8800179170135608953136375)
          ·
            refine ⟨13200268755203413429704563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8800179170135608953136375 13200268755203413429704563)
            ·
              refine ⟨19800403132805120144556845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13200268755203413429704563 19800403132805120144556845)
              ·
                refine ⟨7425151174801920054208817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19800403132805120144556845 7425151174801920054208817)
                ·
                  refine ⟨5568863381101440040656613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7425151174801920054208817 5568863381101440040656613)
                  ·
                    refine ⟨1044161883956520007623115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5568863381101440040656613 1044161883956520007623115)
                    ·
                      rfl

theorem cell23_6100494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_6100494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100494 prefixEnd_6100494 := by exact prefixLift 6100494
  have htrace : WordTrace (prefixWord ++ tailWord_6100494) baseStart_6100494 baseEnd_6100494 := by
    simpa [prefixWord, tailWord_6100494, baseEnd_6100494] using wordTrace_append hprefix tailTrace_6100494
  have hstable : (prefixWord ++ tailWord_6100494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100494).length < 2 ^ (prefixWord ++ tailWord_6100494).sum := by decide
  have hdescent : baseEnd_6100494 < baseStart_6100494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100560 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 3]
def baseStart_6100560 : Nat := 118140960795 + 6100560 * 2 ^ 59
def prefixEnd_6100560 : Nat := 4983230072969 + 3 ^ 40 * 6100560 * 2
def baseEnd_6100560 : Nat := 3132519541592756764644041

theorem tailTrace_6100560 : CollatzResearch.WordTrace tailWord_6100560 prefixEnd_6100560 3132519541592756764644041 := by
  unfold tailWord_6100560
  simp only [CollatzResearch.WordTrace]
  refine ⟨111252851389360243771897567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148337135185813658362530089 111252851389360243771897567)
  ·
    refine ⟨166879277084040365657846351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111252851389360243771897567 166879277084040365657846351)
    ·
      refine ⟨250318915626060548486769527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166879277084040365657846351 250318915626060548486769527)
      ·
        refine ⟨375478373439090822730154291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250318915626060548486769527 375478373439090822730154291)
        ·
          refine ⟨563217560158636234095231437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375478373439090822730154291 563217560158636234095231437)
          ·
            refine ⟨211206585059488587785711789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 563217560158636234095231437 211206585059488587785711789)
            ·
              refine ⟨79202469397308220419641921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211206585059488587785711789 79202469397308220419641921)
              ·
                refine ⟨59401852047981165314731441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79202469397308220419641921 59401852047981165314731441)
                ·
                  refine ⟨44551389035985873986048581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59401852047981165314731441 44551389035985873986048581)
                  ·
                    refine ⟨8353385444247351372384109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44551389035985873986048581 8353385444247351372384109)
                    ·
                      refine ⟨3132519541592756764644041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8353385444247351372384109 3132519541592756764644041)
                      ·
                        rfl

theorem cell23_6100560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 3].length) (baseStart_6100560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100560 prefixEnd_6100560 := by exact prefixLift 6100560
  have htrace : WordTrace (prefixWord ++ tailWord_6100560) baseStart_6100560 baseEnd_6100560 := by
    simpa [prefixWord, tailWord_6100560, baseEnd_6100560] using wordTrace_append hprefix tailTrace_6100560
  have hstable : (prefixWord ++ tailWord_6100560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100560).length < 2 ^ (prefixWord ++ tailWord_6100560).sum := by decide
  have hdescent : baseEnd_6100560 < baseStart_6100560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100597 : List Nat := [1, 3, 4, 2, 1, 1, 1, 3, 7]
def baseStart_6100597 : Nat := 118140960795 + 6100597 * 2 ^ 59
def prefixEnd_6100597 : Nat := 4983230072969 + 3 ^ 40 * 6100597 * 2
def baseEnd_6100597 : Nat := 348059837819663679986819

theorem tailTrace_6100597 : CollatzResearch.WordTrace tailWord_6100597 prefixEnd_6100597 348059837819663679986819 := by
  unfold tailWord_6100597
  simp only [CollatzResearch.WordTrace]
  refine ⟨222507052279586442862892045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148338034853057628575261363 222507052279586442862892045)
  ·
    refine ⟨83440144604844916073584517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222507052279586442862892045 83440144604844916073584517)
    ·
      refine ⟨15645027113408421763797097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83440144604844916073584517 15645027113408421763797097)
      ·
        refine ⟨11733770335056316322847823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15645027113408421763797097 11733770335056316322847823)
        ·
          refine ⟨17600655502584474484271735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11733770335056316322847823 17600655502584474484271735)
          ·
            refine ⟨26400983253876711726407603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17600655502584474484271735 26400983253876711726407603)
            ·
              refine ⟨39601474880815067589611405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26400983253876711726407603 39601474880815067589611405)
              ·
                refine ⟨14850553080305650346104277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39601474880815067589611405 14850553080305650346104277)
                ·
                  refine ⟨348059837819663679986819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14850553080305650346104277 348059837819663679986819)
                  ·
                    rfl

theorem cell23_6100597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 7].length) (baseStart_6100597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100597 prefixEnd_6100597 := by exact prefixLift 6100597
  have htrace : WordTrace (prefixWord ++ tailWord_6100597) baseStart_6100597 baseEnd_6100597 := by
    simpa [prefixWord, tailWord_6100597, baseEnd_6100597] using wordTrace_append hprefix tailTrace_6100597
  have hstable : (prefixWord ++ tailWord_6100597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100597).length < 2 ^ (prefixWord ++ tailWord_6100597).sum := by decide
  have hdescent : baseEnd_6100597 < baseStart_6100597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100617 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 2, 5, 2]
def baseStart_6100617 : Nat := 118140960795 + 6100617 * 2 ^ 59
def prefixEnd_6100617 : Nat := 4983230072969 + 3 ^ 40 * 6100617 * 2
def baseEnd_6100617 : Nat := 3132548809990063041631279

theorem tailTrace_6100617 : CollatzResearch.WordTrace tailWord_6100617 prefixEnd_6100617 3132548809990063041631279 := by
  unfold tailWord_6100617
  simp only [CollatzResearch.WordTrace]
  refine ⟨222507781739513986278620105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148338521159675990852413403 222507781739513986278620105)
  ·
    refine ⟨166880836304635489708965079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222507781739513986278620105 166880836304635489708965079)
    ·
      refine ⟨250321254456953234563447619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166880836304635489708965079 250321254456953234563447619)
      ·
        refine ⟨375481881685429851845171429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250321254456953234563447619 375481881685429851845171429)
        ·
          refine ⟨70402852816018097220969643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 375481881685429851845171429 70402852816018097220969643)
          ·
            refine ⟨105604279224027145831454465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70402852816018097220969643 105604279224027145831454465)
            ·
              refine ⟨79203209418020359373590849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105604279224027145831454465 79203209418020359373590849)
              ·
                refine ⟨59402407063515269530193137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79203209418020359373590849 59402407063515269530193137)
                ·
                  refine ⟨44551805297636452147644853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59402407063515269530193137 44551805297636452147644853)
                  ·
                    refine ⟨4176731746653417388841705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44551805297636452147644853 4176731746653417388841705)
                    ·
                      refine ⟨3132548809990063041631279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4176731746653417388841705 3132548809990063041631279)
                      ·
                        rfl

theorem cell23_6100617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 5, 2].length) (baseStart_6100617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100617 prefixEnd_6100617 := by exact prefixLift 6100617
  have htrace : WordTrace (prefixWord ++ tailWord_6100617) baseStart_6100617 baseEnd_6100617 := by
    simpa [prefixWord, tailWord_6100617, baseEnd_6100617] using wordTrace_append hprefix tailTrace_6100617
  have hstable : (prefixWord ++ tailWord_6100617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100617).length < 2 ^ (prefixWord ++ tailWord_6100617).sum := by decide
  have hdescent : baseEnd_6100617 < baseStart_6100617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100648 : List Nat := [2, 1, 7, 1, 1, 2, 1, 1, 7]
def baseStart_6100648 : Nat := 118140960795 + 6100648 * 2 ^ 59
def prefixEnd_6100648 : Nat := 4983230072969 + 3 ^ 40 * 6100648 * 2
def baseEnd_6100648 : Nat := 348062747543372491149293

theorem tailTrace_6100648 : CollatzResearch.WordTrace tailWord_6100648 prefixEnd_6100648 348062747543372491149293 := by
  unfold tailWord_6100648
  simp only [CollatzResearch.WordTrace]
  refine ⟨111254456201200839286499299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148339274934934452381999065 111254456201200839286499299)
  ·
    refine ⟨166881684301801258929748949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111254456201200839286499299 166881684301801258929748949)
    ·
      refine ⟨3911289475823467006165991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 166881684301801258929748949 3911289475823467006165991)
      ·
        refine ⟨5866934213735200509248987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3911289475823467006165991 5866934213735200509248987)
        ·
          refine ⟨8800401320602800763873481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5866934213735200509248987 8800401320602800763873481)
          ·
            refine ⟨6600300990452100572905111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8800401320602800763873481 6600300990452100572905111)
            ·
              refine ⟨9900451485678150859357667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6600300990452100572905111 9900451485678150859357667)
              ·
                refine ⟨14850677228517226289036501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9900451485678150859357667 14850677228517226289036501)
                ·
                  refine ⟨348062747543372491149293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14850677228517226289036501 348062747543372491149293)
                  ·
                    rfl

theorem cell23_6100648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 7].length) (baseStart_6100648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100648 prefixEnd_6100648 := by exact prefixLift 6100648
  have htrace : WordTrace (prefixWord ++ tailWord_6100648) baseStart_6100648 baseEnd_6100648 := by
    simpa [prefixWord, tailWord_6100648, baseEnd_6100648] using wordTrace_append hprefix tailTrace_6100648
  have hstable : (prefixWord ++ tailWord_6100648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100648).length < 2 ^ (prefixWord ++ tailWord_6100648).sum := by decide
  have hdescent : baseEnd_6100648 < baseStart_6100648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100678 : List Nat := [6, 1, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_6100678 : Nat := 118140960795 + 6100678 * 2 ^ 59
def prefixEnd_6100678 : Nat := 4983230072969 + 3 ^ 40 * 6100678 * 2
def baseEnd_6100678 : Nat := 1044193377436662434322833

theorem tailTrace_6100678 : CollatzResearch.WordTrace tailWord_6100678 prefixEnd_6100678 1044193377436662434322833 := by
  unfold tailWord_6100678
  simp only [CollatzResearch.WordTrace]
  refine ⟨6953437706009156053018459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 148340004394861995797727125 6953437706009156053018459)
  ·
    refine ⟨10430156559013734079527689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6953437706009156053018459 10430156559013734079527689)
    ·
      refine ⟨7822617419260300559645767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10430156559013734079527689 7822617419260300559645767)
      ·
        refine ⟨11733926128890450839468651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7822617419260300559645767 11733926128890450839468651)
        ·
          refine ⟨17600889193335676259202977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11733926128890450839468651 17600889193335676259202977)
          ·
            refine ⟨13200666895001757194402233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17600889193335676259202977 13200666895001757194402233)
            ·
              refine ⟨9900500171251317895801675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13200666895001757194402233 9900500171251317895801675)
              ·
                refine ⟨14850750256876976843702513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9900500171251317895801675 14850750256876976843702513)
                ·
                  refine ⟨11138062692657732632776885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14850750256876976843702513 11138062692657732632776885)
                  ·
                    refine ⟨1044193377436662434322833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11138062692657732632776885 1044193377436662434322833)
                    ·
                      rfl

theorem cell23_6100678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_6100678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100678 prefixEnd_6100678 := by exact prefixLift 6100678
  have htrace : WordTrace (prefixWord ++ tailWord_6100678) baseStart_6100678 baseEnd_6100678 := by
    simpa [prefixWord, tailWord_6100678, baseEnd_6100678] using wordTrace_append hprefix tailTrace_6100678
  have hstable : (prefixWord ++ tailWord_6100678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100678).length < 2 ^ (prefixWord ++ tailWord_6100678).sum := by decide
  have hdescent : baseEnd_6100678 < baseStart_6100678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100747 : List Nat := [1, 1, 1, 1, 5, 1, 4, 2, 1, 6]
def baseStart_6100747 : Nat := 118140960795 + 6100747 * 2 ^ 59
def prefixEnd_6100747 : Nat := 4983230072969 + 3 ^ 40 * 6100747 * 2
def baseEnd_6100747 : Nat := 1044205187491715844335227

theorem tailTrace_6100747 : CollatzResearch.WordTrace tailWord_6100747 prefixEnd_6100747 1044205187491715844335227 := by
  unfold tailWord_6100747
  simp only [CollatzResearch.WordTrace]
  refine ⟨222512523229043018480852495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148341682152695345653901663 222512523229043018480852495)
  ·
    refine ⟨333768784843564527721278743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222512523229043018480852495 333768784843564527721278743)
    ·
      refine ⟨500653177265346791581918115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333768784843564527721278743 500653177265346791581918115)
      ·
        refine ⟨750979765898020187372877173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500653177265346791581918115 750979765898020187372877173)
        ·
          refine ⟨70404353052939392566207235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 750979765898020187372877173 70404353052939392566207235)
          ·
            refine ⟨105606529579409088849310853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70404353052939392566207235 105606529579409088849310853)
            ·
              refine ⟨19801224296139204159245785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105606529579409088849310853 19801224296139204159245785)
              ·
                refine ⟨14850918222104403119434339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19801224296139204159245785 14850918222104403119434339)
                ·
                  refine ⟨22276377333156604679151509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14850918222104403119434339 22276377333156604679151509)
                  ·
                    refine ⟨1044205187491715844335227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22276377333156604679151509 1044205187491715844335227)
                    ·
                      rfl

theorem cell23_6100747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 6].length) (baseStart_6100747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100747 prefixEnd_6100747 := by exact prefixLift 6100747
  have htrace : WordTrace (prefixWord ++ tailWord_6100747) baseStart_6100747 baseEnd_6100747 := by
    simpa [prefixWord, tailWord_6100747, baseEnd_6100747] using wordTrace_append hprefix tailTrace_6100747
  have hstable : (prefixWord ++ tailWord_6100747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100747).length < 2 ^ (prefixWord ++ tailWord_6100747).sum := by decide
  have hdescent : baseEnd_6100747 < baseStart_6100747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100764 : List Nat := [2, 2, 3, 1, 1, 2, 3, 1, 4, 4]
def baseStart_6100764 : Nat := 118140960795 + 6100764 * 2 ^ 59
def prefixEnd_6100764 : Nat := 4983230072969 + 3 ^ 40 * 6100764 * 2
def baseEnd_6100764 : Nat := 1044208097215424655497701

theorem tailTrace_6100764 : CollatzResearch.WordTrace tailWord_6100764 prefixEnd_6100764 1044208097215424655497701 := by
  unfold tailWord_6100764
  simp only [CollatzResearch.WordTrace]
  refine ⟨111256571634990715192110673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148342095513320953589480897 111256571634990715192110673)
  ·
    refine ⟨83442428726243036394083005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111256571634990715192110673 83442428726243036394083005)
    ·
      refine ⟨31290910772341138647781127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83442428726243036394083005 31290910772341138647781127)
      ·
        refine ⟨46936366158511707971671691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31290910772341138647781127 46936366158511707971671691)
        ·
          refine ⟨70404549237767561957507537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46936366158511707971671691 70404549237767561957507537)
          ·
            refine ⟨52803411928325671468130653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70404549237767561957507537 52803411928325671468130653)
            ·
              refine ⟨19801279473122126800548995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52803411928325671468130653 19801279473122126800548995)
              ·
                refine ⟨29701919209683190200823493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19801279473122126800548995 29701919209683190200823493)
                ·
                  refine ⟨5569109851815598162654405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29701919209683190200823493 5569109851815598162654405)
                  ·
                    refine ⟨1044208097215424655497701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5569109851815598162654405 1044208097215424655497701)
                    ·
                      rfl

theorem cell23_6100764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_6100764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100764 prefixEnd_6100764 := by exact prefixLift 6100764
  have htrace : WordTrace (prefixWord ++ tailWord_6100764) baseStart_6100764 baseEnd_6100764 := by
    simpa [prefixWord, tailWord_6100764, baseEnd_6100764] using wordTrace_append hprefix tailTrace_6100764
  have hstable : (prefixWord ++ tailWord_6100764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100764).length < 2 ^ (prefixWord ++ tailWord_6100764).sum := by decide
  have hdescent : baseEnd_6100764 < baseStart_6100764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100767 : List Nat := [1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 6]
def baseStart_6100767 : Nat := 118140960795 + 6100767 * 2 ^ 59
def prefixEnd_6100767 : Nat := 4983230072969 + 3 ^ 40 * 6100767 * 2
def baseEnd_6100767 : Nat := 3132625832088237454755589

theorem tailTrace_6100767 : CollatzResearch.WordTrace tailWord_6100767 prefixEnd_6100767 3132625832088237454755589 := by
  unfold tailWord_6100767
  simp only [CollatzResearch.WordTrace]
  refine ⟨222513252688970561896580555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148342168459313707931053703 222513252688970561896580555)
  ·
    refine ⟨333769879033455842844870833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222513252688970561896580555 333769879033455842844870833)
    ·
      refine ⟨250327409275091882133653125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333769879033455842844870833 250327409275091882133653125)
      ·
        refine ⟨46936389239079727900059961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 250327409275091882133653125 46936389239079727900059961)
        ·
          refine ⟨35202291929309795925044971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46936389239079727900059961 35202291929309795925044971)
          ·
            refine ⟨52803437893964693887567457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35202291929309795925044971 52803437893964693887567457)
            ·
              refine ⟨39602578420473520415675593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52803437893964693887567457 39602578420473520415675593)
              ·
                refine ⟨29701933815355140311756695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39602578420473520415675593 29701933815355140311756695)
                ·
                  refine ⟨44552900723032710467635043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29701933815355140311756695 44552900723032710467635043)
                  ·
                    refine ⟨66829351084549065701452565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44552900723032710467635043 66829351084549065701452565)
                    ·
                      refine ⟨3132625832088237454755589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66829351084549065701452565 3132625832088237454755589)
                      ·
                        rfl

theorem cell23_6100767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_6100767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100767 prefixEnd_6100767 := by exact prefixLift 6100767
  have htrace : WordTrace (prefixWord ++ tailWord_6100767) baseStart_6100767 baseEnd_6100767 := by
    simpa [prefixWord, tailWord_6100767, baseEnd_6100767] using wordTrace_append hprefix tailTrace_6100767
  have hstable : (prefixWord ++ tailWord_6100767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100767).length < 2 ^ (prefixWord ++ tailWord_6100767).sum := by decide
  have hdescent : baseEnd_6100767 < baseStart_6100767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100771 : List Nat := [1, 1, 1, 4, 2, 1, 3, 3, 3, 2, 2]
def baseStart_6100771 : Nat := 118140960795 + 6100771 * 2 ^ 59
def prefixEnd_6100771 : Nat := 4983230072969 + 3 ^ 40 * 6100771 * 2
def baseEnd_6100771 : Nat := 3132627886010855439105571

theorem tailTrace_6100771 : CollatzResearch.WordTrace tailWord_6100771 prefixEnd_6100771 3132627886010855439105571 := by
  unfold tailWord_6100771
  simp only [CollatzResearch.WordTrace]
  refine ⟨222513398580956070579726167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148342265720637380386484111 222513398580956070579726167)
  ·
    refine ⟨333770097871434105869589251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222513398580956070579726167 333770097871434105869589251)
    ·
      refine ⟨500655146807151158804383877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333770097871434105869589251 500655146807151158804383877)
      ·
        refine ⟨93872840026340842275821977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 500655146807151158804383877 93872840026340842275821977)
        ·
          refine ⟨70404630019755631706866483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93872840026340842275821977 70404630019755631706866483)
          ·
            refine ⟨105606945029633447560299725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70404630019755631706866483 105606945029633447560299725)
            ·
              refine ⟨39602604386112542835112397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105606945029633447560299725 39602604386112542835112397)
              ·
                refine ⟨14850976644792203563167149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39602604386112542835112397 14850976644792203563167149)
                ·
                  refine ⟨5569116241797076336187681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14850976644792203563167149 5569116241797076336187681)
                  ·
                    refine ⟨4176837181347807252140761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5569116241797076336187681 4176837181347807252140761)
                    ·
                      refine ⟨3132627886010855439105571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4176837181347807252140761 3132627886010855439105571)
                      ·
                        rfl

theorem cell23_6100771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 2, 2].length) (baseStart_6100771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100771 prefixEnd_6100771 := by exact prefixLift 6100771
  have htrace : WordTrace (prefixWord ++ tailWord_6100771) baseStart_6100771 baseEnd_6100771 := by
    simpa [prefixWord, tailWord_6100771, baseEnd_6100771] using wordTrace_append hprefix tailTrace_6100771
  have hstable : (prefixWord ++ tailWord_6100771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100771).length < 2 ^ (prefixWord ++ tailWord_6100771).sum := by decide
  have hdescent : baseEnd_6100771 < baseStart_6100771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100788 : List Nat := [2, 5, 1, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_6100788 : Nat := 118140960795 + 6100788 * 2 ^ 59
def prefixEnd_6100788 : Nat := 4983230072969 + 3 ^ 40 * 6100788 * 2
def baseEnd_6100788 : Nat := 3132636615181981872592993

theorem tailTrace_6100788 : CollatzResearch.WordTrace tailWord_6100788 prefixEnd_6100788 3132636615181981872592993 := by
  unfold tailWord_6100788
  simp only [CollatzResearch.WordTrace]
  refine ⟨111257009310947241241547509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148342679081262988322063345 111257009310947241241547509)
  ·
    refine ⟨10430344622901303866395079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111257009310947241241547509 10430344622901303866395079)
    ·
      refine ⟨15645516934351955799592619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10430344622901303866395079 15645516934351955799592619)
      ·
        refine ⟨23468275401527933699388929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15645516934351955799592619 23468275401527933699388929)
        ·
          refine ⟨17601206551145950274541697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23468275401527933699388929 17601206551145950274541697)
          ·
            refine ⟨13200904913359462705906273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17601206551145950274541697 13200904913359462705906273)
            ·
              refine ⟨9900678685019597029429705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13200904913359462705906273 9900678685019597029429705)
              ·
                refine ⟨7425509013764697772072279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9900678685019597029429705 7425509013764697772072279)
                ·
                  refine ⟨11138263520647046658108419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7425509013764697772072279 11138263520647046658108419)
                  ·
                    refine ⟨16707395280970569987162629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11138263520647046658108419 16707395280970569987162629)
                    ·
                      refine ⟨3132636615181981872592993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16707395280970569987162629 3132636615181981872592993)
                      ·
                        rfl

theorem cell23_6100788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_6100788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100788 prefixEnd_6100788 := by exact prefixLift 6100788
  have htrace : WordTrace (prefixWord ++ tailWord_6100788) baseStart_6100788 baseEnd_6100788 := by
    simpa [prefixWord, tailWord_6100788, baseEnd_6100788] using wordTrace_append hprefix tailTrace_6100788
  have hstable : (prefixWord ++ tailWord_6100788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100788).length < 2 ^ (prefixWord ++ tailWord_6100788).sum := by decide
  have hdescent : baseEnd_6100788 < baseStart_6100788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100794 : List Nat := [3, 1, 1, 1, 5, 1, 4, 7]
def baseStart_6100794 : Nat := 118140960795 + 6100794 * 2 ^ 59
def prefixEnd_6100794 : Nat := 4983230072969 + 3 ^ 40 * 6100794 * 2
def baseEnd_6100794 : Nat := 116023692446885512930295

theorem tailTrace_6100794 : CollatzResearch.WordTrace tailWord_6100794 prefixEnd_6100794 116023692446885512930295 := by
  unfold tailWord_6100794
  simp only [CollatzResearch.WordTrace]
  refine ⟨55628559364968186376953359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148342824973248497005208957 55628559364968186376953359)
  ·
    refine ⟨83442839047452279565430039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55628559364968186376953359 83442839047452279565430039)
    ·
      refine ⟨125164258571178419348145059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83442839047452279565430039 125164258571178419348145059)
      ·
        refine ⟨187746387856767629022217589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125164258571178419348145059 187746387856767629022217589)
        ·
          refine ⟨17601223861571965220832899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 187746387856767629022217589 17601223861571965220832899)
          ·
            refine ⟨26401835792357947831249349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17601223861571965220832899 26401835792357947831249349)
            ·
              refine ⟨4950344211067115218359253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26401835792357947831249349 4950344211067115218359253)
              ·
                refine ⟨116023692446885512930295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4950344211067115218359253 116023692446885512930295)
                ·
                  rfl

theorem cell23_6100794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 7].length) (baseStart_6100794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100794 prefixEnd_6100794 := by exact prefixLift 6100794
  have htrace : WordTrace (prefixWord ++ tailWord_6100794) baseStart_6100794 baseEnd_6100794 := by
    simpa [prefixWord, tailWord_6100794, baseEnd_6100794] using wordTrace_append hprefix tailTrace_6100794
  have hstable : (prefixWord ++ tailWord_6100794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100794).length < 2 ^ (prefixWord ++ tailWord_6100794).sum := by decide
  have hdescent : baseEnd_6100794 < baseStart_6100794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100821 : List Nat := [1, 3, 2, 2, 2, 2, 2, 1, 4, 1, 3]
def baseStart_6100821 : Nat := 118140960795 + 6100821 * 2 ^ 59
def prefixEnd_6100821 : Nat := 4983230072969 + 3 ^ 40 * 6100821 * 2
def baseEnd_6100821 : Nat := 3132653560043580243480341

theorem tailTrace_6100821 : CollatzResearch.WordTrace tailWord_6100821 prefixEnd_6100821 3132653560043580243480341 := by
  unfold tailWord_6100821
  simp only [CollatzResearch.WordTrace]
  refine ⟨222515222230774929119046317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148343481487183286079364211 222515222230774929119046317)
  ·
    refine ⟨83443208336540598419642369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222515222230774929119046317 83443208336540598419642369)
    ·
      refine ⟨62582406252405448814731777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83443208336540598419642369 62582406252405448814731777)
      ·
        refine ⟨46936804689304086611048833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62582406252405448814731777 46936804689304086611048833)
        ·
          refine ⟨35202603516978064958286625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46936804689304086611048833 35202603516978064958286625)
          ·
            refine ⟨26401952637733548718714969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35202603516978064958286625 26401952637733548718714969)
            ·
              refine ⟨19801464478300161539036227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26401952637733548718714969 19801464478300161539036227)
              ·
                refine ⟨29702196717450242308554341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19801464478300161539036227 29702196717450242308554341)
                ·
                  refine ⟨5569161884521920432853939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29702196717450242308554341 5569161884521920432853939)
                  ·
                    refine ⟨8353742826782880649280909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5569161884521920432853939 8353742826782880649280909)
                    ·
                      refine ⟨3132653560043580243480341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8353742826782880649280909 3132653560043580243480341)
                      ·
                        rfl

theorem cell23_6100821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_6100821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100821 prefixEnd_6100821 := by exact prefixLift 6100821
  have htrace : WordTrace (prefixWord ++ tailWord_6100821) baseStart_6100821 baseEnd_6100821 := by
    simpa [prefixWord, tailWord_6100821, baseEnd_6100821] using wordTrace_append hprefix tailTrace_6100821
  have hstable : (prefixWord ++ tailWord_6100821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100821).length < 2 ^ (prefixWord ++ tailWord_6100821).sum := by decide
  have hdescent : baseEnd_6100821 < baseStart_6100821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100837 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 1, 8]
def baseStart_6100837 : Nat := 118140960795 + 6100837 * 2 ^ 59
def prefixEnd_6100837 : Nat := 4983230072969 + 3 ^ 40 * 6100837 * 2
def baseEnd_6100837 : Nat := 1044220591911350726960089

theorem tailTrace_6100837 : CollatzResearch.WordTrace tailWord_6100837 prefixEnd_6100837 1044220591911350726960089 := by
  unfold tailWord_6100837
  simp only [CollatzResearch.WordTrace]
  refine ⟨222515805798716963851628765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148343870532477975901085843 222515805798716963851628765)
  ·
    refine ⟨83443427174518861444360787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222515805798716963851628765 83443427174518861444360787)
    ·
      refine ⟨125165140761778292166541181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83443427174518861444360787 125165140761778292166541181)
      ·
        refine ⟨46936927785666859562452943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125165140761778292166541181 46936927785666859562452943)
        ·
          refine ⟨70405391678500289343679415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46936927785666859562452943 70405391678500289343679415)
          ·
            refine ⟨105608087517750434015519123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70405391678500289343679415 105608087517750434015519123)
            ·
              refine ⟨158412131276625651023278685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105608087517750434015519123 158412131276625651023278685)
              ·
                refine ⟨59404549228734619133729507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158412131276625651023278685 59404549228734619133729507)
                ·
                  refine ⟨89106823843101928700594261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59404549228734619133729507 89106823843101928700594261)
                  ·
                    refine ⟨1044220591911350726960089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89106823843101928700594261 1044220591911350726960089)
                    ·
                      rfl

theorem cell23_6100837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_6100837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100837 prefixEnd_6100837 := by exact prefixLift 6100837
  have htrace : WordTrace (prefixWord ++ tailWord_6100837) baseStart_6100837 baseEnd_6100837 := by
    simpa [prefixWord, tailWord_6100837, baseEnd_6100837] using wordTrace_append hprefix tailTrace_6100837
  have hstable : (prefixWord ++ tailWord_6100837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100837).length < 2 ^ (prefixWord ++ tailWord_6100837).sum := by decide
  have hdescent : baseEnd_6100837 < baseStart_6100837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100842 : List Nat := [3, 1, 3, 4, 2, 1, 1, 2, 1, 2, 3]
def baseStart_6100842 : Nat := 118140960795 + 6100842 * 2 ^ 59
def prefixEnd_6100842 : Nat := 4983230072969 + 3 ^ 40 * 6100842 * 2
def baseEnd_6100842 : Nat := 3132664343137324661317745

theorem tailTrace_6100842 : CollatzResearch.WordTrace tailWord_6100842 prefixEnd_6100842 3132664343137324661317745 := by
  unfold tailWord_6100842
  simp only [CollatzResearch.WordTrace]
  refine ⟨55628997040924712426390195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148343992109132566470373853 55628997040924712426390195)
  ·
    refine ⟨83443495561387068639585293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55628997040924712426390195 83443495561387068639585293)
    ·
      refine ⟨31291310835520150739844485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83443495561387068639585293 31291310835520150739844485)
      ·
        refine ⟨5867120781660028263720841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31291310835520150739844485 5867120781660028263720841)
        ·
          refine ⟨4400340586245021197790631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5867120781660028263720841 4400340586245021197790631)
          ·
            refine ⟨6600510879367531796685947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4400340586245021197790631 6600510879367531796685947)
            ·
              refine ⟨9900766319051297695028921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6600510879367531796685947 9900766319051297695028921)
              ·
                refine ⟨7425574739288473271271691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9900766319051297695028921 7425574739288473271271691)
                ·
                  refine ⟨11138362108932709906907537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7425574739288473271271691 11138362108932709906907537)
                  ·
                    refine ⟨8353771581699532430180653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11138362108932709906907537 8353771581699532430180653)
                    ·
                      refine ⟨3132664343137324661317745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8353771581699532430180653 3132664343137324661317745)
                      ·
                        rfl

theorem cell23_6100842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_6100842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100842 prefixEnd_6100842 := by exact prefixLift 6100842
  have htrace : WordTrace (prefixWord ++ tailWord_6100842) baseStart_6100842 baseEnd_6100842 := by
    simpa [prefixWord, tailWord_6100842, baseEnd_6100842] using wordTrace_append hprefix tailTrace_6100842
  have hstable : (prefixWord ++ tailWord_6100842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100842).length < 2 ^ (prefixWord ++ tailWord_6100842).sum := by decide
  have hdescent : baseEnd_6100842 < baseStart_6100842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100916 : List Nat := [2, 5, 2, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_6100916 : Nat := 118140960795 + 6100916 * 2 ^ 59
def prefixEnd_6100916 : Nat := 4983230072969 + 3 ^ 40 * 6100916 * 2
def baseEnd_6100916 : Nat := 3132702340705757371792405

theorem tailTrace_6100916 : CollatzResearch.WordTrace tailWord_6100916 prefixEnd_6100916 3132702340705757371792405 := by
  unfold tailWord_6100916
  simp only [CollatzResearch.WordTrace]
  refine ⟨111259343582715380171877301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148345791443620506895836401 111259343582715380171877301)
  ·
    refine ⟨10430563460879566891113497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111259343582715380171877301 10430563460879566891113497)
    ·
      refine ⟨7822922595659675168335123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10430563460879566891113497 7822922595659675168335123)
      ·
        refine ⟨11734383893489512752502685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7822922595659675168335123 11734383893489512752502685)
        ·
          refine ⟨4400393960058567282188507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11734383893489512752502685 4400393960058567282188507)
          ·
            refine ⟨6600590940087850923282761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4400393960058567282188507 6600590940087850923282761)
            ·
              refine ⟨4950443205065888192462071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6600590940087850923282761 4950443205065888192462071)
              ·
                refine ⟨7425664807598832288693107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4950443205065888192462071 7425664807598832288693107)
                ·
                  refine ⟨11138497211398248433039661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7425664807598832288693107 11138497211398248433039661)
                  ·
                    refine ⟨4176936454274343162389873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11138497211398248433039661 4176936454274343162389873)
                    ·
                      refine ⟨3132702340705757371792405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4176936454274343162389873 3132702340705757371792405)
                      ·
                        rfl

theorem cell23_6100916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_6100916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100916 prefixEnd_6100916 := by exact prefixLift 6100916
  have htrace : WordTrace (prefixWord ++ tailWord_6100916) baseStart_6100916 baseEnd_6100916 := by
    simpa [prefixWord, tailWord_6100916, baseEnd_6100916] using wordTrace_append hprefix tailTrace_6100916
  have hstable : (prefixWord ++ tailWord_6100916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100916).length < 2 ^ (prefixWord ++ tailWord_6100916).sum := by decide
  have hdescent : baseEnd_6100916 < baseStart_6100916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100951 : List Nat := [1, 1, 3, 2, 1, 1, 3, 3, 2, 4, 2]
def baseStart_6100951 : Nat := 118140960795 + 6100951 * 2 ^ 59
def prefixEnd_6100951 : Nat := 4983230072969 + 3 ^ 40 * 6100951 * 2
def baseEnd_6100951 : Nat := 3132720312528664734854743

theorem tailTrace_6100951 : CollatzResearch.WordTrace tailWord_6100951 prefixEnd_6100951 3132720312528664734854743 := by
  unfold tailWord_6100951
  simp only [CollatzResearch.WordTrace]
  refine ⟨222519963720303961321278707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148346642480202640880852471 222519963720303961321278707)
  ·
    refine ⟨333779945580455941981918061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222519963720303961321278707 333779945580455941981918061)
    ·
      refine ⟨125167479592670978243219273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333779945580455941981918061 125167479592670978243219273)
      ·
        refine ⟨93875609694503233682414455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125167479592670978243219273 93875609694503233682414455)
        ·
          refine ⟨140813414541754850523621683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93875609694503233682414455 140813414541754850523621683)
          ·
            refine ⟨211220121812632275785432525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140813414541754850523621683 211220121812632275785432525)
            ·
              refine ⟨79207545679737103419537197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211220121812632275785432525 79207545679737103419537197)
              ·
                refine ⟨29702829629901413782326449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79207545679737103419537197 29702829629901413782326449)
                ·
                  refine ⟨22277122222426060336744837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29702829629901413782326449 22277122222426060336744837)
                  ·
                    refine ⟨4176960416704886313139657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22277122222426060336744837 4176960416704886313139657)
                    ·
                      refine ⟨3132720312528664734854743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4176960416704886313139657 3132720312528664734854743)
                      ·
                        rfl

theorem cell23_6100951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 4, 2].length) (baseStart_6100951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100951 prefixEnd_6100951 := by exact prefixLift 6100951
  have htrace : WordTrace (prefixWord ++ tailWord_6100951) baseStart_6100951 baseEnd_6100951 := by
    simpa [prefixWord, tailWord_6100951, baseEnd_6100951] using wordTrace_append hprefix tailTrace_6100951
  have hstable : (prefixWord ++ tailWord_6100951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100951).length < 2 ^ (prefixWord ++ tailWord_6100951).sum := by decide
  have hdescent : baseEnd_6100951 < baseStart_6100951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100961 : List Nat := [1, 2, 3, 1, 2, 1, 4, 2, 3, 4]
def baseStart_6100961 : Nat := 118140960795 + 6100961 * 2 ^ 59
def prefixEnd_6100961 : Nat := 4983230072969 + 3 ^ 40 * 6100961 * 2
def baseEnd_6100961 : Nat := 1044241815778403231909899

theorem tailTrace_6100961 : CollatzResearch.WordTrace tailWord_6100961 prefixEnd_6100961 1044241815778403231909899 := by
  unfold tailWord_6100961
  simp only [CollatzResearch.WordTrace]
  refine ⟨222520328450267733029142737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148346885633511822019428491 222520328450267733029142737)
  ·
    refine ⟨166890246337700799771857053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222520328450267733029142737 166890246337700799771857053)
    ·
      refine ⟨62583842376637799914446395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166890246337700799771857053 62583842376637799914446395)
      ·
        refine ⟨93875763564956699871669593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62583842376637799914446395 93875763564956699871669593)
        ·
          refine ⟨70406822673717524903752195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93875763564956699871669593 70406822673717524903752195)
          ·
            refine ⟨105610234010576287355628293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70406822673717524903752195 105610234010576287355628293)
            ·
              refine ⟨19801918876983053879180305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105610234010576287355628293 19801918876983053879180305)
              ·
                refine ⟨14851439157737290409385229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19801918876983053879180305 14851439157737290409385229)
                ·
                  refine ⟨5569289684151483903519461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14851439157737290409385229 5569289684151483903519461)
                  ·
                    refine ⟨1044241815778403231909899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5569289684151483903519461 1044241815778403231909899)
                    ·
                      rfl

theorem cell23_6100961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_6100961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100961 prefixEnd_6100961 := by exact prefixLift 6100961
  have htrace : WordTrace (prefixWord ++ tailWord_6100961) baseStart_6100961 baseEnd_6100961 := by
    simpa [prefixWord, tailWord_6100961, baseEnd_6100961] using wordTrace_append hprefix tailTrace_6100961
  have hstable : (prefixWord ++ tailWord_6100961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100961).length < 2 ^ (prefixWord ++ tailWord_6100961).sum := by decide
  have hdescent : baseEnd_6100961 < baseStart_6100961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6100964 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 2, 4, 4]
def baseStart_6100964 : Nat := 118140960795 + 6100964 * 2 ^ 59
def prefixEnd_6100964 : Nat := 4983230072969 + 3 ^ 40 * 6100964 * 2
def baseEnd_6100964 : Nat := 3132726987777173183992183

theorem tailTrace_6100964 : CollatzResearch.WordTrace tailWord_6100964 prefixEnd_6100964 3132726987777173183992183 := by
  unfold tailWord_6100964
  simp only [CollatzResearch.WordTrace]
  refine ⟨111260218934628432270750973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148346958579504576361001297 111260218934628432270750973)
  ·
    refine ⟨41722582100485662101531615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111260218934628432270750973 41722582100485662101531615)
    ·
      refine ⟨62583873150728493152297423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41722582100485662101531615 62583873150728493152297423)
      ·
        refine ⟨93875809726092739728446135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62583873150728493152297423 93875809726092739728446135)
        ·
          refine ⟨140813714589139109592669203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93875809726092739728446135 140813714589139109592669203)
          ·
            refine ⟨211220571883708664389003805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140813714589139109592669203 211220571883708664389003805)
            ·
              refine ⟨79207714456390749145876427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211220571883708664389003805 79207714456390749145876427)
              ·
                refine ⟨118811571684586123718814641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79207714456390749145876427 118811571684586123718814641)
                ·
                  refine ⟨89108678763439592789110981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118811571684586123718814641 89108678763439592789110981)
                  ·
                    refine ⟨16707877268144923647958309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89108678763439592789110981 16707877268144923647958309)
                    ·
                      refine ⟨3132726987777173183992183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16707877268144923647958309 3132726987777173183992183)
                      ·
                        rfl

theorem cell23_6100964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_6100964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6100964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6100964 prefixEnd_6100964 := by exact prefixLift 6100964
  have htrace : WordTrace (prefixWord ++ tailWord_6100964) baseStart_6100964 baseEnd_6100964 := by
    simpa [prefixWord, tailWord_6100964, baseEnd_6100964] using wordTrace_append hprefix tailTrace_6100964
  have hstable : (prefixWord ++ tailWord_6100964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6100964).length < 2 ^ (prefixWord ++ tailWord_6100964).sum := by decide
  have hdescent : baseEnd_6100964 < baseStart_6100964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6100964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101011 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 3, 5, 2]
def baseStart_6101011 : Nat := 118140960795 + 6101011 * 2 ^ 59
def prefixEnd_6101011 : Nat := 4983230072969 + 3 ^ 40 * 6101011 * 2
def baseEnd_6101011 : Nat := 3132751121367934500104467

theorem tailTrace_6101011 : CollatzResearch.WordTrace tailWord_6101011 prefixEnd_6101011 3132751121367934500104467 := by
  unfold tailWord_6101011
  simp only [CollatzResearch.WordTrace]
  refine ⟨222522152100086591568462887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148348101400057727712308591 222522152100086591568462887)
  ·
    refine ⟨333783228150129887352694331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222522152100086591568462887 333783228150129887352694331)
    ·
      refine ⟨500674842225194831029041497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333783228150129887352694331 500674842225194831029041497)
      ·
        refine ⟨375506131668896123271781123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 500674842225194831029041497 375506131668896123271781123)
        ·
          refine ⟨563259197503344184907671685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375506131668896123271781123 563259197503344184907671685)
          ·
            refine ⟨105611099531877034670188441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 563259197503344184907671685 105611099531877034670188441)
            ·
              refine ⟨79208324648907776002641331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105611099531877034670188441 79208324648907776002641331)
              ·
                refine ⟨118812486973361664003961997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79208324648907776002641331 118812486973361664003961997)
                ·
                  refine ⟨44554682615010624001485749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118812486973361664003961997 44554682615010624001485749)
                  ·
                    refine ⟨4177001495157246000139289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44554682615010624001485749 4177001495157246000139289)
                    ·
                      refine ⟨3132751121367934500104467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4177001495157246000139289 3132751121367934500104467)
                      ·
                        rfl

theorem cell23_6101011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 5, 2].length) (baseStart_6101011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101011 prefixEnd_6101011 := by exact prefixLift 6101011
  have htrace : WordTrace (prefixWord ++ tailWord_6101011) baseStart_6101011 baseEnd_6101011 := by
    simpa [prefixWord, tailWord_6101011, baseEnd_6101011] using wordTrace_append hprefix tailTrace_6101011
  have hstable : (prefixWord ++ tailWord_6101011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101011).length < 2 ^ (prefixWord ++ tailWord_6101011).sum := by decide
  have hdescent : baseEnd_6101011 < baseStart_6101011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101064 : List Nat := [2, 1, 3, 1, 1, 1, 2, 12]
def baseStart_6101064 : Nat := 118140960795 + 6101064 * 2 ^ 59
def prefixEnd_6101064 : Nat := 4983230072969 + 3 ^ 40 * 6101064 * 2
def baseEnd_6101064 : Nat := 116028827253430473805249

theorem tailTrace_6101064 : CollatzResearch.WordTrace tailWord_6101064 prefixEnd_6101064 116028827253430473805249 := by
  unfold tailWord_6101064
  simp only [CollatzResearch.WordTrace]
  refine ⟨111262042584447290810071123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148349390112596387746761497 111262042584447290810071123)
  ·
    refine ⟨166893063876670936215106685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111262042584447290810071123 166893063876670936215106685)
    ·
      refine ⟨62584898953751601080665007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166893063876670936215106685 62584898953751601080665007)
      ·
        refine ⟨93877348430627401620997511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62584898953751601080665007 93877348430627401620997511)
        ·
          refine ⟨140816022645941102431496267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93877348430627401620997511 140816022645941102431496267)
          ·
            refine ⟨211224033968911653647244401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140816022645941102431496267 211224033968911653647244401)
            ·
              refine ⟨158418025476683740235433301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211224033968911653647244401 158418025476683740235433301)
              ·
                refine ⟨116028827253430473805249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 158418025476683740235433301 116028827253430473805249)
                ·
                  rfl

theorem cell23_6101064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 12].length) (baseStart_6101064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101064 prefixEnd_6101064 := by exact prefixLift 6101064
  have htrace : WordTrace (prefixWord ++ tailWord_6101064) baseStart_6101064 baseEnd_6101064 := by
    simpa [prefixWord, tailWord_6101064, baseEnd_6101064] using wordTrace_append hprefix tailTrace_6101064
  have hstable : (prefixWord ++ tailWord_6101064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101064).length < 2 ^ (prefixWord ++ tailWord_6101064).sum := by decide
  have hdescent : baseEnd_6101064 < baseStart_6101064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101068 : List Nat := [2, 2, 1, 3, 1, 1, 4, 3, 2, 4]
def baseStart_6101068 : Nat := 118140960795 + 6101068 * 2 ^ 59
def prefixEnd_6101068 : Nat := 4983230072969 + 3 ^ 40 * 6101068 * 2
def baseEnd_6101068 : Nat := 1044260129921746925697235

theorem tailTrace_6101068 : CollatzResearch.WordTrace tailWord_6101068 prefixEnd_6101068 1044260129921746925697235 := by
  unfold tailWord_6101068
  simp only [CollatzResearch.WordTrace]
  refine ⟨111262115530440045151643929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148349487373920060202191905 111262115530440045151643929)
  ·
    refine ⟨83446586647830033863732947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111262115530440045151643929 83446586647830033863732947)
    ·
      refine ⟨125169879971745050795599421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83446586647830033863732947 125169879971745050795599421)
      ·
        refine ⟨46938704989404394048349783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125169879971745050795599421 46938704989404394048349783)
        ·
          refine ⟨70408057484106591072524675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46938704989404394048349783 70408057484106591072524675)
          ·
            refine ⟨105612086226159886608787013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70408057484106591072524675 105612086226159886608787013)
            ·
              refine ⟨19802266167404978739147565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105612086226159886608787013 19802266167404978739147565)
              ·
                refine ⟨7425849812776867027180337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19802266167404978739147565 7425849812776867027180337)
                ·
                  refine ⟨5569387359582650270385253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7425849812776867027180337 5569387359582650270385253)
                  ·
                    refine ⟨1044260129921746925697235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5569387359582650270385253 1044260129921746925697235)
                    ·
                      rfl

theorem cell23_6101068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 2, 4].length) (baseStart_6101068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101068 prefixEnd_6101068 := by exact prefixLift 6101068
  have htrace : WordTrace (prefixWord ++ tailWord_6101068) baseStart_6101068 baseEnd_6101068 := by
    simpa [prefixWord, tailWord_6101068, baseEnd_6101068] using wordTrace_append hprefix tailTrace_6101068
  have hstable : (prefixWord ++ tailWord_6101068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101068).length < 2 ^ (prefixWord ++ tailWord_6101068).sum := by decide
  have hdescent : baseEnd_6101068 < baseStart_6101068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101081 : List Nat := [1, 2, 1, 2, 2, 1, 7, 7]
def baseStart_6101081 : Nat := 118140960795 + 6101081 * 2 ^ 59
def prefixEnd_6101081 : Nat := 4983230072969 + 3 ^ 40 * 6101081 * 2
def baseEnd_6101081 : Nat := 116029150556064786156635

theorem tailTrace_6101081 : CollatzResearch.WordTrace tailWord_6101081 prefixEnd_6101081 116029150556064786156635 := by
  unfold tailWord_6101081
  simp only [CollatzResearch.WordTrace]
  refine ⟨222524705209832993523511097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148349803473221995682340731 222524705209832993523511097)
  ·
    refine ⟨166893528907374745142633323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222524705209832993523511097 166893528907374745142633323)
    ·
      refine ⟨250340293361062117713949985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166893528907374745142633323 250340293361062117713949985)
      ·
        refine ⟨187755220020796588285462489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250340293361062117713949985 187755220020796588285462489)
        ·
          refine ⟨140816415015597441214096867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187755220020796588285462489 140816415015597441214096867)
          ·
            refine ⟨211224622523396161821145301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140816415015597441214096867 211224622523396161821145301)
            ·
              refine ⟨4950577090392097542683093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 211224622523396161821145301 4950577090392097542683093)
              ·
                refine ⟨116029150556064786156635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4950577090392097542683093 116029150556064786156635)
                ·
                  rfl

theorem cell23_6101081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 7].length) (baseStart_6101081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101081 prefixEnd_6101081 := by exact prefixLift 6101081
  have htrace : WordTrace (prefixWord ++ tailWord_6101081) baseStart_6101081 baseEnd_6101081 := by
    simpa [prefixWord, tailWord_6101081, baseEnd_6101081] using wordTrace_append hprefix tailTrace_6101081
  have hstable : (prefixWord ++ tailWord_6101081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101081).length < 2 ^ (prefixWord ++ tailWord_6101081).sum := by decide
  have hdescent : baseEnd_6101081 < baseStart_6101081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101092 : List Nat := [2, 3, 1, 1, 2, 1, 3, 5, 1, 2, 2]
def baseStart_6101092 : Nat := 118140960795 + 6101092 * 2 ^ 59
def prefixEnd_6101092 : Nat := 4983230072969 + 3 ^ 40 * 6101092 * 2
def baseEnd_6101092 : Nat := 3132792713300948683191595

theorem tailTrace_6101092 : CollatzResearch.WordTrace tailWord_6101092 prefixEnd_6101092 3132792713300948683191595 := by
  unfold tailWord_6101092
  simp only [CollatzResearch.WordTrace]
  refine ⟨111262553206396571201080765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148350070941862094934774353 111262553206396571201080765)
  ·
    refine ⟨41723457452398714200405287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111262553206396571201080765 41723457452398714200405287)
    ·
      refine ⟨62585186178598071300607931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41723457452398714200405287 62585186178598071300607931)
      ·
        refine ⟨93877779267897106950911897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62585186178598071300607931 93877779267897106950911897)
        ·
          refine ⟨70408334450922830213183923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93877779267897106950911897 70408334450922830213183923)
          ·
            refine ⟨105612501676384245319775885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70408334450922830213183923 105612501676384245319775885)
            ·
              refine ⟨39604688128644091994915957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105612501676384245319775885 39604688128644091994915957)
              ·
                refine ⟨3712939512060383624523371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39604688128644091994915957 3712939512060383624523371)
                ·
                  refine ⟨5569409268090575436785057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3712939512060383624523371 5569409268090575436785057)
                  ·
                    refine ⟨4177056951067931577588793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5569409268090575436785057 4177056951067931577588793)
                    ·
                      refine ⟨3132792713300948683191595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4177056951067931577588793 3132792713300948683191595)
                      ·
                        rfl

theorem cell23_6101092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 1, 2, 2].length) (baseStart_6101092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101092 prefixEnd_6101092 := by exact prefixLift 6101092
  have htrace : WordTrace (prefixWord ++ tailWord_6101092) baseStart_6101092 baseEnd_6101092 := by
    simpa [prefixWord, tailWord_6101092, baseEnd_6101092] using wordTrace_append hprefix tailTrace_6101092
  have hstable : (prefixWord ++ tailWord_6101092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101092).length < 2 ^ (prefixWord ++ tailWord_6101092).sum := by decide
  have hdescent : baseEnd_6101092 < baseStart_6101092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101125 : List Nat := [1, 3, 1, 1, 5, 3, 1, 1, 1, 3, 3]
def baseStart_6101125 : Nat := 118140960795 + 6101125 * 2 ^ 59
def prefixEnd_6101125 : Nat := 4983230072969 + 3 ^ 40 * 6101125 * 2
def baseEnd_6101125 : Nat := 3132809658162547054078943

theorem tailTrace_6101125 : CollatzResearch.WordTrace tailWord_6101125 prefixEnd_6101125 3132809658162547054078943 := by
  unfold tailWord_6101125
  simp only [CollatzResearch.WordTrace]
  refine ⟨222526310021673589038112829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148350873347782392692075219 222526310021673589038112829)
  ·
    refine ⟨83447366258127595889292311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222526310021673589038112829 83447366258127595889292311)
    ·
      refine ⟨125171049387191393833938467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83447366258127595889292311 125171049387191393833938467)
      ·
        refine ⟨187756574080787090750907701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125171049387191393833938467 187756574080787090750907701)
        ·
          refine ⟨17602178820073789757897597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 187756574080787090750907701 17602178820073789757897597)
          ·
            refine ⟨6600817057527671159211599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17602178820073789757897597 6600817057527671159211599)
            ·
              refine ⟨9901225586291506738817399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6600817057527671159211599 9901225586291506738817399)
              ·
                refine ⟨14851838379437260108226099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9901225586291506738817399 14851838379437260108226099)
                ·
                  refine ⟨22277757569155890162339149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14851838379437260108226099 22277757569155890162339149)
                  ·
                    refine ⟨8354159088433458810877181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22277757569155890162339149 8354159088433458810877181)
                    ·
                      refine ⟨3132809658162547054078943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8354159088433458810877181 3132809658162547054078943)
                      ·
                        rfl

theorem cell23_6101125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 3, 3].length) (baseStart_6101125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101125 prefixEnd_6101125 := by exact prefixLift 6101125
  have htrace : WordTrace (prefixWord ++ tailWord_6101125) baseStart_6101125 baseEnd_6101125 := by
    simpa [prefixWord, tailWord_6101125, baseEnd_6101125] using wordTrace_append hprefix tailTrace_6101125
  have hstable : (prefixWord ++ tailWord_6101125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101125).length < 2 ^ (prefixWord ++ tailWord_6101125).sum := by decide
  have hdescent : baseEnd_6101125 < baseStart_6101125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101186 : List Nat := [3, 5, 1, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_6101186 : Nat := 118140960795 + 6101186 * 2 ^ 59
def prefixEnd_6101186 : Nat := 4983230072969 + 3 ^ 40 * 6101186 * 2
def baseEnd_6101186 : Nat := 3132840980482471315416163

theorem tailTrace_6101186 : CollatzResearch.WordTrace tailWord_6101186 prefixEnd_6101186 3132840980482471315416163 := by
  unfold tailWord_6101186
  simp only [CollatzResearch.WordTrace]
  refine ⟨55632133718613149114020853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148352356582968397637388941 55632133718613149114020853)
  ·
    refine ⟨5215512536119982729439455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55632133718613149114020853 5215512536119982729439455)
    ·
      refine ⟨7823268804179974094159183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5215512536119982729439455 7823268804179974094159183)
      ·
        refine ⟨11734903206269961141238775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7823268804179974094159183 11734903206269961141238775)
        ·
          refine ⟨17602354809404941711858163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11734903206269961141238775 17602354809404941711858163)
          ·
            refine ⟨26403532214107412567787245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17602354809404941711858163 26403532214107412567787245)
            ·
              refine ⟨9901324580290279712920217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26403532214107412567787245 9901324580290279712920217)
              ·
                refine ⟨7425993435217709784690163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9901324580290279712920217 7425993435217709784690163)
                ·
                  refine ⟨11138990152826564677035245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7425993435217709784690163 11138990152826564677035245)
                  ·
                    refine ⟨4177121307309961753888217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11138990152826564677035245 4177121307309961753888217)
                    ·
                      refine ⟨3132840980482471315416163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4177121307309961753888217 3132840980482471315416163)
                      ·
                        rfl

theorem cell23_6101186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_6101186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101186 prefixEnd_6101186 := by exact prefixLift 6101186
  have htrace : WordTrace (prefixWord ++ tailWord_6101186) baseStart_6101186 baseEnd_6101186 := by
    simpa [prefixWord, tailWord_6101186, baseEnd_6101186] using wordTrace_append hprefix tailTrace_6101186
  have hstable : (prefixWord ++ tailWord_6101186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101186).length < 2 ^ (prefixWord ++ tailWord_6101186).sum := by decide
  have hdescent : baseEnd_6101186 < baseStart_6101186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101201 : List Nat := [1, 2, 2, 1, 2, 2, 2, 3, 1, 7]
def baseStart_6101201 : Nat := 118140960795 + 6101201 * 2 ^ 59
def prefixEnd_6101201 : Nat := 4983230072969 + 3 ^ 40 * 6101201 * 2
def baseEnd_6101201 : Nat := 1044282894230762918909531

theorem tailTrace_6101201 : CollatzResearch.WordTrace tailWord_6101201 prefixEnd_6101201 1044282894230762918909531 := by
  unfold tailWord_6101201
  simp only [CollatzResearch.WordTrace]
  refine ⟨222529081969398254017879457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148352721312932169345252971 222529081969398254017879457)
  ·
    refine ⟨166896811477048690513409593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222529081969398254017879457 166896811477048690513409593)
    ·
      refine ⟨125172608607786517885057195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166896811477048690513409593 125172608607786517885057195)
      ·
        refine ⟨187758912911679776827585793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125172608607786517885057195 187758912911679776827585793)
        ·
          refine ⟨140819184683759832620689345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187758912911679776827585793 140819184683759832620689345)
          ·
            refine ⟨105614388512819874465517009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140819184683759832620689345 105614388512819874465517009)
            ·
              refine ⟨79210791384614905849137757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105614388512819874465517009 79210791384614905849137757)
              ·
                refine ⟨29704046769230589693426659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79210791384614905849137757 29704046769230589693426659)
                ·
                  refine ⟨44556070153845884540139989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29704046769230589693426659 44556070153845884540139989)
                  ·
                    refine ⟨1044282894230762918909531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44556070153845884540139989 1044282894230762918909531)
                    ·
                      rfl

theorem cell23_6101201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_6101201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101201 prefixEnd_6101201 := by exact prefixLift 6101201
  have htrace : WordTrace (prefixWord ++ tailWord_6101201) baseStart_6101201 baseEnd_6101201 := by
    simpa [prefixWord, tailWord_6101201, baseEnd_6101201] using wordTrace_append hprefix tailTrace_6101201
  have hstable : (prefixWord ++ tailWord_6101201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101201).length < 2 ^ (prefixWord ++ tailWord_6101201).sum := by decide
  have hdescent : baseEnd_6101201 < baseStart_6101201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101211 : List Nat := [1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 5]
def baseStart_6101211 : Nat := 118140960795 + 6101211 * 2 ^ 59
def prefixEnd_6101211 : Nat := 4983230072969 + 3 ^ 40 * 6101211 * 2
def baseEnd_6101211 : Nat := 3132853817498833717603547

theorem tailTrace_6101211 : CollatzResearch.WordTrace tailWord_6101211 prefixEnd_6101211 3132853817498833717603547 := by
  unfold tailWord_6101211
  simp only [CollatzResearch.WordTrace]
  refine ⟨222529446699362025725743487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148352964466241350483828991 222529446699362025725743487)
  ·
    refine ⟨333794170049043038588615231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222529446699362025725743487 333794170049043038588615231)
    ·
      refine ⟨500691255073564557882922847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333794170049043038588615231 500691255073564557882922847)
      ·
        refine ⟨751036882610346836824384271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500691255073564557882922847 751036882610346836824384271)
        ·
          refine ⟨1126555323915520255236576407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751036882610346836824384271 1126555323915520255236576407)
          ·
            refine ⟨1689832985873280382854864611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1126555323915520255236576407 1689832985873280382854864611)
            ·
              refine ⟨2534749478809920574282296917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1689832985873280382854864611 2534749478809920574282296917)
              ·
                refine ⟨29704095454803756729870667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2534749478809920574282296917 29704095454803756729870667)
                ·
                  refine ⟨44556143182205635094806001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29704095454803756729870667 44556143182205635094806001)
                  ·
                    refine ⟨33417107386654226321104501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44556143182205635094806001 33417107386654226321104501)
                    ·
                      refine ⟨3132853817498833717603547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33417107386654226321104501 3132853817498833717603547)
                      ·
                        rfl

theorem cell23_6101211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 5].length) (baseStart_6101211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101211 prefixEnd_6101211 := by exact prefixLift 6101211
  have htrace : WordTrace (prefixWord ++ tailWord_6101211) baseStart_6101211 baseEnd_6101211 := by
    simpa [prefixWord, tailWord_6101211, baseEnd_6101211] using wordTrace_append hprefix tailTrace_6101211
  have hstable : (prefixWord ++ tailWord_6101211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101211).length < 2 ^ (prefixWord ++ tailWord_6101211).sum := by decide
  have hdescent : baseEnd_6101211 < baseStart_6101211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101248 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 5, 4]
def baseStart_6101248 : Nat := 118140960795 + 6101248 * 2 ^ 59
def prefixEnd_6101248 : Nat := 4983230072969 + 3 ^ 40 * 6101248 * 2
def baseEnd_6101248 : Nat := 1044290938761016690946959

theorem tailTrace_6101248 : CollatzResearch.WordTrace tailWord_6101248 prefixEnd_6101248 1044290938761016690946959 := by
  unfold tailWord_6101248
  simp only [CollatzResearch.WordTrace]
  refine ⟨111265398100113990522420199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148353864133485320696560265 111265398100113990522420199)
  ·
    refine ⟨166898097150170985783630299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111265398100113990522420199 166898097150170985783630299)
    ·
      refine ⟨250347145725256478675445449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166898097150170985783630299 250347145725256478675445449)
      ·
        refine ⟨187760359293942359006584087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250347145725256478675445449 187760359293942359006584087)
        ·
          refine ⟨281640538940913538509876131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187760359293942359006584087 281640538940913538509876131)
          ·
            refine ⟨422460808411370307764814197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281640538940913538509876131 422460808411370307764814197)
            ·
              refine ⟨39605700788565966352951331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 422460808411370307764814197 39605700788565966352951331)
              ·
                refine ⟨59408551182848949529426997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39605700788565966352951331 59408551182848949529426997)
                ·
                  refine ⟨5569551673392089018383781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59408551182848949529426997 5569551673392089018383781)
                  ·
                    refine ⟨1044290938761016690946959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5569551673392089018383781 1044290938761016690946959)
                    ·
                      rfl

theorem cell23_6101248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 5, 4].length) (baseStart_6101248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101248 prefixEnd_6101248 := by exact prefixLift 6101248
  have htrace : WordTrace (prefixWord ++ tailWord_6101248) baseStart_6101248 baseEnd_6101248 := by
    simpa [prefixWord, tailWord_6101248, baseEnd_6101248] using wordTrace_append hprefix tailTrace_6101248
  have hstable : (prefixWord ++ tailWord_6101248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101248).length < 2 ^ (prefixWord ++ tailWord_6101248).sum := by decide
  have hdescent : baseEnd_6101248 < baseStart_6101248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101252 : List Nat := [2, 3, 2, 2, 3, 2, 1, 1, 2, 5]
def baseStart_6101252 : Nat := 118140960795 + 6101252 * 2 ^ 59
def prefixEnd_6101252 : Nat := 4983230072969 + 3 ^ 40 * 6101252 * 2
def baseEnd_6101252 : Nat := 1044291623401889352396953

theorem tailTrace_6101252 : CollatzResearch.WordTrace tailWord_6101252 prefixEnd_6101252 1044291623401889352396953 := by
  unfold tailWord_6101252
  simp only [CollatzResearch.WordTrace]
  refine ⟨111265471046106744863993005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148353961394808993151990673 111265471046106744863993005)
  ·
    refine ⟨41724551642290029323997377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111265471046106744863993005 41724551642290029323997377)
    ·
      refine ⟨31293413731717521992998033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41724551642290029323997377 31293413731717521992998033)
      ·
        refine ⟨23470060298788141494748525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31293413731717521992998033 23470060298788141494748525)
        ·
          refine ⟨8801272612045553060530697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23470060298788141494748525 8801272612045553060530697)
          ·
            refine ⟨6600954459034164795398023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8801272612045553060530697 6600954459034164795398023)
            ·
              refine ⟨9901431688551247193097035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6600954459034164795398023 9901431688551247193097035)
              ·
                refine ⟨14852147532826870789645553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9901431688551247193097035 14852147532826870789645553)
                ·
                  refine ⟨11139110649620153092234165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14852147532826870789645553 11139110649620153092234165)
                  ·
                    refine ⟨1044291623401889352396953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11139110649620153092234165 1044291623401889352396953)
                    ·
                      rfl

theorem cell23_6101252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_6101252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101252 prefixEnd_6101252 := by exact prefixLift 6101252
  have htrace : WordTrace (prefixWord ++ tailWord_6101252) baseStart_6101252 baseEnd_6101252 := by
    simpa [prefixWord, tailWord_6101252, baseEnd_6101252] using wordTrace_append hprefix tailTrace_6101252
  have hstable : (prefixWord ++ tailWord_6101252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101252).length < 2 ^ (prefixWord ++ tailWord_6101252).sum := by decide
  have hdescent : baseEnd_6101252 < baseStart_6101252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101282 : List Nat := [3, 3, 1, 1, 3, 2, 2, 1, 3, 4]
def baseStart_6101282 : Nat := 118140960795 + 6101282 * 2 ^ 59
def prefixEnd_6101282 : Nat := 4983230072969 + 3 ^ 40 * 6101282 * 2
def baseEnd_6101282 : Nat := 1044296758208434313271907

theorem tailTrace_6101282 : CollatzResearch.WordTrace tailWord_6101282 prefixEnd_6101282 1044296758208434313271907 := by
  unfold tailWord_6101282
  simp only [CollatzResearch.WordTrace]
  refine ⟨55633009070526201212894525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148354690854736536567718733 55633009070526201212894525)
  ·
    refine ⟨20862378401447325454835447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55633009070526201212894525 20862378401447325454835447)
    ·
      refine ⟨31293567602170988182253171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20862378401447325454835447 31293567602170988182253171)
      ·
        refine ⟨46940351403256482273379757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31293567602170988182253171 46940351403256482273379757)
        ·
          refine ⟨17602631776221180852517409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46940351403256482273379757 17602631776221180852517409)
          ·
            refine ⟨13201973832165885639388057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17602631776221180852517409 13201973832165885639388057)
            ·
              refine ⟨9901480374124414229541043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13201973832165885639388057 9901480374124414229541043)
              ·
                refine ⟨14852220561186621344311565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9901480374124414229541043 14852220561186621344311565)
                ·
                  refine ⟨5569582710444983004116837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14852220561186621344311565 5569582710444983004116837)
                  ·
                    refine ⟨1044296758208434313271907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5569582710444983004116837 1044296758208434313271907)
                    ·
                      rfl

theorem cell23_6101282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_6101282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101282 prefixEnd_6101282 := by exact prefixLift 6101282
  have htrace : WordTrace (prefixWord ++ tailWord_6101282) baseStart_6101282 baseEnd_6101282 := by
    simpa [prefixWord, tailWord_6101282, baseEnd_6101282] using wordTrace_append hprefix tailTrace_6101282
  have hstable : (prefixWord ++ tailWord_6101282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101282).length < 2 ^ (prefixWord ++ tailWord_6101282).sum := by decide
  have hdescent : baseEnd_6101282 < baseStart_6101282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101315 : List Nat := [1, 1, 1, 3, 1, 3, 4, 1, 1, 5, 2]
def baseStart_6101315 : Nat := 118140960795 + 6101315 * 2 ^ 59
def prefixEnd_6101315 : Nat := 4983230072969 + 3 ^ 40 * 6101315 * 2
def baseEnd_6101315 : Nat := 3132907219486901310703069

theorem tailTrace_6101315 : CollatzResearch.WordTrace tailWord_6101315 prefixEnd_6101315 3132907219486901310703069 := by
  unfold tailWord_6101315
  simp only [CollatzResearch.WordTrace]
  refine ⟨222533239890985251487529399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148355493260656834325019599 222533239890985251487529399)
  ·
    refine ⟨333799859836477877231294099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222533239890985251487529399 333799859836477877231294099)
    ·
      refine ⟨500699789754716815846941149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333799859836477877231294099 500699789754716815846941149)
      ·
        refine ⟨187762421158018805942602931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 500699789754716815846941149 187762421158018805942602931)
        ·
          refine ⟨281643631737028208913904397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187762421158018805942602931 281643631737028208913904397)
          ·
            refine ⟨105616361901385578342714149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281643631737028208913904397 105616361901385578342714149)
            ·
              refine ⟨19803067856509795939258903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105616361901385578342714149 19803067856509795939258903)
              ·
                refine ⟨29704601784764693908888355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19803067856509795939258903 29704601784764693908888355)
                ·
                  refine ⟨44556902677147040863332533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29704601784764693908888355 44556902677147040863332533)
                  ·
                    refine ⟨4177209625982535080937425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44556902677147040863332533 4177209625982535080937425)
                    ·
                      refine ⟨3132907219486901310703069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4177209625982535080937425 3132907219486901310703069)
                      ·
                        rfl

theorem cell23_6101315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 5, 2].length) (baseStart_6101315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101315 prefixEnd_6101315 := by exact prefixLift 6101315
  have htrace : WordTrace (prefixWord ++ tailWord_6101315) baseStart_6101315 baseEnd_6101315 := by
    simpa [prefixWord, tailWord_6101315, baseEnd_6101315] using wordTrace_append hprefix tailTrace_6101315
  have hstable : (prefixWord ++ tailWord_6101315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101315).length < 2 ^ (prefixWord ++ tailWord_6101315).sum := by decide
  have hdescent : baseEnd_6101315 < baseStart_6101315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101332 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 4, 3, 2]
def baseStart_6101332 : Nat := 118140960795 + 6101332 * 2 ^ 59
def prefixEnd_6101332 : Nat := 4983230072969 + 3 ^ 40 * 6101332 * 2
def baseEnd_6101332 : Nat := 3132915948658027744190491

theorem tailTrace_6101332 : CollatzResearch.WordTrace tailWord_6101332 prefixEnd_6101332 3132915948658027744190491 := by
  unfold tailWord_6101332
  simp only [CollatzResearch.WordTrace]
  refine ⟨111266929965961831695449125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148355906621282442260598833 111266929965961831695449125)
  ·
    refine ⟨20862549368617843442896711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111266929965961831695449125 20862549368617843442896711)
    ·
      refine ⟨31293824052926765164345067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20862549368617843442896711 31293824052926765164345067)
      ·
        refine ⟨46940736079390147746517601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31293824052926765164345067 46940736079390147746517601)
        ·
          refine ⟨35205552059542610809888201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46940736079390147746517601 35205552059542610809888201)
          ·
            refine ⟨26404164044656958107416151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35205552059542610809888201 26404164044656958107416151)
            ·
              refine ⟨39606246066985437161124227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26404164044656958107416151 39606246066985437161124227)
              ·
                refine ⟨59409369100478155741686341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39606246066985437161124227 59409369100478155741686341)
                ·
                  refine ⟨11139256706339654201566189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59409369100478155741686341 11139256706339654201566189)
                  ·
                    refine ⟨4177221264877370325587321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11139256706339654201566189 4177221264877370325587321)
                    ·
                      refine ⟨3132915948658027744190491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4177221264877370325587321 3132915948658027744190491)
                      ·
                        rfl

theorem cell23_6101332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_6101332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101332 prefixEnd_6101332 := by exact prefixLift 6101332
  have htrace : WordTrace (prefixWord ++ tailWord_6101332) baseStart_6101332 baseEnd_6101332 := by
    simpa [prefixWord, tailWord_6101332, baseEnd_6101332] using wordTrace_append hprefix tailTrace_6101332
  have hstable : (prefixWord ++ tailWord_6101332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101332).length < 2 ^ (prefixWord ++ tailWord_6101332).sum := by decide
  have hdescent : baseEnd_6101332 < baseStart_6101332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101355 : List Nat := [1, 1, 1, 1, 2, 2, 2, 7, 2, 4]
def baseStart_6101355 : Nat := 118140960795 + 6101355 * 2 ^ 59
def prefixEnd_6101355 : Nat := 4983230072969 + 3 ^ 40 * 6101355 * 2
def baseEnd_6101355 : Nat := 1044309252904360384734295

theorem tailTrace_6101355 : CollatzResearch.WordTrace tailWord_6101355 prefixEnd_6101355 1044309252904360384734295 := by
  unfold tailWord_6101355
  simp only [CollatzResearch.WordTrace]
  refine ⟨222534698810840338318985519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148356465873893558879323679 222534698810840338318985519)
  ·
    refine ⟨333802048216260507478478279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222534698810840338318985519 333802048216260507478478279)
    ·
      refine ⟨500703072324390761217717419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333802048216260507478478279 500703072324390761217717419)
      ·
        refine ⟨751054608486586141826576129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500703072324390761217717419 751054608486586141826576129)
        ·
          refine ⟨563290956364939606369932097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 751054608486586141826576129 563290956364939606369932097)
          ·
            refine ⟨422468217273704704777449073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 563290956364939606369932097 422468217273704704777449073)
            ·
              refine ⟨316851162955278528583086805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 422468217273704704777449073 316851162955278528583086805)
              ·
                refine ⟨7426199131764340513666097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 316851162955278528583086805 7426199131764340513666097)
                ·
                  refine ⟨5569649348823255385249573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7426199131764340513666097 5569649348823255385249573)
                  ·
                    refine ⟨1044309252904360384734295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5569649348823255385249573 1044309252904360384734295)
                    ·
                      rfl

theorem cell23_6101355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 4].length) (baseStart_6101355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101355 prefixEnd_6101355 := by exact prefixLift 6101355
  have htrace : WordTrace (prefixWord ++ tailWord_6101355) baseStart_6101355 baseEnd_6101355 := by
    simpa [prefixWord, tailWord_6101355, baseEnd_6101355] using wordTrace_append hprefix tailTrace_6101355
  have hstable : (prefixWord ++ tailWord_6101355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101355).length < 2 ^ (prefixWord ++ tailWord_6101355).sum := by decide
  have hdescent : baseEnd_6101355 < baseStart_6101355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101362 : List Nat := [3, 2, 1, 2, 1, 3, 3, 2, 1, 1, 4]
def baseStart_6101362 : Nat := 118140960795 + 6101362 * 2 ^ 59
def prefixEnd_6101362 : Nat := 4983230072969 + 3 ^ 40 * 6101362 * 2
def baseEnd_6101362 : Nat := 3132931353077662626815353

theorem tailTrace_6101362 : CollatzResearch.WordTrace tailWord_6101362 prefixEnd_6101362 3132931353077662626815353 := by
  unfold tailWord_6101362
  simp only [CollatzResearch.WordTrace]
  refine ⟨55633738530453744628622585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148356636081209985676326893 55633738530453744628622585)
  ·
    refine ⟨41725303897840308471466939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55633738530453744628622585 41725303897840308471466939)
    ·
      refine ⟨62587955846760462707200409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41725303897840308471466939 62587955846760462707200409)
      ·
        refine ⟨46940966885070347030400307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62587955846760462707200409 46940966885070347030400307)
        ·
          refine ⟨70411450327605520545600461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46940966885070347030400307 70411450327605520545600461)
          ·
            refine ⟨26404293872852070204600173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70411450327605520545600461 26404293872852070204600173)
            ·
              refine ⟨9901610202319526326725065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26404293872852070204600173 9901610202319526326725065)
              ·
                refine ⟨7426207651739644745043799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9901610202319526326725065 7426207651739644745043799)
                ·
                  refine ⟨11139311477609467117565699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7426207651739644745043799 11139311477609467117565699)
                  ·
                    refine ⟨16708967216414200676348549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11139311477609467117565699 16708967216414200676348549)
                    ·
                      refine ⟨3132931353077662626815353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16708967216414200676348549 3132931353077662626815353)
                      ·
                        rfl

theorem cell23_6101362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_6101362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101362 prefixEnd_6101362 := by exact prefixLift 6101362
  have htrace : WordTrace (prefixWord ++ tailWord_6101362) baseStart_6101362 baseEnd_6101362 := by
    simpa [prefixWord, tailWord_6101362, baseEnd_6101362] using wordTrace_append hprefix tailTrace_6101362
  have hstable : (prefixWord ++ tailWord_6101362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101362).length < 2 ^ (prefixWord ++ tailWord_6101362).sum := by decide
  have hdescent : baseEnd_6101362 < baseStart_6101362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101379 : List Nat := [1, 1, 1, 3, 6, 1, 3, 1, 1, 1, 4]
def baseStart_6101379 : Nat := 118140960795 + 6101379 * 2 ^ 59
def prefixEnd_6101379 : Nat := 4983230072969 + 3 ^ 40 * 6101379 * 2
def baseEnd_6101379 : Nat := 3132940082248789060302775

theorem tailTrace_6101379 : CollatzResearch.WordTrace tailWord_6101379 prefixEnd_6101379 3132940082248789060302775 := by
  unfold tailWord_6101379
  simp only [CollatzResearch.WordTrace]
  refine ⟨222535574162753390417859191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148357049441835593611906127 222535574162753390417859191)
  ·
    refine ⟨333803361244130085626788787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222535574162753390417859191 333803361244130085626788787)
    ·
      refine ⟨500705041866195128440183181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333803361244130085626788787 500705041866195128440183181)
      ·
        refine ⟨187764390699823173165068693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 500705041866195128440183181 187764390699823173165068693)
        ·
          refine ⟨8801455814054211242112595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 187764390699823173165068693 8801455814054211242112595)
          ·
            refine ⟨13202183721081316863168893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8801455814054211242112595 13202183721081316863168893)
            ·
              refine ⟨4950818895405493823688335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13202183721081316863168893 4950818895405493823688335)
              ·
                refine ⟨7426228343108240735532503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4950818895405493823688335 7426228343108240735532503)
                ·
                  refine ⟨11139342514662361103298755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7426228343108240735532503 11139342514662361103298755)
                  ·
                    refine ⟨16709013771993541654948133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11139342514662361103298755 16709013771993541654948133)
                    ·
                      refine ⟨3132940082248789060302775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16709013771993541654948133 3132940082248789060302775)
                      ·
                        rfl

theorem cell23_6101379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 1, 1, 4].length) (baseStart_6101379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101379 prefixEnd_6101379 := by exact prefixLift 6101379
  have htrace : WordTrace (prefixWord ++ tailWord_6101379) baseStart_6101379 baseEnd_6101379 := by
    simpa [prefixWord, tailWord_6101379, baseEnd_6101379] using wordTrace_append hprefix tailTrace_6101379
  have hstable : (prefixWord ++ tailWord_6101379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101379).length < 2 ^ (prefixWord ++ tailWord_6101379).sum := by decide
  have hdescent : baseEnd_6101379 < baseStart_6101379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101409 : List Nat := [1, 2, 3, 5, 1, 1, 2, 1, 1, 2, 4]
def baseStart_6101409 : Nat := 118140960795 + 6101409 * 2 ^ 59
def prefixEnd_6101409 : Nat := 4983230072969 + 3 ^ 40 * 6101409 * 2
def baseEnd_6101409 : Nat := 3132955486668423942927637

theorem tailTrace_6101409 : CollatzResearch.WordTrace tailWord_6101409 prefixEnd_6101409 3132955486668423942927637 := by
  unfold tailWord_6101409
  simp only [CollatzResearch.WordTrace]
  refine ⟨222536668352644705541451281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148357778901763137027634187 222536668352644705541451281)
  ·
    refine ⟨166902501264483529156088461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222536668352644705541451281 166902501264483529156088461)
    ·
      refine ⟨62588437974181323433533173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166902501264483529156088461 62588437974181323433533173)
      ·
        refine ⟨5867666060079499071893735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62588437974181323433533173 5867666060079499071893735)
        ·
          refine ⟨8801499090119248607840603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5867666060079499071893735 8801499090119248607840603)
          ·
            refine ⟨13202248635178872911760905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8801499090119248607840603 13202248635178872911760905)
            ·
              refine ⟨9901686476384154683820679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13202248635178872911760905 9901686476384154683820679)
              ·
                refine ⟨14852529714576232025731019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9901686476384154683820679 14852529714576232025731019)
                ·
                  refine ⟨22278794571864348038596529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14852529714576232025731019 22278794571864348038596529)
                  ·
                    refine ⟨16709095928898261028947397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22278794571864348038596529 16709095928898261028947397)
                    ·
                      refine ⟨3132955486668423942927637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16709095928898261028947397 3132955486668423942927637)
                      ·
                        rfl

theorem cell23_6101409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_6101409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101409 prefixEnd_6101409 := by exact prefixLift 6101409
  have htrace : WordTrace (prefixWord ++ tailWord_6101409) baseStart_6101409 baseEnd_6101409 := by
    simpa [prefixWord, tailWord_6101409, baseEnd_6101409] using wordTrace_append hprefix tailTrace_6101409
  have hstable : (prefixWord ++ tailWord_6101409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101409).length < 2 ^ (prefixWord ++ tailWord_6101409).sum := by decide
  have hdescent : baseEnd_6101409 < baseStart_6101409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101462 : List Nat := [5, 2, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_6101462 : Nat := 118140960795 + 6101462 * 2 ^ 59
def prefixEnd_6101462 : Nat := 4983230072969 + 3 ^ 40 * 6101462 * 2
def baseEnd_6101462 : Nat := 1044327567047704078521631

theorem tailTrace_6101462 : CollatzResearch.WordTrace tailWord_6101462 prefixEnd_6101462 1044327567047704078521631 := by
  unfold tailWord_6101462
  simp only [CollatzResearch.WordTrace]
  refine ⟨13908662588840793474570665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148359067614301797062087093 13908662588840793474570665)
  ·
    refine ⟨10431496941630595105927999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13908662588840793474570665 10431496941630595105927999)
    ·
      refine ⟨15647245412445892658891999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10431496941630595105927999 15647245412445892658891999)
      ·
        refine ⟨23470868118668838988337999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15647245412445892658891999 23470868118668838988337999)
        ·
          refine ⟨35206302178003258482506999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23470868118668838988337999 35206302178003258482506999)
          ·
            refine ⟨52809453267004887723760499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35206302178003258482506999 52809453267004887723760499)
            ·
              refine ⟨79214179900507331585640749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52809453267004887723760499 79214179900507331585640749)
              ·
                refine ⟨29705317462690249344615281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79214179900507331585640749 29705317462690249344615281)
                ·
                  refine ⟨22278988097017687008461461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29705317462690249344615281 22278988097017687008461461)
                  ·
                    refine ⟨1044327567047704078521631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22278988097017687008461461 1044327567047704078521631)
                    ·
                      rfl

theorem cell23_6101462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_6101462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101462 prefixEnd_6101462 := by exact prefixLift 6101462
  have htrace : WordTrace (prefixWord ++ tailWord_6101462) baseStart_6101462 baseEnd_6101462 := by
    simpa [prefixWord, tailWord_6101462, baseEnd_6101462] using wordTrace_append hprefix tailTrace_6101462
  have hstable : (prefixWord ++ tailWord_6101462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101462).length < 2 ^ (prefixWord ++ tailWord_6101462).sum := by decide
  have hdescent : baseEnd_6101462 < baseStart_6101462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101465 : List Nat := [1, 2, 1, 2, 4, 1, 1, 3, 2, 2, 4]
def baseStart_6101465 : Nat := 118140960795 + 6101465 * 2 ^ 59
def prefixEnd_6101465 : Nat := 4983230072969 + 3 ^ 40 * 6101465 * 2
def baseEnd_6101465 : Nat := 3132984241585075723827379

theorem tailTrace_6101465 : CollatzResearch.WordTrace tailWord_6101465 prefixEnd_6101465 3132984241585075723827379 := by
  unfold tailWord_6101465
  simp only [CollatzResearch.WordTrace]
  refine ⟨222538710840441827105489849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148359140560294551403659899 222538710840441827105489849)
  ·
    refine ⟨166904033130331370329117387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222538710840441827105489849 166904033130331370329117387)
    ·
      refine ⟨250356049695497055493676081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166904033130331370329117387 250356049695497055493676081)
      ·
        refine ⟨187767037271622791620257061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250356049695497055493676081 187767037271622791620257061)
        ·
          refine ⟨35206319488429273428798199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187767037271622791620257061 35206319488429273428798199)
          ·
            refine ⟨52809479232643910143197299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35206319488429273428798199 52809479232643910143197299)
            ·
              refine ⟨79214218848965865214795949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52809479232643910143197299 79214218848965865214795949)
              ·
                refine ⟨29705332068362199455548481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79214218848965865214795949 29705332068362199455548481)
                ·
                  refine ⟨22278999051271649591661361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29705332068362199455548481 22278999051271649591661361)
                  ·
                    refine ⟨16709249288453737193746021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22278999051271649591661361 16709249288453737193746021)
                    ·
                      refine ⟨3132984241585075723827379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16709249288453737193746021 3132984241585075723827379)
                      ·
                        rfl

theorem cell23_6101465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_6101465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101465 prefixEnd_6101465 := by exact prefixLift 6101465
  have htrace : WordTrace (prefixWord ++ tailWord_6101465) baseStart_6101465 baseEnd_6101465 := by
    simpa [prefixWord, tailWord_6101465, baseEnd_6101465] using wordTrace_append hprefix tailTrace_6101465
  have hstable : (prefixWord ++ tailWord_6101465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101465).length < 2 ^ (prefixWord ++ tailWord_6101465).sum := by decide
  have hdescent : baseEnd_6101465 < baseStart_6101465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101512 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 2, 5, 2]
def baseStart_6101512 : Nat := 118140960795 + 6101512 * 2 ^ 59
def prefixEnd_6101512 : Nat := 4983230072969 + 3 ^ 40 * 6101512 * 2
def baseEnd_6101512 : Nat := 3133008375175837039939663

theorem tailTrace_6101512 : CollatzResearch.WordTrace tailWord_6101512 prefixEnd_6101512 3133008375175837039939663 := by
  unfold tailWord_6101512
  simp only [CollatzResearch.WordTrace]
  refine ⟨111270212535635777066225395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148360283380847702754967193 111270212535635777066225395)
  ·
    refine ⟨166905318803453665599338093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111270212535635777066225395 166905318803453665599338093)
    ·
      refine ⟨62589494551295124599751785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166905318803453665599338093 62589494551295124599751785)
      ·
        refine ⟨46942120913471343449813839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62589494551295124599751785 46942120913471343449813839)
        ·
          refine ⟨70413181370207015174720759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46942120913471343449813839 70413181370207015174720759)
          ·
            refine ⟨105619772055310522762081139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70413181370207015174720759 105619772055310522762081139)
            ·
              refine ⟨158429658082965784143121709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105619772055310522762081139 158429658082965784143121709)
              ·
                refine ⟨59411121781112169053670641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158429658082965784143121709 59411121781112169053670641)
                ·
                  refine ⟨44558341335834126790252981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59411121781112169053670641 44558341335834126790252981)
                  ·
                    refine ⟨4177344500234449386586217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44558341335834126790252981 4177344500234449386586217)
                    ·
                      refine ⟨3133008375175837039939663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4177344500234449386586217 3133008375175837039939663)
                      ·
                        rfl

theorem cell23_6101512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_6101512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101512 prefixEnd_6101512 := by exact prefixLift 6101512
  have htrace : WordTrace (prefixWord ++ tailWord_6101512) baseStart_6101512 baseEnd_6101512 := by
    simpa [prefixWord, tailWord_6101512, baseEnd_6101512] using wordTrace_append hprefix tailTrace_6101512
  have hstable : (prefixWord ++ tailWord_6101512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101512).length < 2 ^ (prefixWord ++ tailWord_6101512).sum := by decide
  have hdescent : baseEnd_6101512 < baseStart_6101512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101515 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 7]
def baseStart_6101515 : Nat := 118140960795 + 6101515 * 2 ^ 59
def prefixEnd_6101515 : Nat := 4983230072969 + 3 ^ 40 * 6101515 * 2
def baseEnd_6101515 : Nat := 3133009915617800528202149

theorem tailTrace_6101515 : CollatzResearch.WordTrace tailWord_6101515 prefixEnd_6101515 3133009915617800528202149 := by
  unfold tailWord_6101515
  simp only [CollatzResearch.WordTrace]
  refine ⟨222540534490260685644809999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148360356326840457096539999 222540534490260685644809999)
  ·
    refine ⟨333810801735391028467214999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222540534490260685644809999 333810801735391028467214999)
    ·
      refine ⟨500716202603086542700822499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333810801735391028467214999 500716202603086542700822499)
      ·
        refine ⟨751074303904629814051233749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500716202603086542700822499 751074303904629814051233749)
        ·
          refine ⟨17603303997764761266825791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 751074303904629814051233749 17603303997764761266825791)
          ·
            refine ⟨26404955996647141900238687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17603303997764761266825791 26404955996647141900238687)
            ·
              refine ⟨39607433994970712850358031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26404955996647141900238687 39607433994970712850358031)
              ·
                refine ⟨59411150992456069275537047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39607433994970712850358031 59411150992456069275537047)
                ·
                  refine ⟨89116726488684103913305571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59411150992456069275537047 89116726488684103913305571)
                  ·
                    refine ⟨133675089733026155869958357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89116726488684103913305571 133675089733026155869958357)
                    ·
                      refine ⟨3133009915617800528202149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 133675089733026155869958357 3133009915617800528202149)
                      ·
                        rfl

theorem cell23_6101515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 7].length) (baseStart_6101515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101515 prefixEnd_6101515 := by exact prefixLift 6101515
  have htrace : WordTrace (prefixWord ++ tailWord_6101515) baseStart_6101515 baseEnd_6101515 := by
    simpa [prefixWord, tailWord_6101515, baseEnd_6101515] using wordTrace_append hprefix tailTrace_6101515
  have hstable : (prefixWord ++ tailWord_6101515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101515).length < 2 ^ (prefixWord ++ tailWord_6101515).sum := by decide
  have hdescent : baseEnd_6101515 < baseStart_6101515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101555 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 6]
def baseStart_6101555 : Nat := 118140960795 + 6101555 * 2 ^ 59
def prefixEnd_6101555 : Nat := 4983230072969 + 3 ^ 40 * 6101555 * 2
def baseEnd_6101555 : Nat := 3133030454843980371701965

theorem tailTrace_6101555 : CollatzResearch.WordTrace tailWord_6101555 prefixEnd_6101555 3133030454843980371701965 := by
  unfold tailWord_6101555
  simp only [CollatzResearch.WordTrace]
  refine ⟨222541993410115772476266119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148361328940077181650844079 222541993410115772476266119)
  ·
    refine ⟨333812990115173658714399179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222541993410115772476266119 333812990115173658714399179)
    ·
      refine ⟨500719485172760488071598769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333812990115173658714399179 500719485172760488071598769)
      ·
        refine ⟨375539613879570366053699077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 500719485172760488071598769 375539613879570366053699077)
        ·
          refine ⟨70413677602419443635068577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 375539613879570366053699077 70413677602419443635068577)
          ·
            refine ⟨52810258201814582726301433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70413677602419443635068577 52810258201814582726301433)
            ·
              refine ⟨39607693651360937044726075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52810258201814582726301433 39607693651360937044726075)
              ·
                refine ⟨59411540477041405567089113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39607693651360937044726075 59411540477041405567089113)
                ·
                  refine ⟨44558655357781054175316835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59411540477041405567089113 44558655357781054175316835)
                  ·
                    refine ⟨66837983036671581262975253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44558655357781054175316835 66837983036671581262975253)
                    ·
                      refine ⟨3133030454843980371701965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66837983036671581262975253 3133030454843980371701965)
                      ·
                        rfl

theorem cell23_6101555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 6].length) (baseStart_6101555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101555 prefixEnd_6101555 := by exact prefixLift 6101555
  have htrace : WordTrace (prefixWord ++ tailWord_6101555) baseStart_6101555 baseEnd_6101555 := by
    simpa [prefixWord, tailWord_6101555, baseEnd_6101555] using wordTrace_append hprefix tailTrace_6101555
  have hstable : (prefixWord ++ tailWord_6101555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101555).length < 2 ^ (prefixWord ++ tailWord_6101555).sum := by decide
  have hdescent : baseEnd_6101555 < baseStart_6101555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101582 : List Nat := [4, 1, 1, 1, 1, 2, 4, 3, 6]
def baseStart_6101582 : Nat := 118140960795 + 6101582 * 2 ^ 59
def prefixEnd_6101582 : Nat := 4983230072969 + 3 ^ 40 * 6101582 * 2
def baseEnd_6101582 : Nat := 348116035424627974007149

theorem tailTrace_6101582 : CollatzResearch.WordTrace tailWord_6101582 prefixEnd_6101582 348116035424627974007149 := by
  unfold tailWord_6101582
  simp only [CollatzResearch.WordTrace]
  refine ⟨27817872272627244510937375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148361985454011970724999333 27817872272627244510937375)
  ·
    refine ⟨41726808408940866766406063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27817872272627244510937375 41726808408940866766406063)
    ·
      refine ⟨62590212613411300149609095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41726808408940866766406063 62590212613411300149609095)
      ·
        refine ⟨93885318920116950224413643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62590212613411300149609095 93885318920116950224413643)
        ·
          refine ⟨140827978380175425336620465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93885318920116950224413643 140827978380175425336620465)
          ·
            refine ⟨105620983785131569002465349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140827978380175425336620465 105620983785131569002465349)
            ·
              refine ⟨19803934459712169187962253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105620983785131569002465349 19803934459712169187962253)
              ·
                refine ⟨7426475422392063445485845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19803934459712169187962253 7426475422392063445485845)
                ·
                  refine ⟨348116035424627974007149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7426475422392063445485845 348116035424627974007149)
                  ·
                    rfl

theorem cell23_6101582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_6101582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101582 prefixEnd_6101582 := by exact prefixLift 6101582
  have htrace : WordTrace (prefixWord ++ tailWord_6101582) baseStart_6101582 baseEnd_6101582 := by
    simpa [prefixWord, tailWord_6101582, baseEnd_6101582] using wordTrace_append hprefix tailTrace_6101582
  have hstable : (prefixWord ++ tailWord_6101582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101582).length < 2 ^ (prefixWord ++ tailWord_6101582).sum := by decide
  have hdescent : baseEnd_6101582 < baseStart_6101582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101616 : List Nat := [2, 1, 1, 1, 8, 1, 1, 2, 6]
def baseStart_6101616 : Nat := 118140960795 + 6101616 * 2 ^ 59
def prefixEnd_6101616 : Nat := 4983230072969 + 3 ^ 40 * 6101616 * 2
def baseEnd_6101616 : Nat := 348117975240433848115465

theorem tailTrace_6101616 : CollatzResearch.WordTrace tailWord_6101616 prefixEnd_6101616 348117975240433848115465 := by
  unfold tailWord_6101616
  simp only [CollatzResearch.WordTrace]
  refine ⟨111272109131447389947118351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148362812175263186596157801 111272109131447389947118351)
  ·
    refine ⟨166908163697171084920677527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111272109131447389947118351 166908163697171084920677527)
    ·
      refine ⟨250362245545756627381016291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166908163697171084920677527 250362245545756627381016291)
      ·
        refine ⟨375543368318634941071524437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250362245545756627381016291 375543368318634941071524437)
        ·
          refine ⟨4400898847484003215681927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 375543368318634941071524437 4400898847484003215681927)
          ·
            refine ⟨6601348271226004823522891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4400898847484003215681927 6601348271226004823522891)
            ·
              refine ⟨9902022406839007235284337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6601348271226004823522891 9902022406839007235284337)
              ·
                refine ⟨7426516805129255426463253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9902022406839007235284337 7426516805129255426463253)
                ·
                  refine ⟨348117975240433848115465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7426516805129255426463253 348117975240433848115465)
                  ·
                    rfl

theorem cell23_6101616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 6].length) (baseStart_6101616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101616 prefixEnd_6101616 := by exact prefixLift 6101616
  have htrace : WordTrace (prefixWord ++ tailWord_6101616) baseStart_6101616 baseEnd_6101616 := by
    simpa [prefixWord, tailWord_6101616, baseEnd_6101616] using wordTrace_append hprefix tailTrace_6101616
  have hstable : (prefixWord ++ tailWord_6101616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101616).length < 2 ^ (prefixWord ++ tailWord_6101616).sum := by decide
  have hdescent : baseEnd_6101616 < baseStart_6101616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101660 : List Nat := [2, 2, 3, 2, 2, 3, 1, 3, 1, 1, 3]
def baseStart_6101660 : Nat := 118140960795 + 6101660 * 2 ^ 59
def prefixEnd_6101660 : Nat := 4983230072969 + 3 ^ 40 * 6101660 * 2
def baseEnd_6101660 : Nat := 3133084370312702460888983

theorem tailTrace_6101660 : CollatzResearch.WordTrace tailWord_6101660 prefixEnd_6101660 3133084370312702460888983 := by
  unfold tailWord_6101660
  simp only [CollatzResearch.WordTrace]
  refine ⟨111272911537367687704419217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148363882049823583605892289 111272911537367687704419217)
  ·
    refine ⟨83454683653025765778314413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111272911537367687704419217 83454683653025765778314413)
    ·
      refine ⟨31295506369884662166867905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83454683653025765778314413 31295506369884662166867905)
      ·
        refine ⟨23471629777413496625150929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31295506369884662166867905 23471629777413496625150929)
        ·
          refine ⟨17603722333060122468863197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23471629777413496625150929 17603722333060122468863197)
          ·
            refine ⟨6601395874897545925823699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17603722333060122468863197 6601395874897545925823699)
            ·
              refine ⟨9902093812346318888735549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6601395874897545925823699 9902093812346318888735549)
              ·
                refine ⟨3713285179629869583275831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9902093812346318888735549 3713285179629869583275831)
                ·
                  refine ⟨5569927769444804374913747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3713285179629869583275831 5569927769444804374913747)
                  ·
                    refine ⟨8354891654167206562370621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5569927769444804374913747 8354891654167206562370621)
                    ·
                      refine ⟨3133084370312702460888983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8354891654167206562370621 3133084370312702460888983)
                      ·
                        rfl

theorem cell23_6101660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_6101660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101660 prefixEnd_6101660 := by exact prefixLift 6101660
  have htrace : WordTrace (prefixWord ++ tailWord_6101660) baseStart_6101660 baseEnd_6101660 := by
    simpa [prefixWord, tailWord_6101660, baseEnd_6101660] using wordTrace_append hprefix tailTrace_6101660
  have hstable : (prefixWord ++ tailWord_6101660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101660).length < 2 ^ (prefixWord ++ tailWord_6101660).sum := by decide
  have hdescent : baseEnd_6101660 < baseStart_6101660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101683 : List Nat := [1, 1, 1, 2, 3, 6, 1, 1, 3, 2, 2]
def baseStart_6101683 : Nat := 118140960795 + 6101683 * 2 ^ 59
def prefixEnd_6101683 : Nat := 4983230072969 + 3 ^ 40 * 6101683 * 2
def baseEnd_6101683 : Nat := 3133096180367755870901377

theorem tailTrace_6101683 : CollatzResearch.WordTrace tailWord_6101683 prefixEnd_6101683 3133096180367755870901377 := by
  unfold tailWord_6101683
  simp only [CollatzResearch.WordTrace]
  refine ⟨222546661953652050336925703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148364441302434700224617135 222546661953652050336925703)
  ·
    refine ⟨333819992930478075505388555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222546661953652050336925703 333819992930478075505388555)
    ·
      refine ⟨500729989395717113258082833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333819992930478075505388555 500729989395717113258082833)
      ·
        refine ⟨375547492046787834943562125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 500729989395717113258082833 375547492046787834943562125)
        ·
          refine ⟨140830309517545438103835797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 375547492046787834943562125 140830309517545438103835797)
          ·
            refine ⟨6601420758634942411117303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 140830309517545438103835797 6601420758634942411117303)
            ·
              refine ⟨9902131137952413616675955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6601420758634942411117303 9902131137952413616675955)
              ·
                refine ⟨14853196706928620425013933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9902131137952413616675955 14853196706928620425013933)
                ·
                  refine ⟨5569948765098232659380225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14853196706928620425013933 5569948765098232659380225)
                  ·
                    refine ⟨4177461573823674494535169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5569948765098232659380225 4177461573823674494535169)
                    ·
                      refine ⟨3133096180367755870901377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4177461573823674494535169 3133096180367755870901377)
                      ·
                        rfl

theorem cell23_6101683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 2, 2].length) (baseStart_6101683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101683 prefixEnd_6101683 := by exact prefixLift 6101683
  have htrace : WordTrace (prefixWord ++ tailWord_6101683) baseStart_6101683 baseEnd_6101683 := by
    simpa [prefixWord, tailWord_6101683, baseEnd_6101683] using wordTrace_append hprefix tailTrace_6101683
  have hstable : (prefixWord ++ tailWord_6101683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101683).length < 2 ^ (prefixWord ++ tailWord_6101683).sum := by decide
  have hdescent : baseEnd_6101683 < baseStart_6101683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101692 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 2, 2, 6]
def baseStart_6101692 : Nat := 118140960795 + 6101692 * 2 ^ 59
def prefixEnd_6101692 : Nat := 4983230072969 + 3 ^ 40 * 6101692 * 2
def baseEnd_6101692 : Nat := 3133100801693646335688835

theorem tailTrace_6101692 : CollatzResearch.WordTrace tailWord_6101692 prefixEnd_6101692 3133100801693646335688835 := by
  unfold tailWord_6101692
  simp only [CollatzResearch.WordTrace]
  refine ⟨111273495105309722437001665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148364660140412963249335553 111273495105309722437001665)
  ·
    refine ⟨83455121328982291827751249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111273495105309722437001665 83455121328982291827751249)
    ·
      refine ⟨62591340996736718870813437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83455121328982291827751249 62591340996736718870813437)
      ·
        refine ⟨23471752873776269576555039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62591340996736718870813437 23471752873776269576555039)
        ·
          refine ⟨35207629310664404364832559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23471752873776269576555039 35207629310664404364832559)
          ·
            refine ⟨52811443965996606547248839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35207629310664404364832559 52811443965996606547248839)
            ·
              refine ⟨79217165948994909820873259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52811443965996606547248839 79217165948994909820873259)
              ·
                refine ⟨118825748923492364731309889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79217165948994909820873259 118825748923492364731309889)
                ·
                  refine ⟨89119311692619273548482417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118825748923492364731309889 89119311692619273548482417)
                  ·
                    refine ⟨66839483769464455161361813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89119311692619273548482417 66839483769464455161361813)
                    ·
                      refine ⟨3133100801693646335688835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66839483769464455161361813 3133100801693646335688835)
                      ·
                        rfl

theorem cell23_6101692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_6101692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101692 prefixEnd_6101692 := by exact prefixLift 6101692
  have htrace : WordTrace (prefixWord ++ tailWord_6101692) baseStart_6101692 baseEnd_6101692 := by
    simpa [prefixWord, tailWord_6101692, baseEnd_6101692] using wordTrace_append hprefix tailTrace_6101692
  have hstable : (prefixWord ++ tailWord_6101692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101692).length < 2 ^ (prefixWord ++ tailWord_6101692).sum := by decide
  have hdescent : baseEnd_6101692 < baseStart_6101692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101693 : List Nat := [1, 4, 1, 2, 1, 5, 2, 1, 2, 4]
def baseStart_6101693 : Nat := 118140960795 + 6101693 * 2 ^ 59
def prefixEnd_6101693 : Nat := 4983230072969 + 3 ^ 40 * 6101693 * 2
def baseEnd_6101693 : Nat := 1044367105058100277258777

theorem tailTrace_6101693 : CollatzResearch.WordTrace tailWord_6101693 prefixEnd_6101693 1044367105058100277258777 := by
  unfold tailWord_6101693
  simp only [CollatzResearch.WordTrace]
  refine ⟨222547026683615822044789733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148364684455743881363193155 222547026683615822044789733)
  ·
    refine ⟨41727567503177966633398075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222547026683615822044789733 41727567503177966633398075)
    ·
      refine ⟨62591351254766949950097113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41727567503177966633398075 62591351254766949950097113)
      ·
        refine ⟨46943513441075212462572835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62591351254766949950097113 46943513441075212462572835)
        ·
          refine ⟨70415270161612818693859253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46943513441075212462572835 70415270161612818693859253)
          ·
            refine ⟨6601431577651201752549305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70415270161612818693859253 6601431577651201752549305)
            ·
              refine ⟨4951073683238401314411979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6601431577651201752549305 4951073683238401314411979)
              ·
                refine ⟨7426610524857601971617969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4951073683238401314411979 7426610524857601971617969)
                ·
                  refine ⟨5569957893643201478713477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7426610524857601971617969 5569957893643201478713477)
                  ·
                    refine ⟨1044367105058100277258777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5569957893643201478713477 1044367105058100277258777)
                    ·
                      rfl

theorem cell23_6101693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_6101693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101693 prefixEnd_6101693 := by exact prefixLift 6101693
  have htrace : WordTrace (prefixWord ++ tailWord_6101693) baseStart_6101693 baseEnd_6101693 := by
    simpa [prefixWord, tailWord_6101693, baseEnd_6101693] using wordTrace_append hprefix tailTrace_6101693
  have hstable : (prefixWord ++ tailWord_6101693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101693).length < 2 ^ (prefixWord ++ tailWord_6101693).sum := by decide
  have hdescent : baseEnd_6101693 < baseStart_6101693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101733 : List Nat := [1, 3, 1, 4, 1, 3, 2, 2, 2, 1, 3]
def baseStart_6101733 : Nat := 118140960795 + 6101733 * 2 ^ 59
def prefixEnd_6101733 : Nat := 4983230072969 + 3 ^ 40 * 6101733 * 2
def baseEnd_6101733 : Nat := 3133121854400480675276147

theorem tailTrace_6101733 : CollatzResearch.WordTrace tailWord_6101733 prefixEnd_6101733 3133121854400480675276147 := by
  unfold tailWord_6101733
  simp only [CollatzResearch.WordTrace]
  refine ⟨222548485603470908876245853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148365657068980605917497235 222548485603470908876245853)
  ·
    refine ⟨83455682101301590828592195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222548485603470908876245853 83455682101301590828592195)
    ·
      refine ⟨125183523151952386242888293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83455682101301590828592195 125183523151952386242888293)
      ·
        refine ⟨23471910590991072420541555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125183523151952386242888293 23471910590991072420541555)
        ·
          refine ⟨35207865886486608630812333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23471910590991072420541555 35207865886486608630812333)
          ·
            refine ⟨13202949707432478236554625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35207865886486608630812333 13202949707432478236554625)
            ·
              refine ⟨9902212280574358677415969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13202949707432478236554625 9902212280574358677415969)
              ·
                refine ⟨7426659210430769008061977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9902212280574358677415969 7426659210430769008061977)
                ·
                  refine ⟨5569994407823076756046483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7426659210430769008061977 5569994407823076756046483)
                  ·
                    refine ⟨8354991611734615134069725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5569994407823076756046483 8354991611734615134069725)
                    ·
                      refine ⟨3133121854400480675276147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8354991611734615134069725 3133121854400480675276147)
                      ·
                        rfl

theorem cell23_6101733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_6101733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101733 prefixEnd_6101733 := by exact prefixLift 6101733
  have htrace : WordTrace (prefixWord ++ tailWord_6101733) baseStart_6101733 baseEnd_6101733 := by
    simpa [prefixWord, tailWord_6101733, baseEnd_6101733] using wordTrace_append hprefix tailTrace_6101733
  have hstable : (prefixWord ++ tailWord_6101733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101733).length < 2 ^ (prefixWord ++ tailWord_6101733).sum := by decide
  have hdescent : baseEnd_6101733 < baseStart_6101733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101739 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 5, 4, 2]
def baseStart_6101739 : Nat := 118140960795 + 6101739 * 2 ^ 59
def prefixEnd_6101739 : Nat := 4983230072969 + 3 ^ 40 * 6101739 * 2
def baseEnd_6101739 : Nat := 3133124935284407651801119

theorem tailTrace_6101739 : CollatzResearch.WordTrace tailWord_6101739 prefixEnd_6101739 3133124935284407651801119 := by
  unfold tailWord_6101739
  simp only [CollatzResearch.WordTrace]
  refine ⟨222548704441449171900964271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148365802960966114600642847 222548704441449171900964271)
  ·
    refine ⟨333823056662173757851446407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222548704441449171900964271 333823056662173757851446407)
    ·
      refine ⟨500734584993260636777169611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333823056662173757851446407 500734584993260636777169611)
      ·
        refine ⟨751101877489890955165754417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500734584993260636777169611 751101877489890955165754417)
        ·
          refine ⟨563326408117418216374315813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 751101877489890955165754417 563326408117418216374315813)
          ·
            refine ⟨105623701522015915570184215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 563326408117418216374315813 105623701522015915570184215)
            ·
              refine ⟨158435552283023873355276323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105623701522015915570184215 158435552283023873355276323)
              ·
                refine ⟨237653328424535810032914485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158435552283023873355276323 237653328424535810032914485)
                ·
                  refine ⟨22279999539800232190585733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 237653328424535810032914485 22279999539800232190585733)
                  ·
                    refine ⟨4177499913712543535734825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22279999539800232190585733 4177499913712543535734825)
                    ·
                      refine ⟨3133124935284407651801119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4177499913712543535734825 3133124935284407651801119)
                      ·
                        rfl

theorem cell23_6101739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 4, 2].length) (baseStart_6101739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101739 prefixEnd_6101739 := by exact prefixLift 6101739
  have htrace : WordTrace (prefixWord ++ tailWord_6101739) baseStart_6101739 baseEnd_6101739 := by
    simpa [prefixWord, tailWord_6101739, baseEnd_6101739] using wordTrace_append hprefix tailTrace_6101739
  have hstable : (prefixWord ++ tailWord_6101739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101739).length < 2 ^ (prefixWord ++ tailWord_6101739).sum := by decide
  have hdescent : baseEnd_6101739 < baseStart_6101739 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101756 : List Nat := [2, 2, 2, 1, 3, 2, 1, 3, 1, 4, 2]
def baseStart_6101756 : Nat := 118140960795 + 6101756 * 2 ^ 59
def prefixEnd_6101756 : Nat := 4983230072969 + 3 ^ 40 * 6101756 * 2
def baseEnd_6101756 : Nat := 3133133664455534085288541

theorem tailTrace_6101756 : CollatzResearch.WordTrace tailWord_6101756 prefixEnd_6101756 3133133664455534085288541 := by
  unfold tailWord_6101756
  simp only [CollatzResearch.WordTrace]
  refine ⟨111274662241193791902166561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148366216321591722536222081 111274662241193791902166561)
  ·
    refine ⟨83455996680895343926624921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111274662241193791902166561 83455996680895343926624921)
    ·
      refine ⟨62591997510671507944968691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83455996680895343926624921 62591997510671507944968691)
      ·
        refine ⟨93887996266007261917453037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62591997510671507944968691 93887996266007261917453037)
        ·
          refine ⟨35207998599752723219044889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93887996266007261917453037 35207998599752723219044889)
          ·
            refine ⟨26405998949814542414283667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35207998599752723219044889 26405998949814542414283667)
            ·
              refine ⟨39608998424721813621425501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26405998949814542414283667 39608998424721813621425501)
              ·
                refine ⟨14853374409270680108034563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39608998424721813621425501 14853374409270680108034563)
                ·
                  refine ⟨22280061613906020162051845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14853374409270680108034563 22280061613906020162051845)
                  ·
                    refine ⟨4177511552607378780384721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22280061613906020162051845 4177511552607378780384721)
                    ·
                      refine ⟨3133133664455534085288541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4177511552607378780384721 3133133664455534085288541)
                      ·
                        rfl

theorem cell23_6101756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 1, 4, 2].length) (baseStart_6101756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101756 prefixEnd_6101756 := by exact prefixLift 6101756
  have htrace : WordTrace (prefixWord ++ tailWord_6101756) baseStart_6101756 baseEnd_6101756 := by
    simpa [prefixWord, tailWord_6101756, baseEnd_6101756] using wordTrace_append hprefix tailTrace_6101756
  have hstable : (prefixWord ++ tailWord_6101756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101756).length < 2 ^ (prefixWord ++ tailWord_6101756).sum := by decide
  have hdescent : baseEnd_6101756 < baseStart_6101756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101772 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 1, 2, 7]
def baseStart_6101772 : Nat := 118140960795 + 6101772 * 2 ^ 59
def prefixEnd_6101772 : Nat := 4983230072969 + 3 ^ 40 * 6101772 * 2
def baseEnd_6101772 : Nat := 3133141880146006022688467

theorem tailTrace_6101772 : CollatzResearch.WordTrace tailWord_6101772 prefixEnd_6101772 3133141880146006022688467 := by
  unfold tailWord_6101772
  simp only [CollatzResearch.WordTrace]
  refine ⟨111274954025164809268457785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148366605366886412357943713 111274954025164809268457785)
  ·
    refine ⟨83456215518873606951343339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111274954025164809268457785 83456215518873606951343339)
    ·
      refine ⟨125184323278310410427015009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83456215518873606951343339 125184323278310410427015009)
      ·
        refine ⟨93888242458732807820261257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125184323278310410427015009 93888242458732807820261257)
        ·
          refine ⟨70416181844049605865195943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93888242458732807820261257 70416181844049605865195943)
          ·
            refine ⟨105624272766074408797793915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70416181844049605865195943 105624272766074408797793915)
            ·
              refine ⟨158436409149111613196690873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105624272766074408797793915 158436409149111613196690873)
              ·
                refine ⟨118827306861833709897518155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158436409149111613196690873 118827306861833709897518155)
                ·
                  refine ⟨178240960292750564846277233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118827306861833709897518155 178240960292750564846277233)
                  ·
                    refine ⟨133680720219562923634707925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 178240960292750564846277233 133680720219562923634707925)
                    ·
                      refine ⟨3133141880146006022688467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 133680720219562923634707925 3133141880146006022688467)
                      ·
                        rfl

theorem cell23_6101772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_6101772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101772 prefixEnd_6101772 := by exact prefixLift 6101772
  have htrace : WordTrace (prefixWord ++ tailWord_6101772) baseStart_6101772 baseEnd_6101772 := by
    simpa [prefixWord, tailWord_6101772, baseEnd_6101772] using wordTrace_append hprefix tailTrace_6101772
  have hstable : (prefixWord ++ tailWord_6101772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101772).length < 2 ^ (prefixWord ++ tailWord_6101772).sum := by decide
  have hdescent : baseEnd_6101772 < baseStart_6101772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101796 : List Nat := [2, 3, 1, 3, 3, 1, 2, 1, 7]
def baseStart_6101796 : Nat := 118140960795 + 6101796 * 2 ^ 59
def prefixEnd_6101796 : Nat := 4983230072969 + 3 ^ 40 * 6101796 * 2
def baseEnd_6101796 : Nat := 348128244853523769865373

theorem tailTrace_6101796 : CollatzResearch.WordTrace tailWord_6101796 prefixEnd_6101796 348128244853523769865373 := by
  unfold tailWord_6101796
  simp only [CollatzResearch.WordTrace]
  refine ⟨111275391701121335317894621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148367188934828447090526161 111275391701121335317894621)
  ·
    refine ⟨41728271887920500744210483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111275391701121335317894621 41728271887920500744210483)
    ·
      refine ⟨62592407831880751116315725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41728271887920500744210483 62592407831880751116315725)
      ·
        refine ⟨23472152936955281668618397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62592407831880751116315725 23472152936955281668618397)
        ·
          refine ⟨8802057351358230625731899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23472152936955281668618397 8802057351358230625731899)
          ·
            refine ⟨13203086027037345938597849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8802057351358230625731899 13203086027037345938597849)
            ·
              refine ⟨9902314520278009453948387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13203086027037345938597849 9902314520278009453948387)
              ·
                refine ⟨14853471780417014180922581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9902314520278009453948387 14853471780417014180922581)
                ·
                  refine ⟨348128244853523769865373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14853471780417014180922581 348128244853523769865373)
                  ·
                    rfl

theorem cell23_6101796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_6101796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101796 prefixEnd_6101796 := by exact prefixLift 6101796
  have htrace : WordTrace (prefixWord ++ tailWord_6101796) baseStart_6101796 baseEnd_6101796 := by
    simpa [prefixWord, tailWord_6101796, baseEnd_6101796] using wordTrace_append hprefix tailTrace_6101796
  have hstable : (prefixWord ++ tailWord_6101796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101796).length < 2 ^ (prefixWord ++ tailWord_6101796).sum := by decide
  have hdescent : baseEnd_6101796 < baseStart_6101796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101879 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 3]
def baseStart_6101879 : Nat := 118140960795 + 6101879 * 2 ^ 59
def prefixEnd_6101879 : Nat := 4983230072969 + 3 ^ 40 * 6101879 * 2
def baseEnd_6101879 : Nat := 3133196822576037104050475

theorem tailTrace_6101879 : CollatzResearch.WordTrace tailWord_6101879 prefixEnd_6101879 3133196822576037104050475 := by
  unfold tailWord_6101879
  simp only [CollatzResearch.WordTrace]
  refine ⟨222553810660941975811060691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148369207107294650540707127 222553810660941975811060691)
  ·
    refine ⟨333830715991412963716591037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222553810660941975811060691 333830715991412963716591037)
    ·
      refine ⟨125186518496779861393721639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333830715991412963716591037 125186518496779861393721639)
      ·
        refine ⟨187779777745169792090582459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125186518496779861393721639 187779777745169792090582459)
        ·
          refine ⟨281669666617754688135873689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187779777745169792090582459 281669666617754688135873689)
          ·
            refine ⟨211252249963316016101905267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281669666617754688135873689 211252249963316016101905267)
            ·
              refine ⟨316878374944974024152857901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211252249963316016101905267 316878374944974024152857901)
              ·
                refine ⟨118829390604365259057321713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 316878374944974024152857901 118829390604365259057321713)
                ·
                  refine ⟨89122042953273944292991285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118829390604365259057321713 89122042953273944292991285)
                  ·
                    refine ⟨8355191526869432277467933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89122042953273944292991285 8355191526869432277467933)
                    ·
                      refine ⟨3133196822576037104050475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8355191526869432277467933 3133196822576037104050475)
                      ·
                        rfl

theorem cell23_6101879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 3].length) (baseStart_6101879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101879 prefixEnd_6101879 := by exact prefixLift 6101879
  have htrace : WordTrace (prefixWord ++ tailWord_6101879) baseStart_6101879 baseEnd_6101879 := by
    simpa [prefixWord, tailWord_6101879, baseEnd_6101879] using wordTrace_append hprefix tailTrace_6101879
  have hstable : (prefixWord ++ tailWord_6101879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101879).length < 2 ^ (prefixWord ++ tailWord_6101879).sum := by decide
  have hdescent : baseEnd_6101879 < baseStart_6101879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101939 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 5]
def baseStart_6101939 : Nat := 118140960795 + 6101939 * 2 ^ 59
def prefixEnd_6101939 : Nat := 4983230072969 + 3 ^ 40 * 6101939 * 2
def baseEnd_6101939 : Nat := 3133227631415306869300199

theorem tailTrace_6101939 : CollatzResearch.WordTrace tailWord_6101939 prefixEnd_6101939 3133227631415306869300199 := by
  unfold tailWord_6101939
  simp only [CollatzResearch.WordTrace]
  refine ⟨222555999040724606058244871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148370666027149737372163247 222555999040724606058244871)
  ·
    refine ⟨333833998561086909087367307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222555999040724606058244871 333833998561086909087367307)
    ·
      refine ⟨500750997841630363631050961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333833998561086909087367307 500750997841630363631050961)
      ·
        refine ⟨375563248381222772723288221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 500750997841630363631050961 375563248381222772723288221)
        ·
          refine ⟨140836218142958539771233083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 375563248381222772723288221 140836218142958539771233083)
          ·
            refine ⟨211254327214437809656849625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140836218142958539771233083 211254327214437809656849625)
            ·
              refine ⟨158440745410828357242637219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211254327214437809656849625 158440745410828357242637219)
              ·
                refine ⟨237661118116242535863955829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158440745410828357242637219 237661118116242535863955829)
                ·
                  refine ⟨22280729823397737737245859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 237661118116242535863955829 22280729823397737737245859)
                  ·
                    refine ⟨33421094735096606605868789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22280729823397737737245859 33421094735096606605868789)
                    ·
                      refine ⟨3133227631415306869300199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33421094735096606605868789 3133227631415306869300199)
                      ·
                        rfl

theorem cell23_6101939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 5].length) (baseStart_6101939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101939 prefixEnd_6101939 := by exact prefixLift 6101939
  have htrace : WordTrace (prefixWord ++ tailWord_6101939) baseStart_6101939 baseEnd_6101939 := by
    simpa [prefixWord, tailWord_6101939, baseEnd_6101939] using wordTrace_append hprefix tailTrace_6101939
  have hstable : (prefixWord ++ tailWord_6101939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101939).length < 2 ^ (prefixWord ++ tailWord_6101939).sum := by decide
  have hdescent : baseEnd_6101939 < baseStart_6101939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101946 : List Nat := [3, 1, 1, 1, 2, 1, 4, 2, 4, 4]
def baseStart_6101946 : Nat := 118140960795 + 6101946 * 2 ^ 59
def prefixEnd_6101946 : Nat := 4983230072969 + 3 ^ 40 * 6101946 * 2
def baseEnd_6101946 : Nat := 1044410408593296113970889

theorem tailTrace_6101946 : CollatzResearch.WordTrace tailWord_6101946 prefixEnd_6101946 1044410408593296113970889 := by
  unfold tailWord_6101946
  simp only [CollatzResearch.WordTrace]
  refine ⟨55639063587924811563437423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148370836234466164169166461 55639063587924811563437423)
  ·
    refine ⟨83458595381887217345156135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55639063587924811563437423 83458595381887217345156135)
    ·
      refine ⟨125187893072830826017734203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83458595381887217345156135 125187893072830826017734203)
      ·
        refine ⟨187781839609246239026601305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125187893072830826017734203 187781839609246239026601305)
        ·
          refine ⟨140836379706934679269950979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187781839609246239026601305 140836379706934679269950979)
          ·
            refine ⟨211254569560402018904926469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140836379706934679269950979 211254569560402018904926469)
            ·
              refine ⟨39610231792575378544673713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 211254569560402018904926469 39610231792575378544673713)
              ·
                refine ⟨29707673844431533908505285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39610231792575378544673713 29707673844431533908505285)
                ·
                  refine ⟨5570188845830912607844741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29707673844431533908505285 5570188845830912607844741)
                  ·
                    refine ⟨1044410408593296113970889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5570188845830912607844741 1044410408593296113970889)
                    ·
                      rfl

theorem cell23_6101946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 4, 4].length) (baseStart_6101946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101946 prefixEnd_6101946 := by exact prefixLift 6101946
  have htrace : WordTrace (prefixWord ++ tailWord_6101946) baseStart_6101946 baseEnd_6101946 := by
    simpa [prefixWord, tailWord_6101946, baseEnd_6101946] using wordTrace_append hprefix tailTrace_6101946
  have hstable : (prefixWord ++ tailWord_6101946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101946).length < 2 ^ (prefixWord ++ tailWord_6101946).sum := by decide
  have hdescent : baseEnd_6101946 < baseStart_6101946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101963 : List Nat := [1, 1, 1, 1, 3, 5, 3, 2, 2, 4]
def baseStart_6101963 : Nat := 118140960795 + 6101963 * 2 ^ 59
def prefixEnd_6101963 : Nat := 4983230072969 + 3 ^ 40 * 6101963 * 2
def baseEnd_6101963 : Nat := 1044413318317004925133363

theorem tailTrace_6101963 : CollatzResearch.WordTrace tailWord_6101963 prefixEnd_6101963 1044413318317004925133363 := by
  unfold tailWord_6101963
  simp only [CollatzResearch.WordTrace]
  refine ⟨222556874392637658157118543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148371249595091772104745695 222556874392637658157118543)
  ·
    refine ⟨333835311588956487235677815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222556874392637658157118543 333835311588956487235677815)
    ·
      refine ⟨500752967383434730853516723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333835311588956487235677815 500752967383434730853516723)
      ·
        refine ⟨751129451075152096280275085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500752967383434730853516723 751129451075152096280275085)
        ·
          refine ⟨281673544153182036105103157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 751129451075152096280275085 281673544153182036105103157)
          ·
            refine ⟨26406894764360815884853421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 281673544153182036105103157 26406894764360815884853421)
            ·
              refine ⟨9902585536635305956820033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26406894764360815884853421 9902585536635305956820033)
              ·
                refine ⟨7426939152476479467615025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9902585536635305956820033 7426939152476479467615025)
                ·
                  refine ⟨5570204364357359600711269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7426939152476479467615025 5570204364357359600711269)
                  ·
                    refine ⟨1044413318317004925133363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5570204364357359600711269 1044413318317004925133363)
                    ·
                      rfl

theorem cell23_6101963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 4].length) (baseStart_6101963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101963 prefixEnd_6101963 := by exact prefixLift 6101963
  have htrace : WordTrace (prefixWord ++ tailWord_6101963) baseStart_6101963 baseEnd_6101963 := by
    simpa [prefixWord, tailWord_6101963, baseEnd_6101963] using wordTrace_append hprefix tailTrace_6101963
  have hstable : (prefixWord ++ tailWord_6101963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101963).length < 2 ^ (prefixWord ++ tailWord_6101963).sum := by decide
  have hdescent : baseEnd_6101963 < baseStart_6101963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6101973 : List Nat := [1, 3, 2, 3, 3, 1, 1, 2, 1, 1, 5]
def baseStart_6101973 : Nat := 118140960795 + 6101973 * 2 ^ 59
def prefixEnd_6101973 : Nat := 4983230072969 + 3 ^ 40 * 6101973 * 2
def baseEnd_6101973 : Nat := 3133245089757559736275043

theorem tailTrace_6101973 : CollatzResearch.WordTrace tailWord_6101973 prefixEnd_6101973 3133245089757559736275043 := by
  unfold tailWord_6101973
  simp only [CollatzResearch.WordTrace]
  refine ⟨222557239122601429864982573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148371492748400953243321715 222557239122601429864982573)
  ·
    refine ⟨83458964670975536199368465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222557239122601429864982573 83458964670975536199368465)
    ·
      refine ⟨62594223503231652149526349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83458964670975536199368465 62594223503231652149526349)
      ·
        refine ⟨23472833813711869556072381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62594223503231652149526349 23472833813711869556072381)
        ·
          refine ⟨8802312680141951083527143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23472833813711869556072381 8802312680141951083527143)
          ·
            refine ⟨13203469020212926625290715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8802312680141951083527143 13203469020212926625290715)
            ·
              refine ⟨19805203530319389937936073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13203469020212926625290715 19805203530319389937936073)
              ·
                refine ⟨14853902647739542453452055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19805203530319389937936073 14853902647739542453452055)
                ·
                  refine ⟨22280853971609313680178083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14853902647739542453452055 22280853971609313680178083)
                  ·
                    refine ⟨33421280957413970520267125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22280853971609313680178083 33421280957413970520267125)
                    ·
                      refine ⟨3133245089757559736275043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33421280957413970520267125 3133245089757559736275043)
                      ·
                        rfl

theorem cell23_6101973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_6101973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6101973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6101973 prefixEnd_6101973 := by exact prefixLift 6101973
  have htrace : WordTrace (prefixWord ++ tailWord_6101973) baseStart_6101973 baseEnd_6101973 := by
    simpa [prefixWord, tailWord_6101973, baseEnd_6101973] using wordTrace_append hprefix tailTrace_6101973
  have hstable : (prefixWord ++ tailWord_6101973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6101973).length < 2 ^ (prefixWord ++ tailWord_6101973).sum := by decide
  have hdescent : baseEnd_6101973 < baseStart_6101973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6101973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102013 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 5, 3, 2]
def baseStart_6102013 : Nat := 118140960795 + 6102013 * 2 ^ 59
def prefixEnd_6102013 : Nat := 4983230072969 + 3 ^ 40 * 6102013 * 2
def baseEnd_6102013 : Nat := 3133265628983739579774859

theorem tailTrace_6102013 : CollatzResearch.WordTrace tailWord_6102013 prefixEnd_6102013 3133265628983739579774859 := by
  unfold tailWord_6102013
  simp only [CollatzResearch.WordTrace]
  refine ⟨222558698042456516696438693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148372465361637677797625795 222558698042456516696438693)
  ·
    refine ⟨41729755882960596880582255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222558698042456516696438693 41729755882960596880582255)
    ·
      refine ⟨62594633824440895320873383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41729755882960596880582255 62594633824440895320873383)
      ·
        refine ⟨93891950736661342981310075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62594633824440895320873383 93891950736661342981310075)
        ·
          refine ⟨140837926104992014471965113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93891950736661342981310075 140837926104992014471965113)
          ·
            refine ⟨105628444578744010853973835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140837926104992014471965113 105628444578744010853973835)
            ·
              refine ⟨158442666868116016280960753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105628444578744010853973835 158442666868116016280960753)
              ·
                refine ⟨118832000151087012210720565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158442666868116016280960753 118832000151087012210720565)
                ·
                  refine ⟨11140500014164407394755053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118832000151087012210720565 11140500014164407394755053)
                  ·
                    refine ⟨4177687505311652773033145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11140500014164407394755053 4177687505311652773033145)
                    ·
                      refine ⟨3133265628983739579774859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4177687505311652773033145 3133265628983739579774859)
                      ·
                        rfl

theorem cell23_6102013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 3, 2].length) (baseStart_6102013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102013 prefixEnd_6102013 := by exact prefixLift 6102013
  have htrace : WordTrace (prefixWord ++ tailWord_6102013) baseStart_6102013 baseEnd_6102013 := by
    simpa [prefixWord, tailWord_6102013, baseEnd_6102013] using wordTrace_append hprefix tailTrace_6102013
  have hstable : (prefixWord ++ tailWord_6102013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102013).length < 2 ^ (prefixWord ++ tailWord_6102013).sum := by decide
  have hdescent : baseEnd_6102013 < baseStart_6102013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102037 : List Nat := [1, 3, 2, 1, 4, 1, 4, 1, 2, 1, 3]
def baseStart_6102037 : Nat := 118140960795 + 6102037 * 2 ^ 59
def prefixEnd_6102037 : Nat := 4983230072969 + 3 ^ 40 * 6102037 * 2
def baseEnd_6102037 : Nat := 3133277952519447485874749

theorem tailTrace_6102037 : CollatzResearch.WordTrace tailWord_6102037 prefixEnd_6102037 3133277952519447485874749 := by
  unfold tailWord_6102037
  simp only [CollatzResearch.WordTrace]
  refine ⟨222559573394369568795312365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148373048929579712530208243 222559573394369568795312365)
  ·
    refine ⟨83459840022888588298242137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222559573394369568795312365 83459840022888588298242137)
    ·
      refine ⟨62594880017166441223681603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83459840022888588298242137 62594880017166441223681603)
      ·
        refine ⟨93892320025749661835522405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62594880017166441223681603 93892320025749661835522405)
        ·
          refine ⟨17604810004828061594160451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93892320025749661835522405 17604810004828061594160451)
          ·
            refine ⟨26407215007242092391240677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17604810004828061594160451 26407215007242092391240677)
            ·
              refine ⟨4951352813857892323357627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26407215007242092391240677 4951352813857892323357627)
              ·
                refine ⟨7427029220786838485036441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4951352813857892323357627 7427029220786838485036441)
                ·
                  refine ⟨5570271915590128863777331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7427029220786838485036441 5570271915590128863777331)
                  ·
                    refine ⟨8355407873385193295665997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5570271915590128863777331 8355407873385193295665997)
                    ·
                      refine ⟨3133277952519447485874749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8355407873385193295665997 3133277952519447485874749)
                      ·
                        rfl

theorem cell23_6102037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 2, 1, 3].length) (baseStart_6102037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102037 prefixEnd_6102037 := by exact prefixLift 6102037
  have htrace : WordTrace (prefixWord ++ tailWord_6102037) baseStart_6102037 baseEnd_6102037 := by
    simpa [prefixWord, tailWord_6102037, baseEnd_6102037] using wordTrace_append hprefix tailTrace_6102037
  have hstable : (prefixWord ++ tailWord_6102037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102037).length < 2 ^ (prefixWord ++ tailWord_6102037).sum := by decide
  have hdescent : baseEnd_6102037 < baseStart_6102037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102047 : List Nat := [1, 1, 2, 4, 1, 5, 1, 2, 1, 3, 2]
def baseStart_6102047 : Nat := 118140960795 + 6102047 * 2 ^ 59
def prefixEnd_6102047 : Nat := 4983230072969 + 3 ^ 40 * 6102047 * 2
def baseEnd_6102047 : Nat := 3133283087325992446749703

theorem tailTrace_6102047 : CollatzResearch.WordTrace tailWord_6102047 prefixEnd_6102047 3133283087325992446749703 := by
  unfold tailWord_6102047
  simp only [CollatzResearch.WordTrace]
  refine ⟨222559938124333340503176395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148373292082888893668784263 222559938124333340503176395)
  ·
    refine ⟨333839907186500010754764593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222559938124333340503176395 333839907186500010754764593)
    ·
      refine ⟨250379930389875008066073445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333839907186500010754764593 250379930389875008066073445)
      ·
        refine ⟨46946236948101564012388771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 250379930389875008066073445 46946236948101564012388771)
        ·
          refine ⟨70419355422152346018583157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46946236948101564012388771 70419355422152346018583157)
          ·
            refine ⟨6601814570826782439242171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70419355422152346018583157 6601814570826782439242171)
            ·
              refine ⟨9902721856240173658863257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6601814570826782439242171 9902721856240173658863257)
              ·
                refine ⟨7427041392180130244147443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9902721856240173658863257 7427041392180130244147443)
                ·
                  refine ⟨11140562088270195366221165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7427041392180130244147443 11140562088270195366221165)
                  ·
                    refine ⟨4177710783101323262332937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11140562088270195366221165 4177710783101323262332937)
                    ·
                      refine ⟨3133283087325992446749703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4177710783101323262332937 3133283087325992446749703)
                      ·
                        rfl

theorem cell23_6102047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_6102047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102047 prefixEnd_6102047 := by exact prefixLift 6102047
  have htrace : WordTrace (prefixWord ++ tailWord_6102047) baseStart_6102047 baseEnd_6102047 := by
    simpa [prefixWord, tailWord_6102047, baseEnd_6102047] using wordTrace_append hprefix tailTrace_6102047
  have hstable : (prefixWord ++ tailWord_6102047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102047).length < 2 ^ (prefixWord ++ tailWord_6102047).sum := by decide
  have hdescent : baseEnd_6102047 < baseStart_6102047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102077 : List Nat := [1, 4, 1, 3, 1, 2, 1, 4, 2, 2, 2]
def baseStart_6102077 : Nat := 118140960795 + 6102077 * 2 ^ 59
def prefixEnd_6102077 : Nat := 4983230072969 + 3 ^ 40 * 6102077 * 2
def baseEnd_6102077 : Nat := 3133298491745627329374565

theorem tailTrace_6102077 : CollatzResearch.WordTrace tailWord_6102077 prefixEnd_6102077 3133298491745627329374565 := by
  unfold tailWord_6102077
  simp only [CollatzResearch.WordTrace]
  refine ⟨222561032314224655626768485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148374021542816437084512323 222561032314224655626768485)
  ·
    refine ⟨41730193558917122930019091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222561032314224655626768485 41730193558917122930019091)
    ·
      refine ⟨62595290338375684395028637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41730193558917122930019091 62595290338375684395028637)
      ·
        refine ⟨23473233876890881648135739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62595290338375684395028637 23473233876890881648135739)
        ·
          refine ⟨35209850815336322472203609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23473233876890881648135739 35209850815336322472203609)
          ·
            refine ⟨26407388111502241854152707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35209850815336322472203609 26407388111502241854152707)
            ·
              refine ⟨39611082167253362781229061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26407388111502241854152707 39611082167253362781229061)
              ·
                refine ⟨7427077906360005521480449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39611082167253362781229061 7427077906360005521480449)
                ·
                  refine ⟨5570308429770004141110337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7427077906360005521480449 5570308429770004141110337)
                  ·
                    refine ⟨4177731322327503105832753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5570308429770004141110337 4177731322327503105832753)
                    ·
                      refine ⟨3133298491745627329374565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4177731322327503105832753 3133298491745627329374565)
                      ·
                        rfl

theorem cell23_6102077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_6102077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102077 prefixEnd_6102077 := by exact prefixLift 6102077
  have htrace : WordTrace (prefixWord ++ tailWord_6102077) baseStart_6102077 baseEnd_6102077 := by
    simpa [prefixWord, tailWord_6102077, baseEnd_6102077] using wordTrace_append hprefix tailTrace_6102077
  have hstable : (prefixWord ++ tailWord_6102077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102077).length < 2 ^ (prefixWord ++ tailWord_6102077).sum := by decide
  have hdescent : baseEnd_6102077 < baseStart_6102077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102083 : List Nat := [1, 1, 1, 3, 1, 2, 5, 4, 5]
def baseStart_6102083 : Nat := 118140960795 + 6102083 * 2 ^ 59
def prefixEnd_6102083 : Nat := 4983230072969 + 3 ^ 40 * 6102083 * 2
def baseEnd_6102083 : Nat := 348144619181061589544393

theorem tailTrace_6102083 : CollatzResearch.WordTrace tailWord_6102083 prefixEnd_6102083 348144619181061589544393 := by
  unfold tailWord_6102083
  simp only [CollatzResearch.WordTrace]
  refine ⟨222561251152202918651486903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148374167434801945767657935 222561251152202918651486903)
  ·
    refine ⟨333841876728304377977230355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222561251152202918651486903 333841876728304377977230355)
    ·
      refine ⟨500762815092456566965845533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333841876728304377977230355 500762815092456566965845533)
      ·
        refine ⟨187786055659671212612192075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 500762815092456566965845533 187786055659671212612192075)
        ·
          refine ⟨281679083489506818918288113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187786055659671212612192075 281679083489506818918288113)
          ·
            refine ⟨211259312617130114188716085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281679083489506818918288113 211259312617130114188716085)
            ·
              refine ⟨19805560557855948205192133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 211259312617130114188716085 19805560557855948205192133)
              ·
                refine ⟨3713542604597990288473525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19805560557855948205192133 3713542604597990288473525)
                ·
                  refine ⟨348144619181061589544393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3713542604597990288473525 348144619181061589544393)
                  ·
                    rfl

theorem cell23_6102083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 5].length) (baseStart_6102083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102083 prefixEnd_6102083 := by exact prefixLift 6102083
  have htrace : WordTrace (prefixWord ++ tailWord_6102083) baseStart_6102083 baseEnd_6102083 := by
    simpa [prefixWord, tailWord_6102083, baseEnd_6102083] using wordTrace_append hprefix tailTrace_6102083
  have hstable : (prefixWord ++ tailWord_6102083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102083).length < 2 ^ (prefixWord ++ tailWord_6102083).sum := by decide
  have hdescent : baseEnd_6102083 < baseStart_6102083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102096 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 4, 5]
def baseStart_6102096 : Nat := 118140960795 + 6102096 * 2 ^ 59
def prefixEnd_6102096 : Nat := 4983230072969 + 3 ^ 40 * 6102096 * 2
def baseEnd_6102096 : Nat := 1044436082626020918345659

theorem tailTrace_6102096 : CollatzResearch.WordTrace tailWord_6102096 prefixEnd_6102096 1044436082626020918345659 := by
  unfold tailWord_6102096
  simp only [CollatzResearch.WordTrace]
  refine ⟨111280862650577910935855071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148374483534103881247806761 111280862650577910935855071)
  ·
    refine ⟨166921293975866866403782607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111280862650577910935855071 166921293975866866403782607)
    ·
      refine ⟨250381940963800299605673911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166921293975866866403782607 250381940963800299605673911)
      ·
        refine ⟨375572911445700449408510867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250381940963800299605673911 375572911445700449408510867)
        ·
          refine ⟨563359367168550674112766301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375572911445700449408510867 563359367168550674112766301)
          ·
            refine ⟨211259762688206502792287363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 563359367168550674112766301 211259762688206502792287363)
            ·
              refine ⟨316889644032309754188431045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211259762688206502792287363 316889644032309754188431045)
              ·
                refine ⟨59416808256058078910330821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 316889644032309754188431045 59416808256058078910330821)
                ·
                  refine ⟨11140651548010889795687029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59416808256058078910330821 11140651548010889795687029)
                  ·
                    refine ⟨1044436082626020918345659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11140651548010889795687029 1044436082626020918345659)
                    ·
                      rfl

theorem cell23_6102096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 4, 5].length) (baseStart_6102096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102096 prefixEnd_6102096 := by exact prefixLift 6102096
  have htrace : WordTrace (prefixWord ++ tailWord_6102096) baseStart_6102096 baseEnd_6102096 := by
    simpa [prefixWord, tailWord_6102096, baseEnd_6102096] using wordTrace_append hprefix tailTrace_6102096
  have hstable : (prefixWord ++ tailWord_6102096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102096).length < 2 ^ (prefixWord ++ tailWord_6102096).sum := by decide
  have hdescent : baseEnd_6102096 < baseStart_6102096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102103 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 4, 5, 2]
def baseStart_6102103 : Nat := 118140960795 + 6102103 * 2 ^ 59
def prefixEnd_6102103 : Nat := 4983230072969 + 3 ^ 40 * 6102103 * 2
def baseEnd_6102103 : Nat := 3133311842242644227649445

theorem tailTrace_6102103 : CollatzResearch.WordTrace tailWord_6102103 prefixEnd_6102103 3133311842242644227649445 := by
  unfold tailWord_6102103
  simp only [CollatzResearch.WordTrace]
  refine ⟨222561980612130462067214963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148374653741420308044809975 222561980612130462067214963)
  ·
    refine ⟨333842970918195693100822445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222561980612130462067214963 333842970918195693100822445)
    ·
      refine ⟨125191114094323384912808417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333842970918195693100822445 125191114094323384912808417)
      ·
        refine ⟨93893335570742538684606313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125191114094323384912808417 93893335570742538684606313)
        ·
          refine ⟨70420001678056904013454735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93893335570742538684606313 70420001678056904013454735)
          ·
            refine ⟨105630002517085356020182103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70420001678056904013454735 105630002517085356020182103)
            ·
              refine ⟨158445003775628034030273155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105630002517085356020182103 158445003775628034030273155)
              ·
                refine ⟨237667505663442051045409733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158445003775628034030273155 237667505663442051045409733)
                ·
                  refine ⟨44562657311895384571014325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 237667505663442051045409733 44562657311895384571014325)
                  ·
                    refine ⟨4177749122990192303532593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44562657311895384571014325 4177749122990192303532593)
                    ·
                      refine ⟨3133311842242644227649445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4177749122990192303532593 3133311842242644227649445)
                      ·
                        rfl

theorem cell23_6102103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 5, 2].length) (baseStart_6102103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102103 prefixEnd_6102103 := by exact prefixLift 6102103
  have htrace : WordTrace (prefixWord ++ tailWord_6102103) baseStart_6102103 baseEnd_6102103 := by
    simpa [prefixWord, tailWord_6102103, baseEnd_6102103] using wordTrace_append hprefix tailTrace_6102103
  have hstable : (prefixWord ++ tailWord_6102103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102103).length < 2 ^ (prefixWord ++ tailWord_6102103).sum := by decide
  have hdescent : baseEnd_6102103 < baseStart_6102103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102106 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5]
def baseStart_6102106 : Nat := 118140960795 + 6102106 * 2 ^ 59
def prefixEnd_6102106 : Nat := 4983230072969 + 3 ^ 40 * 6102106 * 2
def baseEnd_6102106 : Nat := 3133313382684607715911931

theorem tailTrace_6102106 : CollatzResearch.WordTrace tailWord_6102106 prefixEnd_6102106 3133313382684607715911931 := by
  unfold tailWord_6102106
  simp only [CollatzResearch.WordTrace]
  refine ⟨55640522507779898394893543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148374726687413062386382781 55640522507779898394893543)
  ·
    refine ⟨83460783761669847592340315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55640522507779898394893543 83460783761669847592340315)
    ·
      refine ⟨125191175642504771388510473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83460783761669847592340315 125191175642504771388510473)
      ·
        refine ⟨93893381731878578541382855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125191175642504771388510473 93893381731878578541382855)
        ·
          refine ⟨140840072597817867812074283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93893381731878578541382855 140840072597817867812074283)
          ·
            refine ⟨211260108896726801718111425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140840072597817867812074283 211260108896726801718111425)
            ·
              refine ⟨158445081672545101288583569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211260108896726801718111425 158445081672545101288583569)
              ·
                refine ⟨118833811254408825966437677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158445081672545101288583569 118833811254408825966437677)
                ·
                  refine ⟨44562679220403309737414129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118833811254408825966437677 44562679220403309737414129)
                  ·
                    refine ⟨33422009415302482303060597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44562679220403309737414129 33422009415302482303060597)
                    ·
                      refine ⟨3133313382684607715911931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33422009415302482303060597 3133313382684607715911931)
                      ·
                        rfl

theorem cell23_6102106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_6102106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102106 prefixEnd_6102106 := by exact prefixLift 6102106
  have htrace : WordTrace (prefixWord ++ tailWord_6102106) baseStart_6102106 baseEnd_6102106 := by
    simpa [prefixWord, tailWord_6102106, baseEnd_6102106] using wordTrace_append hprefix tailTrace_6102106
  have hstable : (prefixWord ++ tailWord_6102106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102106).length < 2 ^ (prefixWord ++ tailWord_6102106).sum := by decide
  have hdescent : baseEnd_6102106 < baseStart_6102106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102113 : List Nat := [1, 2, 3, 1, 1, 2, 5, 1, 2, 5]
def baseStart_6102113 : Nat := 118140960795 + 6102113 * 2 ^ 59
def prefixEnd_6102113 : Nat := 4983230072969 + 3 ^ 40 * 6102113 * 2
def baseEnd_6102113 : Nat := 1044438992349729729508133

theorem tailTrace_6102113 : CollatzResearch.WordTrace tailWord_6102113 prefixEnd_6102113 1044438992349729729508133 := by
  unfold tailWord_6102113
  simp only [CollatzResearch.WordTrace]
  refine ⟨222562345342094233775078993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148374896894729489183385995 222562345342094233775078993)
  ·
    refine ⟨166921759006570675331309245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222562345342094233775078993 166921759006570675331309245)
    ·
      refine ⟨62595659627464003249240967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166921759006570675331309245 62595659627464003249240967)
      ·
        refine ⟨93893489441196004873861451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62595659627464003249240967 93893489441196004873861451)
        ·
          refine ⟨140840234161794007310792177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93893489441196004873861451 140840234161794007310792177)
          ·
            refine ⟨105630175621345505483094133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140840234161794007310792177 105630175621345505483094133)
            ·
              refine ⟨9902828964501141139040075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105630175621345505483094133 9902828964501141139040075)
              ·
                refine ⟨14854243446751711708560113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9902828964501141139040075 14854243446751711708560113)
                ·
                  refine ⟨11140682585063783781420085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14854243446751711708560113 11140682585063783781420085)
                  ·
                    refine ⟨1044438992349729729508133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11140682585063783781420085 1044438992349729729508133)
                    ·
                      rfl

theorem cell23_6102113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_6102113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102113 prefixEnd_6102113 := by exact prefixLift 6102113
  have htrace : WordTrace (prefixWord ++ tailWord_6102113) baseStart_6102113 baseEnd_6102113 := by
    simpa [prefixWord, tailWord_6102113, baseEnd_6102113] using wordTrace_append hprefix tailTrace_6102113
  have hstable : (prefixWord ++ tailWord_6102113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102113).length < 2 ^ (prefixWord ++ tailWord_6102113).sum := by decide
  have hdescent : baseEnd_6102113 < baseStart_6102113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102136 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 2, 3, 5]
def baseStart_6102136 : Nat := 118140960795 + 6102136 * 2 ^ 59
def prefixEnd_6102136 : Nat := 4983230072969 + 3 ^ 40 * 6102136 * 2
def baseEnd_6102136 : Nat := 3133328787104242598536793

theorem tailTrace_6102136 : CollatzResearch.WordTrace tailWord_6102136 prefixEnd_6102136 3133328787104242598536793 := by
  unfold tailWord_6102136
  simp only [CollatzResearch.WordTrace]
  refine ⟨111281592110505454351583131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148375456147340605802110841 111281592110505454351583131)
  ·
    refine ⟨166922388165758181527374697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111281592110505454351583131 166922388165758181527374697)
    ·
      refine ⟨125191791124318636145531023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166922388165758181527374697 125191791124318636145531023)
      ·
        refine ⟨187787686686477954218296535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125191791124318636145531023 187787686686477954218296535)
        ·
          refine ⟨281681530029716931327444803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187787686686477954218296535 281681530029716931327444803)
          ·
            refine ⟨422522295044575396991167205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281681530029716931327444803 422522295044575396991167205)
            ·
              refine ⟨79222930320857886935843851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 422522295044575396991167205 79222930320857886935843851)
              ·
                refine ⟨118834395481286830403765777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79222930320857886935843851 118834395481286830403765777)
                ·
                  refine ⟨89125796610965122802824333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118834395481286830403765777 89125796610965122802824333)
                  ·
                    refine ⟨33422173729111921051059125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89125796610965122802824333 33422173729111921051059125)
                    ·
                      refine ⟨3133328787104242598536793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33422173729111921051059125 3133328787104242598536793)
                      ·
                        rfl

theorem cell23_6102136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_6102136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102136 prefixEnd_6102136 := by exact prefixLift 6102136
  have htrace : WordTrace (prefixWord ++ tailWord_6102136) baseStart_6102136 baseEnd_6102136 := by
    simpa [prefixWord, tailWord_6102136, baseEnd_6102136] using wordTrace_append hprefix tailTrace_6102136
  have hstable : (prefixWord ++ tailWord_6102136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102136).length < 2 ^ (prefixWord ++ tailWord_6102136).sum := by decide
  have hdescent : baseEnd_6102136 < baseStart_6102136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102153 : List Nat := [1, 2, 1, 1, 4, 3, 1, 2, 1, 4, 3]
def baseStart_6102153 : Nat := 118140960795 + 6102153 * 2 ^ 59
def prefixEnd_6102153 : Nat := 4983230072969 + 3 ^ 40 * 6102153 * 2
def baseEnd_6102153 : Nat := 3133337516275369032024215

theorem tailTrace_6102153 : CollatzResearch.WordTrace tailWord_6102153 prefixEnd_6102153 3133337516275369032024215 := by
  unfold tailWord_6102153
  simp only [CollatzResearch.WordTrace]
  refine ⟨222563804261949320606535113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148375869507966213737690075 222563804261949320606535113)
  ·
    refine ⟨166922853196461990454901335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222563804261949320606535113 166922853196461990454901335)
    ·
      refine ⟨250384279794692985682352003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166922853196461990454901335 250384279794692985682352003)
      ·
        refine ⟨375576419692039478523528005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250384279794692985682352003 375576419692039478523528005)
        ·
          refine ⟨70420578692257402223161501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 375576419692039478523528005 70420578692257402223161501)
          ·
            refine ⟨26407717009596525833685563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70420578692257402223161501 26407717009596525833685563)
            ·
              refine ⟨39611575514394788750528345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26407717009596525833685563 39611575514394788750528345)
              ·
                refine ⟨29708681635796091562896259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39611575514394788750528345 29708681635796091562896259)
                ·
                  refine ⟨44563022453694137344344389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29708681635796091562896259 44563022453694137344344389)
                  ·
                    refine ⟨8355566710067650752064573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44563022453694137344344389 8355566710067650752064573)
                    ·
                      refine ⟨3133337516275369032024215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8355566710067650752064573 3133337516275369032024215)
                      ·
                        rfl

theorem cell23_6102153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 4, 3].length) (baseStart_6102153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102153 prefixEnd_6102153 := by exact prefixLift 6102153
  have htrace : WordTrace (prefixWord ++ tailWord_6102153) baseStart_6102153 baseEnd_6102153 := by
    simpa [prefixWord, tailWord_6102153, baseEnd_6102153] using wordTrace_append hprefix tailTrace_6102153
  have hstable : (prefixWord ++ tailWord_6102153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102153).length < 2 ^ (prefixWord ++ tailWord_6102153).sum := by decide
  have hdescent : baseEnd_6102153 < baseStart_6102153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102170 : List Nat := [3, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3]
def baseStart_6102170 : Nat := 118140960795 + 6102170 * 2 ^ 59
def prefixEnd_6102170 : Nat := 4983230072969 + 3 ^ 40 * 6102170 * 2
def baseEnd_6102170 : Nat := 3133346245446495465511637

theorem tailTrace_6102170 : CollatzResearch.WordTrace tailWord_6102170 prefixEnd_6102170 3133346245446495465511637 := by
  unfold tailWord_6102170
  simp only [CollatzResearch.WordTrace]
  refine ⟨55641106075721933127475991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148376282868591821673269309 55641106075721933127475991)
  ·
    refine ⟨83461659113582899691213987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55641106075721933127475991 83461659113582899691213987)
    ·
      refine ⟨125192488670374349536820981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83461659113582899691213987 125192488670374349536820981)
      ·
        refine ⟨11736795812847595269076967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125192488670374349536820981 11736795812847595269076967)
        ·
          refine ⟨17605193719271392903615451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11736795812847595269076967 17605193719271392903615451)
          ·
            refine ⟨26407790578907089355423177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17605193719271392903615451 26407790578907089355423177)
            ·
              refine ⟨19805842934180317016567383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26407790578907089355423177 19805842934180317016567383)
              ·
                refine ⟨29708764401270475524851075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19805842934180317016567383 29708764401270475524851075)
                ·
                  refine ⟨44563146601905713287276613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29708764401270475524851075 44563146601905713287276613)
                  ·
                    refine ⟨8355589987857321241364365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44563146601905713287276613 8355589987857321241364365)
                    ·
                      refine ⟨3133346245446495465511637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8355589987857321241364365 3133346245446495465511637)
                      ·
                        rfl

theorem cell23_6102170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_6102170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102170 prefixEnd_6102170 := by exact prefixLift 6102170
  have htrace : WordTrace (prefixWord ++ tailWord_6102170) baseStart_6102170 baseEnd_6102170 := by
    simpa [prefixWord, tailWord_6102170, baseEnd_6102170] using wordTrace_append hprefix tailTrace_6102170
  have hstable : (prefixWord ++ tailWord_6102170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102170).length < 2 ^ (prefixWord ++ tailWord_6102170).sum := by decide
  have hdescent : baseEnd_6102170 < baseStart_6102170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102194 : List Nat := [3, 2, 1, 1, 1, 5, 3, 2, 1, 4]
def baseStart_6102194 : Nat := 118140960795 + 6102194 * 2 ^ 59
def prefixEnd_6102194 : Nat := 4983230072969 + 3 ^ 40 * 6102194 * 2
def baseEnd_6102194 : Nat := 1044452856327401123870509

theorem tailTrace_6102194 : CollatzResearch.WordTrace tailWord_6102194 prefixEnd_6102194 1044452856327401123870509 := by
  unfold tailWord_6102194
  simp only [CollatzResearch.WordTrace]
  refine ⟨55641324913700196152194409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148376866436533856405851757 55641324913700196152194409)
  ·
    refine ⟨41730993685275147114145807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55641324913700196152194409 41730993685275147114145807)
    ·
      refine ⟨62596490527912720671218711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41730993685275147114145807 62596490527912720671218711)
      ·
        refine ⟨93894735791869081006828067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62596490527912720671218711 93894735791869081006828067)
        ·
          refine ⟨140842103687803621510242101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93894735791869081006828067 140842103687803621510242101)
          ·
            refine ⟨13203947220731589516585197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140842103687803621510242101 13203947220731589516585197)
            ·
              refine ⟨4951480207774346068719449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13203947220731589516585197 4951480207774346068719449)
              ·
                refine ⟨3713610155830759551539587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4951480207774346068719449 3713610155830759551539587)
                ·
                  refine ⟨5570415233746139327309381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3713610155830759551539587 5570415233746139327309381)
                  ·
                    refine ⟨1044452856327401123870509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5570415233746139327309381 1044452856327401123870509)
                    ·
                      rfl

theorem cell23_6102194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_6102194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102194 prefixEnd_6102194 := by exact prefixLift 6102194
  have htrace : WordTrace (prefixWord ++ tailWord_6102194) baseStart_6102194 baseEnd_6102194 := by
    simpa [prefixWord, tailWord_6102194, baseEnd_6102194] using wordTrace_append hprefix tailTrace_6102194
  have hstable : (prefixWord ++ tailWord_6102194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102194).length < 2 ^ (prefixWord ++ tailWord_6102194).sum := by decide
  have hdescent : baseEnd_6102194 < baseStart_6102194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102200 : List Nat := [2, 1, 2, 1, 2, 1, 2, 5, 3, 1, 3]
def baseStart_6102200 : Nat := 118140960795 + 6102200 * 2 ^ 59
def prefixEnd_6102200 : Nat := 4983230072969 + 3 ^ 40 * 6102200 * 2
def baseEnd_6102200 : Nat := 3133361649866130348136499

theorem tailTrace_6102200 : CollatzResearch.WordTrace tailWord_6102200 prefixEnd_6102200 3133361649866130348136499 := by
  unfold tailWord_6102200
  simp only [CollatzResearch.WordTrace]
  refine ⟨111282759246389523816748027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148377012328519365088997369 111282759246389523816748027)
  ·
    refine ⟨166924138869584285725122041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111282759246389523816748027 166924138869584285725122041)
    ·
      refine ⟨125193104152188214293841531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166924138869584285725122041 125193104152188214293841531)
      ·
        refine ⟨187789656228282321440762297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125193104152188214293841531 187789656228282321440762297)
        ·
          refine ⟨140842242171211741080571723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187789656228282321440762297 140842242171211741080571723)
          ·
            refine ⟨211263363256817611620857585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140842242171211741080571723 211263363256817611620857585)
            ·
              refine ⟨158447522442613208715643189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211263363256817611620857585 158447522442613208715643189)
              ·
                refine ⟨14854455228994988317091549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 158447522442613208715643189 14854455228994988317091549)
                ·
                  refine ⟨5570420710873120618909331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14854455228994988317091549 5570420710873120618909331)
                  ·
                    refine ⟨8355631066309680928363997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5570420710873120618909331 8355631066309680928363997)
                    ·
                      refine ⟨3133361649866130348136499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8355631066309680928363997 3133361649866130348136499)
                      ·
                        rfl

theorem cell23_6102200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 3, 1, 3].length) (baseStart_6102200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102200 prefixEnd_6102200 := by exact prefixLift 6102200
  have htrace : WordTrace (prefixWord ++ tailWord_6102200) baseStart_6102200 baseEnd_6102200 := by
    simpa [prefixWord, tailWord_6102200, baseEnd_6102200] using wordTrace_append hprefix tailTrace_6102200
  have hstable : (prefixWord ++ tailWord_6102200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102200).length < 2 ^ (prefixWord ++ tailWord_6102200).sum := by decide
  have hdescent : baseEnd_6102200 < baseStart_6102200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102221 : List Nat := [1, 6, 2, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_6102221 : Nat := 118140960795 + 6102221 * 2 ^ 59
def prefixEnd_6102221 : Nat := 4983230072969 + 3 ^ 40 * 6102221 * 2
def baseEnd_6102221 : Nat := 3133372432959874765973903

theorem tailTrace_6102221 : CollatzResearch.WordTrace tailWord_6102221 prefixEnd_6102221 3133372432959874765973903 := by
  unfold tailWord_6102221
  simp only [CollatzResearch.WordTrace]
  refine ⟨222566284425702968220010517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148377522950468645480007011 222566284425702968220010517)
  ·
    refine ⟨10432794582454826635312993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 222566284425702968220010517 10432794582454826635312993)
    ·
      refine ⟨7824595936841119976484745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10432794582454826635312993 7824595936841119976484745)
      ·
        refine ⟨5868446952630839982363559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7824595936841119976484745 5868446952630839982363559)
        ·
          refine ⟨8802670428946259973545339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5868446952630839982363559 8802670428946259973545339)
          ·
            refine ⟨13204005643419389960318009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8802670428946259973545339 13204005643419389960318009)
            ·
              refine ⟨9903004232564542470238507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13204005643419389960318009 9903004232564542470238507)
              ·
                refine ⟨14854506348846813705357761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9903004232564542470238507 14854506348846813705357761)
                ·
                  refine ⟨11140879761635110279018321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14854506348846813705357761 11140879761635110279018321)
                  ·
                    refine ⟨8355659821226332709263741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11140879761635110279018321 8355659821226332709263741)
                    ·
                      refine ⟨3133372432959874765973903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8355659821226332709263741 3133372432959874765973903)
                      ·
                        rfl

theorem cell23_6102221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_6102221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102221 prefixEnd_6102221 := by exact prefixLift 6102221
  have htrace : WordTrace (prefixWord ++ tailWord_6102221) baseStart_6102221 baseEnd_6102221 := by
    simpa [prefixWord, tailWord_6102221, baseEnd_6102221] using wordTrace_append hprefix tailTrace_6102221
  have hstable : (prefixWord ++ tailWord_6102221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102221).length < 2 ^ (prefixWord ++ tailWord_6102221).sum := by decide
  have hdescent : baseEnd_6102221 < baseStart_6102221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102251 : List Nat := [1, 1, 1, 1, 2, 8, 2, 2, 1, 1, 3]
def baseStart_6102251 : Nat := 118140960795 + 6102251 * 2 ^ 59
def prefixEnd_6102251 : Nat := 4983230072969 + 3 ^ 40 * 6102251 * 2
def baseEnd_6102251 : Nat := 3133387837379509648598765

theorem tailTrace_6102251 : CollatzResearch.WordTrace tailWord_6102251 prefixEnd_6102251 3133387837379509648598765 := by
  unfold tailWord_6102251
  simp only [CollatzResearch.WordTrace]
  refine ⟨222567378615594283343602607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148378252410396188895735071 222567378615594283343602607)
  ·
    refine ⟨333851067923391425015403911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222567378615594283343602607 333851067923391425015403911)
    ·
      refine ⟨500776601885087137523105867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333851067923391425015403911 500776601885087137523105867)
      ·
        refine ⟨751164902827630706284658801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500776601885087137523105867 751164902827630706284658801)
        ·
          refine ⟨563373677120723029713494101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 751164902827630706284658801 563373677120723029713494101)
          ·
            refine ⟨6602035278758473004455009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 563373677120723029713494101 6602035278758473004455009)
            ·
              refine ⟨4951526459068854753341257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6602035278758473004455009 4951526459068854753341257)
              ·
                refine ⟨3713644844301641065005943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4951526459068854753341257 3713644844301641065005943)
                ·
                  refine ⟨5570467266452461597508915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3713644844301641065005943 5570467266452461597508915)
                  ·
                    refine ⟨8355700899678692396263373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5570467266452461597508915 8355700899678692396263373)
                    ·
                      refine ⟨3133387837379509648598765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8355700899678692396263373 3133387837379509648598765)
                      ·
                        rfl

theorem cell23_6102251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 1, 1, 3].length) (baseStart_6102251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102251 prefixEnd_6102251 := by exact prefixLift 6102251
  have htrace : WordTrace (prefixWord ++ tailWord_6102251) baseStart_6102251 baseEnd_6102251 := by
    simpa [prefixWord, tailWord_6102251, baseEnd_6102251] using wordTrace_append hprefix tailTrace_6102251
  have hstable : (prefixWord ++ tailWord_6102251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102251).length < 2 ^ (prefixWord ++ tailWord_6102251).sum := by decide
  have hdescent : baseEnd_6102251 < baseStart_6102251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102257 : List Nat := [1, 2, 2, 2, 2, 1, 1, 5, 3, 2, 2]
def baseStart_6102257 : Nat := 118140960795 + 6102257 * 2 ^ 59
def prefixEnd_6102257 : Nat := 4983230072969 + 3 ^ 40 * 6102257 * 2
def baseEnd_6102257 : Nat := 3133390918263436625123737

theorem tailTrace_6102257 : CollatzResearch.WordTrace tailWord_6102257 prefixEnd_6102257 3133390918263436625123737 := by
  unfold tailWord_6102257
  simp only [CollatzResearch.WordTrace]
  refine ⟨222567597453572546368321025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148378398302381697578880683 222567597453572546368321025)
  ·
    refine ⟨166925698090179409776240769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222567597453572546368321025 166925698090179409776240769)
    ·
      refine ⟨125194273567634557332180577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166925698090179409776240769 125194273567634557332180577)
      ·
        refine ⟨93895705175725917999135433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125194273567634557332180577 93895705175725917999135433)
        ·
          refine ⟨70421778881794438499351575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93895705175725917999135433 70421778881794438499351575)
          ·
            refine ⟨105632668322691657749027363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70421778881794438499351575 105632668322691657749027363)
            ·
              refine ⟨158449002484037486623541045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105632668322691657749027363 158449002484037486623541045)
              ·
                refine ⟨14854593982878514370956973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 158449002484037486623541045 14854593982878514370956973)
                ·
                  refine ⟨5570472743579442889108865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14854593982878514370956973 5570472743579442889108865)
                  ·
                    refine ⟨4177854557684582166831649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5570472743579442889108865 4177854557684582166831649)
                    ·
                      refine ⟨3133390918263436625123737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4177854557684582166831649 3133390918263436625123737)
                      ·
                        rfl

theorem cell23_6102257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 2, 2].length) (baseStart_6102257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102257 prefixEnd_6102257 := by exact prefixLift 6102257
  have htrace : WordTrace (prefixWord ++ tailWord_6102257) baseStart_6102257 baseEnd_6102257 := by
    simpa [prefixWord, tailWord_6102257, baseEnd_6102257] using wordTrace_append hprefix tailTrace_6102257
  have hstable : (prefixWord ++ tailWord_6102257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102257).length < 2 ^ (prefixWord ++ tailWord_6102257).sum := by decide
  have hdescent : baseEnd_6102257 < baseStart_6102257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102307 : List Nat := [1, 1, 1, 4, 2, 4, 1, 1, 4, 1, 3]
def baseStart_6102307 : Nat := 118140960795 + 6102307 * 2 ^ 59
def prefixEnd_6102307 : Nat := 4983230072969 + 3 ^ 40 * 6102307 * 2
def baseEnd_6102307 : Nat := 3133416592296161429498507

theorem tailTrace_6102307 : CollatzResearch.WordTrace tailWord_6102307 prefixEnd_6102307 3133416592296161429498507 := by
  unfold tailWord_6102307
  simp only [CollatzResearch.WordTrace]
  refine ⟨222569421103391404907641175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148379614068927603271760783 222569421103391404907641175)
  ·
    refine ⟨333854131655087107361461763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222569421103391404907641175 333854131655087107361461763)
    ·
      refine ⟨500781197482630661042192645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333854131655087107361461763 500781197482630661042192645)
      ·
        refine ⟨93896474527993248945411121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 500781197482630661042192645 93896474527993248945411121)
        ·
          refine ⟨70422355895994936709058341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93896474527993248945411121 70422355895994936709058341)
          ·
            refine ⟨13204191730499050632948439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70422355895994936709058341 13204191730499050632948439)
            ·
              refine ⟨19806287595748575949422659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13204191730499050632948439 19806287595748575949422659)
              ·
                refine ⟨29709431393622863924133989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19806287595748575949422659 29709431393622863924133989)
                ·
                  refine ⟨5570518386304286985775123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29709431393622863924133989 5570518386304286985775123)
                  ·
                    refine ⟨8355777579456430478662685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5570518386304286985775123 8355777579456430478662685)
                    ·
                      refine ⟨3133416592296161429498507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8355777579456430478662685 3133416592296161429498507)
                      ·
                        rfl

theorem cell23_6102307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_6102307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102307 prefixEnd_6102307 := by exact prefixLift 6102307
  have htrace : WordTrace (prefixWord ++ tailWord_6102307) baseStart_6102307 baseEnd_6102307 := by
    simpa [prefixWord, tailWord_6102307, baseEnd_6102307] using wordTrace_append hprefix tailTrace_6102307
  have hstable : (prefixWord ++ tailWord_6102307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102307).length < 2 ^ (prefixWord ++ tailWord_6102307).sum := by decide
  have hdescent : baseEnd_6102307 < baseStart_6102307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102313 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 6, 3, 4]
def baseStart_6102313 : Nat := 118140960795 + 6102313 * 2 ^ 59
def prefixEnd_6102313 : Nat := 4983230072969 + 3 ^ 40 * 6102313 * 2
def baseEnd_6102313 : Nat := 3133419673180088406023479

theorem tailTrace_6102313 : CollatzResearch.WordTrace tailWord_6102313 prefixEnd_6102313 3133419673180088406023479 := by
  unfold tailWord_6102313
  simp only [CollatzResearch.WordTrace]
  refine ⟨222569639941369667932359593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148379759960913111954906395 222569639941369667932359593)
  ·
    refine ⟨166927229956027250949269695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222569639941369667932359593 166927229956027250949269695)
    ·
      refine ⟨250390844934040876423904543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166927229956027250949269695 250390844934040876423904543)
      ·
        refine ⟨375586267401061314635856815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250390844934040876423904543 375586267401061314635856815)
        ·
          refine ⟨563379401101591971953785223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375586267401061314635856815 563379401101591971953785223)
          ·
            refine ⟨845069101652387957930677835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563379401101591971953785223 845069101652387957930677835)
            ·
              refine ⟨1267603652478581936896016753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 845069101652387957930677835 1267603652478581936896016753)
              ·
                refine ⟨950702739358936452672012565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1267603652478581936896016753 950702739358936452672012565)
                ·
                  refine ⟨44564190907450146219000589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 950702739358936452672012565 44564190907450146219000589)
                  ·
                    refine ⟨16711571590293804832125221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44564190907450146219000589 16711571590293804832125221)
                    ·
                      refine ⟨3133419673180088406023479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16711571590293804832125221 3133419673180088406023479)
                      ·
                        rfl

theorem cell23_6102313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 3, 4].length) (baseStart_6102313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102313 prefixEnd_6102313 := by exact prefixLift 6102313
  have htrace : WordTrace (prefixWord ++ tailWord_6102313) baseStart_6102313 baseEnd_6102313 := by
    simpa [prefixWord, tailWord_6102313, baseEnd_6102313] using wordTrace_append hprefix tailTrace_6102313
  have hstable : (prefixWord ++ tailWord_6102313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102313).length < 2 ^ (prefixWord ++ tailWord_6102313).sum := by decide
  have hdescent : baseEnd_6102313 < baseStart_6102313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102350 : List Nat := [4, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5]
def baseStart_6102350 : Nat := 118140960795 + 6102350 * 2 ^ 59
def prefixEnd_6102350 : Nat := 4983230072969 + 3 ^ 40 * 6102350 * 2
def baseEnd_6102350 : Nat := 3133438671964304761260809

theorem tailTrace_6102350 : CollatzResearch.WordTrace tailWord_6102350 prefixEnd_6102350 3133438671964304761260809 := by
  unfold tailWord_6102350
  simp only [CollatzResearch.WordTrace]
  refine ⟨27821373680279452906432063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148380659628157082167637669 27821373680279452906432063)
  ·
    refine ⟨41732060520419179359648095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27821373680279452906432063 41732060520419179359648095)
    ·
      refine ⟨62598090780628769039472143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41732060520419179359648095 62598090780628769039472143)
      ·
        refine ⟨93897136170943153559208215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62598090780628769039472143 93897136170943153559208215)
        ·
          refine ⟨140845704256414730338812323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93897136170943153559208215 140845704256414730338812323)
          ·
            refine ⟨211268556384622095508218485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140845704256414730338812323 211268556384622095508218485)
            ·
              refine ⟨19806427161058321453895483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 211268556384622095508218485 19806427161058321453895483)
              ·
                refine ⟨29709640741587482180843225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19806427161058321453895483 29709640741587482180843225)
                ·
                  refine ⟨22282230556190611635632419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29709640741587482180843225 22282230556190611635632419)
                  ·
                    refine ⟨33423345834285917453448629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22282230556190611635632419 33423345834285917453448629)
                    ·
                      refine ⟨3133438671964304761260809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33423345834285917453448629 3133438671964304761260809)
                      ·
                        rfl

theorem cell23_6102350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_6102350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102350 prefixEnd_6102350 := by exact prefixLift 6102350
  have htrace : WordTrace (prefixWord ++ tailWord_6102350) baseStart_6102350 baseEnd_6102350 := by
    simpa [prefixWord, tailWord_6102350, baseEnd_6102350] using wordTrace_append hprefix tailTrace_6102350
  have hstable : (prefixWord ++ tailWord_6102350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102350).length < 2 ^ (prefixWord ++ tailWord_6102350).sum := by decide
  have hdescent : baseEnd_6102350 < baseStart_6102350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102381 : List Nat := [1, 5, 1, 1, 1, 4, 1, 3, 2, 2, 2]
def baseStart_6102381 : Nat := 118140960795 + 6102381 * 2 ^ 59
def prefixEnd_6102381 : Nat := 4983230072969 + 3 ^ 40 * 6102381 * 2
def baseEnd_6102381 : Nat := 3133454589864594139973167

theorem tailTrace_6102381 : CollatzResearch.WordTrace tailWord_6102381 prefixEnd_6102381 3133454589864594139973167 := by
  unfold tailWord_6102381
  simp only [CollatzResearch.WordTrace]
  refine ⟨222572120105123315545834997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148381413403415543697223331 222572120105123315545834997)
  ·
    refine ⟨20866136259855310832422031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 222572120105123315545834997 20866136259855310832422031)
    ·
      refine ⟨31299204389782966248633047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20866136259855310832422031 31299204389782966248633047)
      ·
        refine ⟨46948806584674449372949571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31299204389782966248633047 46948806584674449372949571)
        ·
          refine ⟨70423209877011674059424357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46948806584674449372949571 70423209877011674059424357)
          ·
            refine ⟨13204351851939688886142067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70423209877011674059424357 13204351851939688886142067)
            ·
              refine ⟨19806527777909533329213101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13204351851939688886142067 19806527777909533329213101)
              ·
                refine ⟨7427447916716074998454913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19806527777909533329213101 7427447916716074998454913)
                ·
                  refine ⟨5570585937537056248841185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7427447916716074998454913 5570585937537056248841185)
                  ·
                    refine ⟨4177939453152792186630889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5570585937537056248841185 4177939453152792186630889)
                    ·
                      refine ⟨3133454589864594139973167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4177939453152792186630889 3133454589864594139973167)
                      ·
                        rfl

theorem cell23_6102381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_6102381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102381 prefixEnd_6102381 := by exact prefixLift 6102381
  have htrace : WordTrace (prefixWord ++ tailWord_6102381) baseStart_6102381 baseEnd_6102381 := by
    simpa [prefixWord, tailWord_6102381, baseEnd_6102381] using wordTrace_append hprefix tailTrace_6102381
  have hstable : (prefixWord ++ tailWord_6102381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102381).length < 2 ^ (prefixWord ++ tailWord_6102381).sum := by decide
  have hdescent : baseEnd_6102381 < baseStart_6102381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102398 : List Nat := [4, 2, 3, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_6102398 : Nat := 118140960795 + 6102398 * 2 ^ 59
def prefixEnd_6102398 : Nat := 4983230072969 + 3 ^ 40 * 6102398 * 2
def baseEnd_6102398 : Nat := 3133463319035720573460589

theorem tailTrace_6102398 : CollatzResearch.WordTrace tailWord_6102398 prefixEnd_6102398 3133463319035720573460589 := by
  unfold tailWord_6102398
  simp only [CollatzResearch.WordTrace]
  refine ⟨27821592518257715931150481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148381826764041151632802565 27821592518257715931150481)
  ·
    refine ⟨20866194388693286948362861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27821592518257715931150481 20866194388693286948362861)
    ·
      refine ⟨7824822895759982605636073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20866194388693286948362861 7824822895759982605636073)
      ·
        refine ⟨5868617171819986954227055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7824822895759982605636073 5868617171819986954227055)
        ·
          refine ⟨8802925757729980431340583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5868617171819986954227055 8802925757729980431340583)
          ·
            refine ⟨13204388636594970647010875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8802925757729980431340583 13204388636594970647010875)
            ·
              refine ⟨19806582954892455970516313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13204388636594970647010875 19806582954892455970516313)
              ·
                refine ⟨14854937216169341977887235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19806582954892455970516313 14854937216169341977887235)
                ·
                  refine ⟨22282405824254012966830853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14854937216169341977887235 22282405824254012966830853)
                  ·
                    refine ⟨4177951092047627431280785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22282405824254012966830853 4177951092047627431280785)
                    ·
                      refine ⟨3133463319035720573460589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4177951092047627431280785 3133463319035720573460589)
                      ·
                        rfl

theorem cell23_6102398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_6102398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102398 prefixEnd_6102398 := by exact prefixLift 6102398
  have htrace : WordTrace (prefixWord ++ tailWord_6102398) baseStart_6102398 baseEnd_6102398 := by
    simpa [prefixWord, tailWord_6102398, baseEnd_6102398] using wordTrace_append hprefix tailTrace_6102398
  have hstable : (prefixWord ++ tailWord_6102398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102398).length < 2 ^ (prefixWord ++ tailWord_6102398).sum := by decide
  have hdescent : baseEnd_6102398 < baseStart_6102398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102450 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4]
def baseStart_6102450 : Nat := 118140960795 + 6102450 * 2 ^ 59
def prefixEnd_6102450 : Nat := 4983230072969 + 3 ^ 40 * 6102450 * 2
def baseEnd_6102450 : Nat := 3133490020029754370010349

theorem tailTrace_6102450 : CollatzResearch.WordTrace tailWord_6102450 prefixEnd_6102450 3133490020029754370010349 := by
  unfold tailWord_6102450
  simp only [CollatzResearch.WordTrace]
  refine ⟨55643659185468335082524201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148383091161248893553397869 55643659185468335082524201)
  ·
    refine ⟨41732744389101251311893151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55643659185468335082524201 41732744389101251311893151)
    ·
      refine ⟨62599116583651876967839727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41732744389101251311893151 62599116583651876967839727)
      ·
        refine ⟨93898674875477815451759591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62599116583651876967839727 93898674875477815451759591)
        ·
          refine ⟨140848012313216723177639387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93898674875477815451759591 140848012313216723177639387)
          ·
            refine ⟨211272018469825084766459081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140848012313216723177639387 211272018469825084766459081)
            ·
              refine ⟨158454013852368813574844311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211272018469825084766459081 158454013852368813574844311)
              ·
                refine ⟨237681020778553220362266467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158454013852368813574844311 237681020778553220362266467)
                ·
                  refine ⟨356521531167829830543399701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 237681020778553220362266467 356521531167829830543399701)
                  ·
                    refine ⟨16711946773492023306721861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 356521531167829830543399701 16711946773492023306721861)
                    ·
                      refine ⟨3133490020029754370010349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16711946773492023306721861 3133490020029754370010349)
                      ·
                        rfl

theorem cell23_6102450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_6102450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102450 prefixEnd_6102450 := by exact prefixLift 6102450
  have htrace : WordTrace (prefixWord ++ tailWord_6102450) baseStart_6102450 baseEnd_6102450 := by
    simpa [prefixWord, tailWord_6102450, baseEnd_6102450] using wordTrace_append hprefix tailTrace_6102450
  have hstable : (prefixWord ++ tailWord_6102450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102450).length < 2 ^ (prefixWord ++ tailWord_6102450).sum := by decide
  have hdescent : baseEnd_6102450 < baseStart_6102450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102464 : List Nat := [2, 1, 1, 2, 3, 1, 3, 5, 1, 4]
def baseStart_6102464 : Nat := 118140960795 + 6102464 * 2 ^ 59
def prefixEnd_6102464 : Nat := 4983230072969 + 3 ^ 40 * 6102464 * 2
def baseEnd_6102464 : Nat := 1044499069586305771745095

theorem tailTrace_6102464 : CollatzResearch.WordTrace tailWord_6102464 prefixEnd_6102464 1044499069586305771745095 := by
  unfold tailWord_6102464
  simp only [CollatzResearch.WordTrace]
  refine ⟨111287573681911310360553223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148383431575881747147404297 111287573681911310360553223)
  ·
    refine ⟨166931360522866965540829835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111287573681911310360553223 166931360522866965540829835)
    ·
      refine ⟨250397040784300448311244753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166931360522866965540829835 250397040784300448311244753)
      ·
        refine ⟨187797780588225336233433565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250397040784300448311244753 187797780588225336233433565)
        ·
          refine ⟨70424167720584501087537587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187797780588225336233433565 70424167720584501087537587)
          ·
            refine ⟨105636251580876751631306381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70424167720584501087537587 105636251580876751631306381)
            ·
              refine ⟨39613594342828781861739893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105636251580876751631306381 39613594342828781861739893)
              ·
                refine ⟨3713774469640198299538115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39613594342828781861739893 3713774469640198299538115)
                ·
                  refine ⟨5570661704460297449307173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3713774469640198299538115 5570661704460297449307173)
                  ·
                    refine ⟨1044499069586305771745095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5570661704460297449307173 1044499069586305771745095)
                    ·
                      rfl

theorem cell23_6102464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 1, 4].length) (baseStart_6102464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102464 prefixEnd_6102464 := by exact prefixLift 6102464
  have htrace : WordTrace (prefixWord ++ tailWord_6102464) baseStart_6102464 baseEnd_6102464 := by
    simpa [prefixWord, tailWord_6102464, baseEnd_6102464] using wordTrace_append hprefix tailTrace_6102464
  have hstable : (prefixWord ++ tailWord_6102464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102464).length < 2 ^ (prefixWord ++ tailWord_6102464).sum := by decide
  have hdescent : baseEnd_6102464 < baseStart_6102464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102466 : List Nat := [3, 5, 2, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_6102466 : Nat := 118140960795 + 6102466 * 2 ^ 59
def prefixEnd_6102466 : Nat := 4983230072969 + 3 ^ 40 * 6102466 * 2
def baseEnd_6102466 : Nat := 3133498235720226307410277

theorem tailTrace_6102466 : CollatzResearch.WordTrace tailWord_6102466 prefixEnd_6102466 3133498235720226307410277 := by
  unfold tailWord_6102466
  simp only [CollatzResearch.WordTrace]
  refine ⟨55643805077453843765669813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148383480206543583375119501 55643805077453843765669813)
  ·
    refine ⟨5216606726011297853031545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55643805077453843765669813 5216606726011297853031545)
    ·
      refine ⟨3912455044508473389773659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5216606726011297853031545 3912455044508473389773659)
      ·
        refine ⟨5868682566762710084660489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3912455044508473389773659 5868682566762710084660489)
        ·
          refine ⟨4401511925072032563495367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5868682566762710084660489 4401511925072032563495367)
          ·
            refine ⟨6602267887608048845243051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4401511925072032563495367 6602267887608048845243051)
            ·
              refine ⟨9903401831412073267864577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6602267887608048845243051 9903401831412073267864577)
              ·
                refine ⟨7427551373559054950898433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9903401831412073267864577 7427551373559054950898433)
                ·
                  refine ⟨5570663530169291213173825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7427551373559054950898433 5570663530169291213173825)
                  ·
                    refine ⟨4177997647626968409880369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5570663530169291213173825 4177997647626968409880369)
                    ·
                      refine ⟨3133498235720226307410277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4177997647626968409880369 3133498235720226307410277)
                      ·
                        rfl

theorem cell23_6102466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_6102466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102466 prefixEnd_6102466 := by exact prefixLift 6102466
  have htrace : WordTrace (prefixWord ++ tailWord_6102466) baseStart_6102466 baseEnd_6102466 := by
    simpa [prefixWord, tailWord_6102466, baseEnd_6102466] using wordTrace_append hprefix tailTrace_6102466
  have hstable : (prefixWord ++ tailWord_6102466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102466).length < 2 ^ (prefixWord ++ tailWord_6102466).sum := by decide
  have hdescent : baseEnd_6102466 < baseStart_6102466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102500 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 2, 1, 7]
def baseStart_6102500 : Nat := 118140960795 + 6102500 * 2 ^ 59
def prefixEnd_6102500 : Nat := 4983230072969 + 3 ^ 40 * 6102500 * 2
def baseEnd_6102500 : Nat := 3133515694062479174385119

theorem tailTrace_6102500 : CollatzResearch.WordTrace tailWord_6102500 prefixEnd_6102500 3133515694062479174385119 := by
  unfold tailWord_6102500
  simp only [CollatzResearch.WordTrace]
  refine ⟨111288230195846099434708477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148384306927794799246277969 111288230195846099434708477)
  ·
    refine ⟨41733086323442287288015679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111288230195846099434708477 41733086323442287288015679)
    ·
      refine ⟨62599629485163430932023519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41733086323442287288015679 62599629485163430932023519)
      ·
        refine ⟨93899444227745146398035279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62599629485163430932023519 93899444227745146398035279)
        ·
          refine ⟨140849166341617719597052919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93899444227745146398035279 140849166341617719597052919)
          ·
            refine ⟨211273749512426579395579379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140849166341617719597052919 211273749512426579395579379)
            ·
              refine ⟨316910624268639869093369069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211273749512426579395579379 316910624268639869093369069)
              ·
                refine ⟨118841484100739950910013401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 316910624268639869093369069 118841484100739950910013401)
                ·
                  refine ⟨89131113075554963182510051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118841484100739950910013401 89131113075554963182510051)
                  ·
                    refine ⟨133696669613332444773765077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89131113075554963182510051 133696669613332444773765077)
                    ·
                      refine ⟨3133515694062479174385119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 133696669613332444773765077 3133515694062479174385119)
                      ·
                        rfl

theorem cell23_6102500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_6102500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102500 prefixEnd_6102500 := by exact prefixLift 6102500
  have htrace : WordTrace (prefixWord ++ tailWord_6102500) baseStart_6102500 baseEnd_6102500 := by
    simpa [prefixWord, tailWord_6102500, baseEnd_6102500] using wordTrace_append hprefix tailTrace_6102500
  have hstable : (prefixWord ++ tailWord_6102500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102500).length < 2 ^ (prefixWord ++ tailWord_6102500).sum := by decide
  have hdescent : baseEnd_6102500 < baseStart_6102500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102504 : List Nat := [2, 1, 4, 1, 1, 2, 1, 4, 3, 1, 3]
def baseStart_6102504 : Nat := 118140960795 + 6102504 * 2 ^ 59
def prefixEnd_6102504 : Nat := 4983230072969 + 3 ^ 40 * 6102504 * 2
def baseEnd_6102504 : Nat := 3133517747985097158735101

theorem tailTrace_6102504 : CollatzResearch.WordTrace tailWord_6102504 prefixEnd_6102504 3133517747985097158735101 := by
  unfold tailWord_6102504
  simp only [CollatzResearch.WordTrace]
  refine ⟨111288303141838853776281283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148384404189118471701708377 111288303141838853776281283)
  ·
    refine ⟨166932454712758280664421925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111288303141838853776281283 166932454712758280664421925)
    ·
      refine ⟨31299835258642177624579111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166932454712758280664421925 31299835258642177624579111)
      ·
        refine ⟨46949752887963266436868667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31299835258642177624579111 46949752887963266436868667)
        ·
          refine ⟨70424629331944899655303001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46949752887963266436868667 70424629331944899655303001)
          ·
            refine ⟨52818471998958674741477251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70424629331944899655303001 52818471998958674741477251)
            ·
              refine ⟨79227707998438012112215877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52818471998958674741477251 79227707998438012112215877)
              ·
                refine ⟨14855195249707127271040477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79227707998438012112215877 14855195249707127271040477)
                ·
                  refine ⟨5570698218640172726640179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14855195249707127271040477 5570698218640172726640179)
                  ·
                    refine ⟨8356047327960259089960269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5570698218640172726640179 8356047327960259089960269)
                    ·
                      refine ⟨3133517747985097158735101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8356047327960259089960269 3133517747985097158735101)
                      ·
                        rfl

theorem cell23_6102504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_6102504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102504 prefixEnd_6102504 := by exact prefixLift 6102504
  have htrace : WordTrace (prefixWord ++ tailWord_6102504) baseStart_6102504 baseEnd_6102504 := by
    simpa [prefixWord, tailWord_6102504, baseEnd_6102504] using wordTrace_append hprefix tailTrace_6102504
  have hstable : (prefixWord ++ tailWord_6102504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102504).length < 2 ^ (prefixWord ++ tailWord_6102504).sum := by decide
  have hdescent : baseEnd_6102504 < baseStart_6102504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102537 : List Nat := [1, 2, 1, 1, 3, 1, 3, 3, 4, 4]
def baseStart_6102537 : Nat := 118140960795 + 6102537 * 2 ^ 59
def prefixEnd_6102537 : Nat := 4983230072969 + 3 ^ 40 * 6102537 * 2
def baseEnd_6102537 : Nat := 1044511564282231843207483

theorem tailTrace_6102537 : CollatzResearch.WordTrace tailWord_6102537 prefixEnd_6102537 1044511564282231843207483 := by
  unfold tailWord_6102537
  simp only [CollatzResearch.WordTrace]
  refine ⟨222577809892558154188513865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148385206595038769459009243 222577809892558154188513865)
  ·
    refine ⟨166933357419418615641385399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222577809892558154188513865 166933357419418615641385399)
    ·
      refine ⟨250400036129127923462078099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166933357419418615641385399 250400036129127923462078099)
      ·
        refine ⟨375600054193691885193117149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250400036129127923462078099 375600054193691885193117149)
        ·
          refine ⟨140850020322634456947418931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 375600054193691885193117149 140850020322634456947418931)
          ·
            refine ⟨211275030483951685421128397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140850020322634456947418931 211275030483951685421128397)
            ·
              refine ⟨79228136431481882032923149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211275030483951685421128397 79228136431481882032923149)
              ·
                refine ⟨29710551161805705762346181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79228136431481882032923149 29710551161805705762346181)
                ·
                  refine ⟨5570728342838569830439909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29710551161805705762346181 5570728342838569830439909)
                  ·
                    refine ⟨1044511564282231843207483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5570728342838569830439909 1044511564282231843207483)
                    ·
                      rfl

theorem cell23_6102537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 4].length) (baseStart_6102537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102537 prefixEnd_6102537 := by exact prefixLift 6102537
  have htrace : WordTrace (prefixWord ++ tailWord_6102537) baseStart_6102537 baseEnd_6102537 := by
    simpa [prefixWord, tailWord_6102537, baseEnd_6102537] using wordTrace_append hprefix tailTrace_6102537
  have hstable : (prefixWord ++ tailWord_6102537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102537).length < 2 ^ (prefixWord ++ tailWord_6102537).sum := by decide
  have hdescent : baseEnd_6102537 < baseStart_6102537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102547 : List Nat := [1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 5]
def baseStart_6102547 : Nat := 118140960795 + 6102547 * 2 ^ 59
def prefixEnd_6102547 : Nat := 4983230072969 + 3 ^ 40 * 6102547 * 2
def baseEnd_6102547 : Nat := 3133539827653240490497403

theorem tailTrace_6102547 : CollatzResearch.WordTrace tailWord_6102547 prefixEnd_6102547 3133539827653240490497403 := by
  unfold tailWord_6102547
  simp only [CollatzResearch.WordTrace]
  refine ⟨222578174622521925896377895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148385449748347950597585263 222578174622521925896377895)
  ·
    refine ⟨333867261933782888844566843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222578174622521925896377895 333867261933782888844566843)
    ·
      refine ⟨500800892900674333266850265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333867261933782888844566843 500800892900674333266850265)
      ·
        refine ⟨375600669675505749950137699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 500800892900674333266850265 375600669675505749950137699)
        ·
          refine ⟨563401004513258624925206549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375600669675505749950137699 563401004513258624925206549)
          ·
            refine ⟨26409422086558998043369057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 563401004513258624925206549 26409422086558998043369057)
            ·
              refine ⟨19807066564919248532526793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26409422086558998043369057 19807066564919248532526793)
              ·
                refine ⟨14855299923689436399395095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19807066564919248532526793 14855299923689436399395095)
                ·
                  refine ⟨22282949885534154599092643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14855299923689436399395095 22282949885534154599092643)
                  ·
                    refine ⟨33424424828301231898638965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22282949885534154599092643 33424424828301231898638965)
                    ·
                      refine ⟨3133539827653240490497403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33424424828301231898638965 3133539827653240490497403)
                      ·
                        rfl

theorem cell23_6102547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 5].length) (baseStart_6102547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102547 prefixEnd_6102547 := by exact prefixLift 6102547
  have htrace : WordTrace (prefixWord ++ tailWord_6102547) baseStart_6102547 baseEnd_6102547 := by
    simpa [prefixWord, tailWord_6102547, baseEnd_6102547] using wordTrace_append hprefix tailTrace_6102547
  have hstable : (prefixWord ++ tailWord_6102547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102547).length < 2 ^ (prefixWord ++ tailWord_6102547).sum := by decide
  have hdescent : baseEnd_6102547 < baseStart_6102547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102557 : List Nat := [1, 4, 2, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_6102557 : Nat := 118140960795 + 6102557 * 2 ^ 59
def prefixEnd_6102557 : Nat := 4983230072969 + 3 ^ 40 * 6102557 * 2
def baseEnd_6102557 : Nat := 3133544962459785451372357

theorem tailTrace_6102557 : CollatzResearch.WordTrace tailWord_6102557 prefixEnd_6102557 3133544962459785451372357 := by
  unfold tailWord_6102557
  simp only [CollatzResearch.WordTrace]
  refine ⟨222578539352485697604241925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148385692901657131736161283 222578539352485697604241925)
  ·
    refine ⟨41733476128591068300795361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222578539352485697604241925 41733476128591068300795361)
    ·
      refine ⟨31300107096443301225596521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41733476128591068300795361 31300107096443301225596521)
      ·
        refine ⟨23475080322332475919197391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31300107096443301225596521 23475080322332475919197391)
        ·
          refine ⟨35212620483498713878796087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23475080322332475919197391 35212620483498713878796087)
          ·
            refine ⟨52818930725248070818194131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35212620483498713878796087 52818930725248070818194131)
            ·
              refine ⟨79228396087872106227291197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52818930725248070818194131 79228396087872106227291197)
              ·
                refine ⟨29710648532952039835234199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79228396087872106227291197 29710648532952039835234199)
                ·
                  refine ⟨44565972799428059752851299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29710648532952039835234199 44565972799428059752851299)
                  ·
                    refine ⟨66848959199142089629276949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44565972799428059752851299 66848959199142089629276949)
                    ·
                      refine ⟨3133544962459785451372357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66848959199142089629276949 3133544962459785451372357)
                      ·
                        rfl

theorem cell23_6102557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_6102557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102557 prefixEnd_6102557 := by exact prefixLift 6102557
  have htrace : WordTrace (prefixWord ++ tailWord_6102557) baseStart_6102557 baseEnd_6102557 := by
    simpa [prefixWord, tailWord_6102557, baseEnd_6102557] using wordTrace_append hprefix tailTrace_6102557
  have hstable : (prefixWord ++ tailWord_6102557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102557).length < 2 ^ (prefixWord ++ tailWord_6102557).sum := by decide
  have hdescent : baseEnd_6102557 < baseStart_6102557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102561 : List Nat := [1, 2, 3, 2, 2, 4, 1, 2, 1, 1, 4]
def baseStart_6102561 : Nat := 118140960795 + 6102561 * 2 ^ 59
def prefixEnd_6102561 : Nat := 4983230072969 + 3 ^ 40 * 6102561 * 2
def baseEnd_6102561 : Nat := 3133547016382403435722339

theorem tailTrace_6102561 : CollatzResearch.WordTrace tailWord_6102561 prefixEnd_6102561 3133547016382403435722339 := by
  unfold tailWord_6102561
  simp only [CollatzResearch.WordTrace]
  refine ⟨222578685244471206287387537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148385790162980804191591691 222578685244471206287387537)
  ·
    refine ⟨166934013933353404715540653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222578685244471206287387537 166934013933353404715540653)
    ·
      refine ⟨62600255225007526768327745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166934013933353404715540653 62600255225007526768327745)
      ·
        refine ⟨46950191418755645076245809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62600255225007526768327745 46950191418755645076245809)
        ·
          refine ⟨35212643564066733807184357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46950191418755645076245809 35212643564066733807184357)
          ·
            refine ⟨6602370668262512588847067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35212643564066733807184357 6602370668262512588847067)
            ·
              refine ⟨9903556002393768883270601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6602370668262512588847067 9903556002393768883270601)
              ·
                refine ⟨7427667001795326662452951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9903556002393768883270601 7427667001795326662452951)
                ·
                  refine ⟨11141500502692989993679427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7427667001795326662452951 11141500502692989993679427)
                  ·
                    refine ⟨16712250754039484990519141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11141500502692989993679427 16712250754039484990519141)
                    ·
                      refine ⟨3133547016382403435722339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16712250754039484990519141 3133547016382403435722339)
                      ·
                        rfl

theorem cell23_6102561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_6102561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102561 prefixEnd_6102561 := by exact prefixLift 6102561
  have htrace : WordTrace (prefixWord ++ tailWord_6102561) baseStart_6102561 baseEnd_6102561 := by
    simpa [prefixWord, tailWord_6102561, baseEnd_6102561] using wordTrace_append hprefix tailTrace_6102561
  have hstable : (prefixWord ++ tailWord_6102561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102561).length < 2 ^ (prefixWord ++ tailWord_6102561).sum := by decide
  have hdescent : baseEnd_6102561 < baseStart_6102561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102574 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_6102574 : Nat := 118140960795 + 6102574 * 2 ^ 59
def prefixEnd_6102574 : Nat := 4983230072969 + 3 ^ 40 * 6102574 * 2
def baseEnd_6102574 : Nat := 3133553691630911884859779

theorem tailTrace_6102574 : CollatzResearch.WordTrace tailWord_6102574 prefixEnd_6102574 3133553691630911884859779 := by
  unfold tailWord_6102574
  simp only [CollatzResearch.WordTrace]
  refine ⟨27822394924178013688451347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148386106262282739671740517 27822394924178013688451347)
  ·
    refine ⟨41733592386267020532677021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27822394924178013688451347 41733592386267020532677021)
    ·
      refine ⟨15650097144850132699753883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41733592386267020532677021 15650097144850132699753883)
      ·
        refine ⟨23475145717275199049630825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15650097144850132699753883 23475145717275199049630825)
        ·
          refine ⟨17606359287956399287223119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23475145717275199049630825 17606359287956399287223119)
          ·
            refine ⟨26409538931934598930834679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17606359287956399287223119 26409538931934598930834679)
            ·
              refine ⟨39614308397901898396252019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26409538931934598930834679 39614308397901898396252019)
              ·
                refine ⟨59421462596852847594378029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39614308397901898396252019 59421462596852847594378029)
                ·
                  refine ⟨22283048473819817847891761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59421462596852847594378029 22283048473819817847891761)
                  ·
                    refine ⟨16712286355364863385918821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22283048473819817847891761 16712286355364863385918821)
                    ·
                      refine ⟨3133553691630911884859779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16712286355364863385918821 3133553691630911884859779)
                      ·
                        rfl

theorem cell23_6102574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_6102574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102574 prefixEnd_6102574 := by exact prefixLift 6102574
  have htrace : WordTrace (prefixWord ++ tailWord_6102574) baseStart_6102574 baseEnd_6102574 := by
    simpa [prefixWord, tailWord_6102574, baseEnd_6102574] using wordTrace_append hprefix tailTrace_6102574
  have hstable : (prefixWord ++ tailWord_6102574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102574).length < 2 ^ (prefixWord ++ tailWord_6102574).sum := by decide
  have hdescent : baseEnd_6102574 < baseStart_6102574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102578 : List Nat := [3, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2]
def baseStart_6102578 : Nat := 118140960795 + 6102578 * 2 ^ 59
def prefixEnd_6102578 : Nat := 4983230072969 + 3 ^ 40 * 6102578 * 2
def baseEnd_6102578 : Nat := 3133555745553529869209761

theorem tailTrace_6102578 : CollatzResearch.WordTrace tailWord_6102578 prefixEnd_6102578 3133555745553529869209761 := by
  unfold tailWord_6102578
  simp only [CollatzResearch.WordTrace]
  refine ⟨55644826321352404547689097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148386203523606412127170925 55644826321352404547689097)
  ·
    refine ⟨41733619741014303410766823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55644826321352404547689097 41733619741014303410766823)
    ·
      refine ⟨62600429611521455116150235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41733619741014303410766823 62600429611521455116150235)
      ·
        refine ⟨93900644417282182674225353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62600429611521455116150235 93900644417282182674225353)
        ·
          refine ⟨70425483312961637005669015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93900644417282182674225353 70425483312961637005669015)
          ·
            refine ⟨105638224969442455508503523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70425483312961637005669015 105638224969442455508503523)
            ·
              refine ⟨158457337454163683262755285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105638224969442455508503523 158457337454163683262755285)
              ·
                refine ⟨3713843846581961326470827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 158457337454163683262755285 3713843846581961326470827)
                ·
                  refine ⟨5570765769872941989706241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3713843846581961326470827 5570765769872941989706241)
                  ·
                    refine ⟨4178074327404706492279681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5570765769872941989706241 4178074327404706492279681)
                    ·
                      refine ⟨3133555745553529869209761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4178074327404706492279681 3133555745553529869209761)
                      ·
                        rfl

theorem cell23_6102578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2].length) (baseStart_6102578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102578 prefixEnd_6102578 := by exact prefixLift 6102578
  have htrace : WordTrace (prefixWord ++ tailWord_6102578) baseStart_6102578 baseEnd_6102578 := by
    simpa [prefixWord, tailWord_6102578, baseEnd_6102578] using wordTrace_append hprefix tailTrace_6102578
  have hstable : (prefixWord ++ tailWord_6102578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102578).length < 2 ^ (prefixWord ++ tailWord_6102578).sum := by decide
  have hdescent : baseEnd_6102578 < baseStart_6102578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102645 : List Nat := [1, 3, 4, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_6102645 : Nat := 118140960795 + 6102645 * 2 ^ 59
def prefixEnd_6102645 : Nat := 4983230072969 + 3 ^ 40 * 6102645 * 2
def baseEnd_6102645 : Nat := 3133590148757381107071953

theorem tailTrace_6102645 : CollatzResearch.WordTrace tailWord_6102645 prefixEnd_6102645 3133590148757381107071953 := by
  unfold tailWord_6102645
  simp only [CollatzResearch.WordTrace]
  refine ⟨222581748976166888633445389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148387832650777925755630259 222581748976166888633445389)
  ·
    refine ⟨83468155866062583237542021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222581748976166888633445389 83468155866062583237542021)
    ·
      refine ⟨15650279224886734357039129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83468155866062583237542021 15650279224886734357039129)
      ·
        refine ⟨11737709418665050767779347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15650279224886734357039129 11737709418665050767779347)
        ·
          refine ⟨17606564127997576151669021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11737709418665050767779347 17606564127997576151669021)
          ·
            refine ⟨6602461547999091056875883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17606564127997576151669021 6602461547999091056875883)
            ·
              refine ⟨9903692321998636585313825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6602461547999091056875883 9903692321998636585313825)
              ·
                refine ⟨7427769241498977438985369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9903692321998636585313825 7427769241498977438985369)
                ·
                  refine ⟨5570826931124233079239027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7427769241498977438985369 5570826931124233079239027)
                  ·
                    refine ⟨8356240396686349618858541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5570826931124233079239027 8356240396686349618858541)
                    ·
                      refine ⟨3133590148757381107071953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8356240396686349618858541 3133590148757381107071953)
                      ·
                        rfl

theorem cell23_6102645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_6102645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102645 prefixEnd_6102645 := by exact prefixLift 6102645
  have htrace : WordTrace (prefixWord ++ tailWord_6102645) baseStart_6102645 baseEnd_6102645 := by
    simpa [prefixWord, tailWord_6102645, baseEnd_6102645] using wordTrace_append hprefix tailTrace_6102645
  have hstable : (prefixWord ++ tailWord_6102645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102645).length < 2 ^ (prefixWord ++ tailWord_6102645).sum := by decide
  have hdescent : baseEnd_6102645 < baseStart_6102645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102651 : List Nat := [1, 1, 1, 1, 1, 4, 5, 1, 4, 2, 2]
def baseStart_6102651 : Nat := 118140960795 + 6102651 * 2 ^ 59
def prefixEnd_6102651 : Nat := 4983230072969 + 3 ^ 40 * 6102651 * 2
def baseEnd_6102651 : Nat := 3133593229641308083596925

theorem tailTrace_6102651 : CollatzResearch.WordTrace tailWord_6102651 prefixEnd_6102651 3133593229641308083596925 := by
  unfold tailWord_6102651
  simp only [CollatzResearch.WordTrace]
  refine ⟨222581967814145151658163807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148387978542763434438775871 222581967814145151658163807)
  ·
    refine ⟨333872951721217727487245711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222581967814145151658163807 333872951721217727487245711)
    ·
      refine ⟨500809427581826591230868567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333872951721217727487245711 500809427581826591230868567)
      ·
        refine ⟨751214141372739886846302851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500809427581826591230868567 751214141372739886846302851)
        ·
          refine ⟨1126821212059109830269454277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751214141372739886846302851 1126821212059109830269454277)
          ·
            refine ⟨211278977261083093175522677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1126821212059109830269454277 211278977261083093175522677)
            ·
              refine ⟨19807404118226539985205251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 211278977261083093175522677 19807404118226539985205251)
              ·
                refine ⟨29711106177339809977807877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19807404118226539985205251 29711106177339809977807877)
                ·
                  refine ⟨5570832408251214370838977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29711106177339809977807877 5570832408251214370838977)
                  ·
                    refine ⟨4178124306188410778129233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5570832408251214370838977 4178124306188410778129233)
                    ·
                      refine ⟨3133593229641308083596925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4178124306188410778129233 3133593229641308083596925)
                      ·
                        rfl

theorem cell23_6102651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 2, 2].length) (baseStart_6102651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102651 prefixEnd_6102651 := by exact prefixLift 6102651
  have htrace : WordTrace (prefixWord ++ tailWord_6102651) baseStart_6102651 baseEnd_6102651 := by
    simpa [prefixWord, tailWord_6102651, baseEnd_6102651] using wordTrace_append hprefix tailTrace_6102651
  have hstable : (prefixWord ++ tailWord_6102651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102651).length < 2 ^ (prefixWord ++ tailWord_6102651).sum := by decide
  have hdescent : baseEnd_6102651 < baseStart_6102651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102714 : List Nat := [3, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5]
def baseStart_6102714 : Nat := 118140960795 + 6102714 * 2 ^ 59
def prefixEnd_6102714 : Nat := 4983230072969 + 3 ^ 40 * 6102714 * 2
def baseEnd_6102714 : Nat := 3133625578922541337109135

theorem tailTrace_6102714 : CollatzResearch.WordTrace tailWord_6102714 prefixEnd_6102714 3133625578922541337109135 := by
  unfold tailWord_6102714
  simp only [CollatzResearch.WordTrace]
  refine ⟨55646066403229228354426799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148389510408611275611804797 55646066403229228354426799)
  ·
    refine ⟨83469099604843842531640199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55646066403229228354426799 83469099604843842531640199)
    ·
      refine ⟨125203649407265763797460299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83469099604843842531640199 125203649407265763797460299)
      ·
        refine ⟨187805474110898645696190449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125203649407265763797460299 187805474110898645696190449)
        ·
          refine ⟨140854105583173984272142837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187805474110898645696190449 140854105583173984272142837)
          ·
            refine ⟨13205072398422561025513391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140854105583173984272142837 13205072398422561025513391)
            ·
              refine ⟨19807608597633841538270087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13205072398422561025513391 19807608597633841538270087)
              ·
                refine ⟨29711412896450762307405131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19807608597633841538270087 29711412896450762307405131)
                ·
                  refine ⟨44567119344676143461107697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29711412896450762307405131 44567119344676143461107697)
                  ·
                    refine ⟨33425339508507107595830773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44567119344676143461107697 33425339508507107595830773)
                    ·
                      refine ⟨3133625578922541337109135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33425339508507107595830773 3133625578922541337109135)
                      ·
                        rfl

theorem cell23_6102714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_6102714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102714 prefixEnd_6102714 := by exact prefixLift 6102714
  have htrace : WordTrace (prefixWord ++ tailWord_6102714) baseStart_6102714 baseEnd_6102714 := by
    simpa [prefixWord, tailWord_6102714, baseEnd_6102714] using wordTrace_append hprefix tailTrace_6102714
  have hstable : (prefixWord ++ tailWord_6102714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102714).length < 2 ^ (prefixWord ++ tailWord_6102714).sum := by decide
  have hdescent : baseEnd_6102714 < baseStart_6102714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102764 : List Nat := [2, 2, 1, 1, 2, 2, 3, 4, 6]
def baseStart_6102764 : Nat := 118140960795 + 6102764 * 2 ^ 59
def prefixEnd_6102764 : Nat := 4983230072969 + 3 ^ 40 * 6102764 * 2
def baseEnd_6102764 : Nat := 348183472550585126831545

theorem tailTrace_6102764 : CollatzResearch.WordTrace tailWord_6102764 prefixEnd_6102764 348183472550585126831545 := by
  unfold tailWord_6102764
  simp only [CollatzResearch.WordTrace]
  refine ⟨111293044631367885978513673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148390726175157181304684897 111293044631367885978513673)
  ·
    refine ⟨83469783473525914483885255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111293044631367885978513673 83469783473525914483885255)
    ·
      refine ⟨125204675210288871725827883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83469783473525914483885255 125204675210288871725827883)
      ·
        refine ⟨187807012815433307588741825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125204675210288871725827883 187807012815433307588741825)
        ·
          refine ⟨140855259611574980691556369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187807012815433307588741825 140855259611574980691556369)
          ·
            refine ⟨105641444708681235518667277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140855259611574980691556369 105641444708681235518667277)
            ·
              refine ⟨39615541765755463319500229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105641444708681235518667277 39615541765755463319500229)
              ·
                refine ⟨7427914081079149372406293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39615541765755463319500229 7427914081079149372406293)
                ·
                  refine ⟨348183472550585126831545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7427914081079149372406293 348183472550585126831545)
                  ·
                    rfl

theorem cell23_6102764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 6].length) (baseStart_6102764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102764 prefixEnd_6102764 := by exact prefixLift 6102764
  have htrace : WordTrace (prefixWord ++ tailWord_6102764) baseStart_6102764 baseEnd_6102764 := by
    simpa [prefixWord, tailWord_6102764, baseEnd_6102764] using wordTrace_append hprefix tailTrace_6102764
  have hstable : (prefixWord ++ tailWord_6102764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102764).length < 2 ^ (prefixWord ++ tailWord_6102764).sum := by decide
  have hdescent : baseEnd_6102764 < baseStart_6102764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102802 : List Nat := [3, 2, 4, 1, 1, 2, 2, 3, 1, 4]
def baseStart_6102802 : Nat := 118140960795 + 6102802 * 2 ^ 59
def prefixEnd_6102802 : Nat := 4983230072969 + 3 ^ 40 * 6102802 * 2
def baseEnd_6102802 : Nat := 1044556921740045664269577

theorem tailTrace_6102802 : CollatzResearch.WordTrace tailWord_6102802 prefixEnd_6102802 1044556921740045664269577 := by
  unfold tailWord_6102802
  simp only [CollatzResearch.WordTrace]
  refine ⟨55646868809149526111727665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148391650157732069631273773 55646868809149526111727665)
  ·
    refine ⟨41735151606862144583795749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55646868809149526111727665 41735151606862144583795749)
    ·
      refine ⟨7825340926286652109461703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41735151606862144583795749 7825340926286652109461703)
      ·
        refine ⟨11738011389429978164192555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7825340926286652109461703 11738011389429978164192555)
        ·
          refine ⟨17607017084144967246288833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11738011389429978164192555 17607017084144967246288833)
          ·
            refine ⟨13205262813108725434716625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17607017084144967246288833 13205262813108725434716625)
            ·
              refine ⟨9903947109831544076037469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13205262813108725434716625 9903947109831544076037469)
              ·
                refine ⟨3713980166186829028514051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9903947109831544076037469 3713980166186829028514051)
                ·
                  refine ⟨5570970249280243542771077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3713980166186829028514051 5570970249280243542771077)
                  ·
                    refine ⟨1044556921740045664269577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5570970249280243542771077 1044556921740045664269577)
                    ·
                      rfl

theorem cell23_6102802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_6102802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102802 prefixEnd_6102802 := by exact prefixLift 6102802
  have htrace : WordTrace (prefixWord ++ tailWord_6102802) baseStart_6102802 baseEnd_6102802 := by
    simpa [prefixWord, tailWord_6102802, baseEnd_6102802] using wordTrace_append hprefix tailTrace_6102802
  have hstable : (prefixWord ++ tailWord_6102802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102802).length < 2 ^ (prefixWord ++ tailWord_6102802).sum := by decide
  have hdescent : baseEnd_6102802 < baseStart_6102802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102818 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 4, 3, 2]
def baseStart_6102818 : Nat := 118140960795 + 6102818 * 2 ^ 59
def prefixEnd_6102818 : Nat := 4983230072969 + 3 ^ 40 * 6102818 * 2
def baseEnd_6102818 : Nat := 3133678980910608930208657

theorem tailTrace_6102818 : CollatzResearch.WordTrace tailWord_6102818 prefixEnd_6102818 3133678980910608930208657 := by
  unfold tailWord_6102818
  simp only [CollatzResearch.WordTrace]
  refine ⟨55647014701135034794873277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148392039203026759452995405 55647014701135034794873277)
  ·
    refine ⟨20867630512925638048077479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55647014701135034794873277 20867630512925638048077479)
    ·
      refine ⟨31301445769388457072116219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20867630512925638048077479 31301445769388457072116219)
      ·
        refine ⟨46952168654082685608174329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31301445769388457072116219 46952168654082685608174329)
        ·
          refine ⟨35214126490562014206130747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46952168654082685608174329 35214126490562014206130747)
          ·
            refine ⟨52821189735843021309196121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35214126490562014206130747 52821189735843021309196121)
            ·
              refine ⟨39615892301882265981897091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52821189735843021309196121 39615892301882265981897091)
              ·
                refine ⟨59423838452823398972845637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39615892301882265981897091 59423838452823398972845637)
                ·
                  refine ⟨11141969709904387307408557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59423838452823398972845637 11141969709904387307408557)
                  ·
                    refine ⟨4178238641214145240278209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11141969709904387307408557 4178238641214145240278209)
                    ·
                      refine ⟨3133678980910608930208657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4178238641214145240278209 3133678980910608930208657)
                      ·
                        rfl

theorem cell23_6102818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_6102818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102818 prefixEnd_6102818 := by exact prefixLift 6102818
  have htrace : WordTrace (prefixWord ++ tailWord_6102818) baseStart_6102818 baseEnd_6102818 := by
    simpa [prefixWord, tailWord_6102818, baseEnd_6102818] using wordTrace_append hprefix tailTrace_6102818
  have hstable : (prefixWord ++ tailWord_6102818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102818).length < 2 ^ (prefixWord ++ tailWord_6102818).sum := by decide
  have hdescent : baseEnd_6102818 < baseStart_6102818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102868 : List Nat := [2, 4, 1, 1, 3, 2, 2, 1, 1, 1, 5]
def baseStart_6102868 : Nat := 118140960795 + 6102868 * 2 ^ 59
def prefixEnd_6102868 : Nat := 4983230072969 + 3 ^ 40 * 6102868 * 2
def baseEnd_6102868 : Nat := 3133704654943333734583427

theorem tailTrace_6102868 : CollatzResearch.WordTrace tailWord_6102868 prefixEnd_6102868 3133704654943333734583427 := by
  unfold tailWord_6102868
  simp only [CollatzResearch.WordTrace]
  refine ⟨111294941227179498859406629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148393254969572665145875505 111294941227179498859406629)
  ·
    refine ⟨20867801480096156036138743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111294941227179498859406629 20867801480096156036138743)
    ·
      refine ⟨31301702220144234054208115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20867801480096156036138743 31301702220144234054208115)
      ·
        refine ⟨46952553330216351081312173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31301702220144234054208115 46952553330216351081312173)
        ·
          refine ⟨17607207498831131655492065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46952553330216351081312173 17607207498831131655492065)
          ·
            refine ⟨13205405624123348741619049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17607207498831131655492065 13205405624123348741619049)
            ·
              refine ⟨9904054218092511556214287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13205405624123348741619049 9904054218092511556214287)
              ·
                refine ⟨14856081327138767334321431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9904054218092511556214287 14856081327138767334321431)
                ·
                  refine ⟨22284121990708151001482147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14856081327138767334321431 22284121990708151001482147)
                  ·
                    refine ⟨33426182986062226502223221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22284121990708151001482147 33426182986062226502223221)
                    ·
                      refine ⟨3133704654943333734583427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33426182986062226502223221 3133704654943333734583427)
                      ·
                        rfl

theorem cell23_6102868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_6102868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102868 prefixEnd_6102868 := by exact prefixLift 6102868
  have htrace : WordTrace (prefixWord ++ tailWord_6102868) baseStart_6102868 baseEnd_6102868 := by
    simpa [prefixWord, tailWord_6102868, baseEnd_6102868] using wordTrace_append hprefix tailTrace_6102868
  have hstable : (prefixWord ++ tailWord_6102868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102868).length < 2 ^ (prefixWord ++ tailWord_6102868).sum := by decide
  have hdescent : baseEnd_6102868 < baseStart_6102868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102871 : List Nat := [1, 1, 3, 2, 5, 2, 9]
def baseStart_6102871 : Nat := 118140960795 + 6102871 * 2 ^ 59
def prefixEnd_6102871 : Nat := 4983230072969 + 3 ^ 40 * 6102871 * 2
def baseEnd_6102871 : Nat := 38687730807225891640073

theorem tailTrace_6102871 : CollatzResearch.WordTrace tailWord_6102871 prefixEnd_6102871 38687730807225891640073 := by
  unfold tailWord_6102871
  simp only [CollatzResearch.WordTrace]
  refine ⟨222589991873348129231172467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148393327915565419487448311 222589991873348129231172467)
  ·
    refine ⟨333884987810022193846758701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222589991873348129231172467 333884987810022193846758701)
    ·
      refine ⟨125206870428758322692534513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333884987810022193846758701 125206870428758322692534513)
      ·
        refine ⟨93905152821568742019400885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125206870428758322692534513 93905152821568742019400885)
        ·
          refine ⟨8803608077022069564318833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93905152821568742019400885 8803608077022069564318833)
          ·
            refine ⟨6602706057766552173239125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8803608077022069564318833 6602706057766552173239125)
            ·
              refine ⟨38687730807225891640073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6602706057766552173239125 38687730807225891640073)
              ·
                rfl

theorem cell23_6102871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 9].length) (baseStart_6102871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102871 prefixEnd_6102871 := by exact prefixLift 6102871
  have htrace : WordTrace (prefixWord ++ tailWord_6102871) baseStart_6102871 baseEnd_6102871 := by
    simpa [prefixWord, tailWord_6102871, baseEnd_6102871] using wordTrace_append hprefix tailTrace_6102871
  have hstable : (prefixWord ++ tailWord_6102871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102871).length < 2 ^ (prefixWord ++ tailWord_6102871).sum := by decide
  have hdescent : baseEnd_6102871 < baseStart_6102871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102882 : List Nat := [3, 3, 2, 1, 2, 1, 3, 1, 3, 2, 2]
def baseStart_6102882 : Nat := 118140960795 + 6102882 * 2 ^ 59
def prefixEnd_6102882 : Nat := 4983230072969 + 3 ^ 40 * 6102882 * 2
def baseEnd_6102882 : Nat := 3133711843672496679808363

theorem tailTrace_6102882 : CollatzResearch.WordTrace tailWord_6102882 prefixEnd_6102882 3133711843672496679808363 := by
  unfold tailWord_6102882
  simp only [CollatzResearch.WordTrace]
  refine ⟨55647598269077069527455725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148393595384205518739881933 55647598269077069527455725)
  ·
    refine ⟨20867849350903901072795897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55647598269077069527455725 20867849350903901072795897)
    ·
      refine ⟨15650887013177925804596923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20867849350903901072795897 15650887013177925804596923)
      ·
        refine ⟨23476330519766888706895385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15650887013177925804596923 23476330519766888706895385)
        ·
          refine ⟨17607247889825166530171539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23476330519766888706895385 17607247889825166530171539)
          ·
            refine ⟨26410871834737749795257309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17607247889825166530171539 26410871834737749795257309)
            ·
              refine ⟨9904076938026656173221491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26410871834737749795257309 9904076938026656173221491)
              ·
                refine ⟨14856115407039984259832237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9904076938026656173221491 14856115407039984259832237)
                ·
                  refine ⟨5571043277639994097437089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14856115407039984259832237 5571043277639994097437089)
                  ·
                    refine ⟨4178282458229995573077817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5571043277639994097437089 4178282458229995573077817)
                    ·
                      refine ⟨3133711843672496679808363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4178282458229995573077817 3133711843672496679808363)
                      ·
                        rfl

theorem cell23_6102882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_6102882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102882 prefixEnd_6102882 := by exact prefixLift 6102882
  have htrace : WordTrace (prefixWord ++ tailWord_6102882) baseStart_6102882 baseEnd_6102882 := by
    simpa [prefixWord, tailWord_6102882, baseEnd_6102882] using wordTrace_append hprefix tailTrace_6102882
  have hstable : (prefixWord ++ tailWord_6102882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102882).length < 2 ^ (prefixWord ++ tailWord_6102882).sum := by decide
  have hdescent : baseEnd_6102882 < baseStart_6102882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102891 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 2, 7, 2]
def baseStart_6102891 : Nat := 118140960795 + 6102891 * 2 ^ 59
def prefixEnd_6102891 : Nat := 4983230072969 + 3 ^ 40 * 6102891 * 2
def baseEnd_6102891 : Nat := 3133716464998387144595821

theorem tailTrace_6102891 : CollatzResearch.WordTrace tailWord_6102891 prefixEnd_6102891 3133716464998387144595821 := by
  unfold tailWord_6102891
  simp only [CollatzResearch.WordTrace]
  refine ⟨222590721333275672646900527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148393814222183781764600351 222590721333275672646900527)
  ·
    refine ⟨333886081999913508970350791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222590721333275672646900527 333886081999913508970350791)
    ·
      refine ⟨500829122999870263455526187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333886081999913508970350791 500829122999870263455526187)
      ·
        refine ⟨751243684499805395183289281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500829122999870263455526187 751243684499805395183289281)
        ·
          refine ⟨563432763374854046387466961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 751243684499805395183289281 563432763374854046387466961)
          ·
            refine ⟨422574572531140534790600221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 563432763374854046387466961 422574572531140534790600221)
            ·
              refine ⟨158465464699177700546475083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 422574572531140534790600221 158465464699177700546475083)
              ·
                refine ⟨237698197048766550819712625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158465464699177700546475083 237698197048766550819712625)
                ·
                  refine ⟨178273647786574913114784469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237698197048766550819712625 178273647786574913114784469)
                  ·
                    refine ⟨4178288619997849526127761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 178273647786574913114784469 4178288619997849526127761)
                    ·
                      refine ⟨3133716464998387144595821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4178288619997849526127761 3133716464998387144595821)
                      ·
                        rfl

theorem cell23_6102891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 7, 2].length) (baseStart_6102891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102891 prefixEnd_6102891 := by exact prefixLift 6102891
  have htrace : WordTrace (prefixWord ++ tailWord_6102891) baseStart_6102891 baseEnd_6102891 := by
    simpa [prefixWord, tailWord_6102891, baseEnd_6102891] using wordTrace_append hprefix tailTrace_6102891
  have hstable : (prefixWord ++ tailWord_6102891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102891).length < 2 ^ (prefixWord ++ tailWord_6102891).sum := by decide
  have hdescent : baseEnd_6102891 < baseStart_6102891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102932 : List Nat := [2, 4, 2, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_6102932 : Nat := 118140960795 + 6102932 * 2 ^ 59
def prefixEnd_6102932 : Nat := 4983230072969 + 3 ^ 40 * 6102932 * 2
def baseEnd_6102932 : Nat := 3133737517705221484183133

theorem tailTrace_6102932 : CollatzResearch.WordTrace tailWord_6102932 prefixEnd_6102932 3133737517705221484183133 := by
  unfold tailWord_6102932
  simp only [CollatzResearch.WordTrace]
  refine ⟨111296108363063568324571525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148394811150751424432762033 111296108363063568324571525)
  ·
    refine ⟨20868020318074419060857161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111296108363063568324571525 20868020318074419060857161)
    ·
      refine ⟨15651015238555814295642871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20868020318074419060857161 15651015238555814295642871)
      ·
        refine ⟨23476522857833721443464307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15651015238555814295642871 23476522857833721443464307)
        ·
          refine ⟨35214784286750582165196461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23476522857833721443464307 35214784286750582165196461)
          ·
            refine ⟨13205544107531468311948673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35214784286750582165196461 13205544107531468311948673)
            ·
              refine ⟨9904158080648601233961505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13205544107531468311948673 9904158080648601233961505)
              ·
                refine ⟨7428118560486450925471129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9904158080648601233961505 7428118560486450925471129)
                ·
                  refine ⟨5571088920364838194103347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7428118560486450925471129 5571088920364838194103347)
                  ·
                    refine ⟨8356633380547257291155021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5571088920364838194103347 8356633380547257291155021)
                    ·
                      refine ⟨3133737517705221484183133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8356633380547257291155021 3133737517705221484183133)
                      ·
                        rfl

theorem cell23_6102932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_6102932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102932 prefixEnd_6102932 := by exact prefixLift 6102932
  have htrace : WordTrace (prefixWord ++ tailWord_6102932) baseStart_6102932 baseEnd_6102932 := by
    simpa [prefixWord, tailWord_6102932, baseEnd_6102932] using wordTrace_append hprefix tailTrace_6102932
  have hstable : (prefixWord ++ tailWord_6102932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102932).length < 2 ^ (prefixWord ++ tailWord_6102932).sum := by decide
  have hdescent : baseEnd_6102932 < baseStart_6102932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102961 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 9]
def baseStart_6102961 : Nat := 118140960795 + 6102961 * 2 ^ 59
def prefixEnd_6102961 : Nat := 4983230072969 + 3 ^ 40 * 6102961 * 2
def baseEnd_6102961 : Nat := 348194712071577985635611

theorem tailTrace_6102961 : CollatzResearch.WordTrace tailWord_6102961 prefixEnd_6102961 348194712071577985635611 := by
  unfold tailWord_6102961
  simp only [CollatzResearch.WordTrace]
  refine ⟨222593274443022074601948737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148395516295348049734632491 222593274443022074601948737)
  ·
    refine ⟨166944955832266555951461553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222593274443022074601948737 166944955832266555951461553)
    ·
      refine ⟨125208716874199916963596165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166944955832266555951461553 125208716874199916963596165)
      ·
        refine ⟨23476634413912484430674281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125208716874199916963596165 23476634413912484430674281)
        ·
          refine ⟨17607475810434363323005711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23476634413912484430674281 17607475810434363323005711)
          ·
            refine ⟨26411213715651544984508567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17607475810434363323005711 26411213715651544984508567)
            ·
              refine ⟨39616820573477317476762851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26411213715651544984508567 39616820573477317476762851)
              ·
                refine ⟨59425230860215976215144277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39616820573477317476762851 59425230860215976215144277)
                ·
                  refine ⟨348194712071577985635611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59425230860215976215144277 348194712071577985635611)
                  ·
                    rfl

theorem cell23_6102961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 9].length) (baseStart_6102961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102961 prefixEnd_6102961 := by exact prefixLift 6102961
  have htrace : WordTrace (prefixWord ++ tailWord_6102961) baseStart_6102961 baseEnd_6102961 := by
    simpa [prefixWord, tailWord_6102961, baseEnd_6102961] using wordTrace_append hprefix tailTrace_6102961
  have hstable : (prefixWord ++ tailWord_6102961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102961).length < 2 ^ (prefixWord ++ tailWord_6102961).sum := by decide
  have hdescent : baseEnd_6102961 < baseStart_6102961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102971 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 3]
def baseStart_6102971 : Nat := 118140960795 + 6102971 * 2 ^ 59
def prefixEnd_6102971 : Nat := 4983230072969 + 3 ^ 40 * 6102971 * 2
def baseEnd_6102971 : Nat := 3133757543450746831595453

theorem tailTrace_6102971 : CollatzResearch.WordTrace tailWord_6102971 prefixEnd_6102971 3133757543450746831595453 := by
  unfold tailWord_6102971
  simp only [CollatzResearch.WordTrace]
  refine ⟨222593639172985846309812767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148395759448657230873208511 222593639172985846309812767)
  ·
    refine ⟨333890458759478769464719151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222593639172985846309812767 333890458759478769464719151)
    ·
      refine ⟨500835688139218154197078727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333890458759478769464719151 500835688139218154197078727)
      ·
        refine ⟨751253532208827231295618091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500835688139218154197078727 751253532208827231295618091)
        ·
          refine ⟨1126880298313240846943427137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751253532208827231295618091 1126880298313240846943427137)
          ·
            refine ⟨845160223734930635207570353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1126880298313240846943427137 845160223734930635207570353)
            ·
              refine ⟨633870167801197976405677765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 845160223734930635207570353 633870167801197976405677765)
              ·
                refine ⟨118850656462724620576064581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 633870167801197976405677765 118850656462724620576064581)
                ·
                  refine ⟨22284498086760866358012109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118850656462724620576064581 22284498086760866358012109)
                  ·
                    refine ⟨8356686782535324884254541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22284498086760866358012109 8356686782535324884254541)
                    ·
                      refine ⟨3133757543450746831595453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8356686782535324884254541 3133757543450746831595453)
                      ·
                        rfl

theorem cell23_6102971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 3].length) (baseStart_6102971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102971 prefixEnd_6102971 := by exact prefixLift 6102971
  have htrace : WordTrace (prefixWord ++ tailWord_6102971) baseStart_6102971 baseEnd_6102971 := by
    simpa [prefixWord, tailWord_6102971, baseEnd_6102971] using wordTrace_append hprefix tailTrace_6102971
  have hstable : (prefixWord ++ tailWord_6102971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102971).length < 2 ^ (prefixWord ++ tailWord_6102971).sum := by decide
  have hdescent : baseEnd_6102971 < baseStart_6102971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102988 : List Nat := [2, 2, 1, 4, 1, 2, 1, 2, 2, 3, 3]
def baseStart_6102988 : Nat := 118140960795 + 6102988 * 2 ^ 59
def prefixEnd_6102988 : Nat := 4983230072969 + 3 ^ 40 * 6102988 * 2
def baseEnd_6102988 : Nat := 3133766272621873265082875

theorem tailTrace_6102988 : CollatzResearch.WordTrace tailWord_6102988 prefixEnd_6102988 3133766272621873265082875 := by
  unfold tailWord_6102988
  simp only [CollatzResearch.WordTrace]
  refine ⟨111297129606962129106590809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148396172809282838808787745 111297129606962129106590809)
  ·
    refine ⟨83472847205221596829943107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111297129606962129106590809 83472847205221596829943107)
    ·
      refine ⟨125209270807832395244914661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83472847205221596829943107 125209270807832395244914661)
      ·
        refine ⟨23476738276468574108421499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125209270807832395244914661 23476738276468574108421499)
        ·
          refine ⟨35215107414702861162632249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23476738276468574108421499 35215107414702861162632249)
          ·
            refine ⟨26411330561027145871974187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35215107414702861162632249 26411330561027145871974187)
            ·
              refine ⟨39616995841540718807961281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26411330561027145871974187 39616995841540718807961281)
              ·
                refine ⟨29712746881155539105970961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39616995841540718807961281 29712746881155539105970961)
                ·
                  refine ⟨22284560160866654329478221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29712746881155539105970961 22284560160866654329478221)
                  ·
                    refine ⟨8356710060324995373554333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22284560160866654329478221 8356710060324995373554333)
                    ·
                      refine ⟨3133766272621873265082875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8356710060324995373554333 3133766272621873265082875)
                      ·
                        rfl

theorem cell23_6102988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_6102988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102988 prefixEnd_6102988 := by exact prefixLift 6102988
  have htrace : WordTrace (prefixWord ++ tailWord_6102988) baseStart_6102988 baseEnd_6102988 := by
    simpa [prefixWord, tailWord_6102988, baseEnd_6102988] using wordTrace_append hprefix tailTrace_6102988
  have hstable : (prefixWord ++ tailWord_6102988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102988).length < 2 ^ (prefixWord ++ tailWord_6102988).sum := by decide
  have hdescent : baseEnd_6102988 < baseStart_6102988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6102991 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 4, 5]
def baseStart_6102991 : Nat := 118140960795 + 6102991 * 2 ^ 59
def prefixEnd_6102991 : Nat := 4983230072969 + 3 ^ 40 * 6102991 * 2
def baseEnd_6102991 : Nat := 1044589271021278917781787

theorem tailTrace_6102991 : CollatzResearch.WordTrace tailWord_6102991 prefixEnd_6102991 1044589271021278917781787 := by
  unfold tailWord_6102991
  simp only [CollatzResearch.WordTrace]
  refine ⟨222594368632913389725540827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148396245755275593150360551 222594368632913389725540827)
  ·
    refine ⟨333891552949370084588311241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222594368632913389725540827 333891552949370084588311241)
    ·
      refine ⟨250418664712027563441233431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333891552949370084588311241 250418664712027563441233431)
      ·
        refine ⟨375627997068041345161850147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250418664712027563441233431 375627997068041345161850147)
        ·
          refine ⟨563441995602062017742775221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375627997068041345161850147 563441995602062017742775221)
          ·
            refine ⟨52822687087693314163385177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 563441995602062017742775221 52822687087693314163385177)
            ·
              refine ⟨39617015315769985622538883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52822687087693314163385177 39617015315769985622538883)
              ·
                refine ⟨59425522973654978433808325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39617015315769985622538883 59425522973654978433808325)
                ·
                  refine ⟨11142285557560308456339061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59425522973654978433808325 11142285557560308456339061)
                  ·
                    refine ⟨1044589271021278917781787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11142285557560308456339061 1044589271021278917781787)
                    ·
                      rfl

theorem cell23_6102991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 5].length) (baseStart_6102991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6102991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6102991 prefixEnd_6102991 := by exact prefixLift 6102991
  have htrace : WordTrace (prefixWord ++ tailWord_6102991) baseStart_6102991 baseEnd_6102991 := by
    simpa [prefixWord, tailWord_6102991, baseEnd_6102991] using wordTrace_append hprefix tailTrace_6102991
  have hstable : (prefixWord ++ tailWord_6102991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6102991).length < 2 ^ (prefixWord ++ tailWord_6102991).sum := by decide
  have hdescent : baseEnd_6102991 < baseStart_6102991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6102991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103046 : List Nat := [6, 2, 1, 2, 1, 2, 1, 1, 7]
def baseStart_6103046 : Nat := 118140960795 + 6103046 * 2 ^ 59
def prefixEnd_6103046 : Nat := 4983230072969 + 3 ^ 40 * 6103046 * 2
def baseEnd_6103046 : Nat := 348199561611092670906401

theorem tailTrace_6103046 : CollatzResearch.WordTrace tailWord_6103046 prefixEnd_6103046 348199561611092670906401 := by
  unfold tailWord_6103046
  simp only [CollatzResearch.WordTrace]
  refine ⟨6956136707741066691212281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 148397583098476089412528661 6956136707741066691212281)
  ·
    refine ⟨5217102530805800018409211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6956136707741066691212281 5217102530805800018409211)
    ·
      refine ⟨7825653796208700027613817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5217102530805800018409211 7825653796208700027613817)
      ·
        refine ⟨5869240347156525020710363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7825653796208700027613817 5869240347156525020710363)
        ·
          refine ⟨8803860520734787531065545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5869240347156525020710363 8803860520734787531065545)
          ·
            refine ⟨6602895390551090648299159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8803860520734787531065545 6602895390551090648299159)
            ·
              refine ⟨9904343085826635972448739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6602895390551090648299159 9904343085826635972448739)
              ·
                refine ⟨14856514628739953958673109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9904343085826635972448739 14856514628739953958673109)
                ·
                  refine ⟨348199561611092670906401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14856514628739953958673109 348199561611092670906401)
                  ·
                    rfl

theorem cell23_6103046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_6103046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103046 prefixEnd_6103046 := by exact prefixLift 6103046
  have htrace : WordTrace (prefixWord ++ tailWord_6103046) baseStart_6103046 baseEnd_6103046 := by
    simpa [prefixWord, tailWord_6103046, baseEnd_6103046] using wordTrace_append hprefix tailTrace_6103046
  have hstable : (prefixWord ++ tailWord_6103046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103046).length < 2 ^ (prefixWord ++ tailWord_6103046).sum := by decide
  have hdescent : baseEnd_6103046 < baseStart_6103046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103051 : List Nat := [1, 1, 1, 1, 6, 1, 1, 3, 8]
def baseStart_6103051 : Nat := 118140960795 + 6103051 * 2 ^ 59
def prefixEnd_6103051 : Nat := 4983230072969 + 3 ^ 40 * 6103051 * 2
def baseEnd_6103051 : Nat := 348199846878122946510565

theorem tailTrace_6103051 : CollatzResearch.WordTrace tailWord_6103051 prefixEnd_6103051 348199846878122946510565 := by
  unfold tailWord_6103051
  simp only [CollatzResearch.WordTrace]
  refine ⟨222596557012696019972725007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148397704675130679981816671 222596557012696019972725007)
  ·
    refine ⟨333894835519044029959087511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222596557012696019972725007 333894835519044029959087511)
    ·
      refine ⟨500842253278566044938631267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333894835519044029959087511 500842253278566044938631267)
      ·
        refine ⟨751263379917849067407946901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500842253278566044938631267 751263379917849067407946901)
        ·
          refine ⟨35215470933649175034747511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 751263379917849067407946901 35215470933649175034747511)
          ·
            refine ⟨52823206400473762552121267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35215470933649175034747511 52823206400473762552121267)
            ·
              refine ⟨79234809600710643828181901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52823206400473762552121267 79234809600710643828181901)
              ·
                refine ⟨29713053600266491435568213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79234809600710643828181901 29713053600266491435568213)
                ·
                  refine ⟨348199846878122946510565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29713053600266491435568213 348199846878122946510565)
                  ·
                    rfl

theorem cell23_6103051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 8].length) (baseStart_6103051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103051 prefixEnd_6103051 := by exact prefixLift 6103051
  have htrace : WordTrace (prefixWord ++ tailWord_6103051) baseStart_6103051 baseEnd_6103051 := by
    simpa [prefixWord, tailWord_6103051, baseEnd_6103051] using wordTrace_append hprefix tailTrace_6103051
  have hstable : (prefixWord ++ tailWord_6103051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103051).length < 2 ^ (prefixWord ++ tailWord_6103051).sum := by decide
  have hdescent : baseEnd_6103051 < baseStart_6103051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103082 : List Nat := [3, 1, 4, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_6103082 : Nat := 118140960795 + 6103082 * 2 ^ 59
def prefixEnd_6103082 : Nat := 4983230072969 + 3 ^ 40 * 6103082 * 2
def baseEnd_6103082 : Nat := 3133814539803395897307443

theorem tailTrace_6103082 : CollatzResearch.WordTrace tailWord_6103082 prefixEnd_6103082 3133814539803395897307443 := by
  unfold tailWord_6103082
  simp only [CollatzResearch.WordTrace]
  refine ⟨55649421918895928066775875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148398458450389141511402333 55649421918895928066775875)
  ·
    refine ⟨83474132878343892100163813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55649421918895928066775875 83474132878343892100163813)
    ·
      refine ⟨15651399914689479768780715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83474132878343892100163813 15651399914689479768780715)
      ·
        refine ⟨23477099872034219653171073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15651399914689479768780715 23477099872034219653171073)
        ·
          refine ⟨17607824904025664739878305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23477099872034219653171073 17607824904025664739878305)
          ·
            refine ⟨13205868678019248554908729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17607824904025664739878305 13205868678019248554908729)
            ·
              refine ⟨9904401508514436416181547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13205868678019248554908729 9904401508514436416181547)
              ·
                refine ⟨14856602262771654624272321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9904401508514436416181547 14856602262771654624272321)
                ·
                  refine ⟨11142451697078740968204241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14856602262771654624272321 11142451697078740968204241)
                  ·
                    refine ⟨8356838772809055726153181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11142451697078740968204241 8356838772809055726153181)
                    ·
                      refine ⟨3133814539803395897307443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8356838772809055726153181 3133814539803395897307443)
                      ·
                        rfl

theorem cell23_6103082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_6103082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103082 prefixEnd_6103082 := by exact prefixLift 6103082
  have htrace : WordTrace (prefixWord ++ tailWord_6103082) baseStart_6103082 baseEnd_6103082 := by
    simpa [prefixWord, tailWord_6103082, baseEnd_6103082] using wordTrace_append hprefix tailTrace_6103082
  have hstable : (prefixWord ++ tailWord_6103082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103082).length < 2 ^ (prefixWord ++ tailWord_6103082).sum := by decide
  have hdescent : baseEnd_6103082 < baseStart_6103082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103102 : List Nat := [4, 2, 1, 3, 2, 1, 2, 2, 6]
def baseStart_6103102 : Nat := 118140960795 + 6103102 * 2 ^ 59
def prefixEnd_6103102 : Nat := 4983230072969 + 3 ^ 40 * 6103102 * 2
def baseEnd_6103102 : Nat := 348202756601831757673039

theorem tailTrace_6103102 : CollatzResearch.WordTrace tailWord_6103102 prefixEnd_6103102 348202756601831757673039 := by
  unfold tailWord_6103102
  simp only [CollatzResearch.WordTrace]
  refine ⟨27824802141938906960353945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148398944757007503788554373 27824802141938906960353945)
  ·
    refine ⟨20868601606454180220265459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27824802141938906960353945 20868601606454180220265459)
    ·
      refine ⟨31302902409681270330398189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20868601606454180220265459 31302902409681270330398189)
      ·
        refine ⟨11738588403630476373899321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31302902409681270330398189 11738588403630476373899321)
        ·
          refine ⟨8803941302722857280424491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11738588403630476373899321 8803941302722857280424491)
          ·
            refine ⟨13205911954084285920636737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8803941302722857280424491 13205911954084285920636737)
            ·
              refine ⟨9904433965563214440477553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13205911954084285920636737 9904433965563214440477553)
              ·
                refine ⟨7428325474172410830358165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9904433965563214440477553 7428325474172410830358165)
                ·
                  refine ⟨348202756601831757673039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7428325474172410830358165 348202756601831757673039)
                  ·
                    rfl

theorem cell23_6103102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_6103102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103102 prefixEnd_6103102 := by exact prefixLift 6103102
  have htrace : WordTrace (prefixWord ++ tailWord_6103102) baseStart_6103102 baseEnd_6103102 := by
    simpa [prefixWord, tailWord_6103102, baseEnd_6103102] using wordTrace_append hprefix tailTrace_6103102
  have hstable : (prefixWord ++ tailWord_6103102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103102).length < 2 ^ (prefixWord ++ tailWord_6103102).sum := by decide
  have hdescent : baseEnd_6103102 < baseStart_6103102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103128 : List Nat := [2, 1, 2, 2, 1, 4, 1, 3, 1, 6]
def baseStart_6103128 : Nat := 118140960795 + 6103128 * 2 ^ 59
def prefixEnd_6103128 : Nat := 4983230072969 + 3 ^ 40 * 6103128 * 2
def baseEnd_6103128 : Nat := 1044612719971167572444077

theorem tailTrace_6103128 : CollatzResearch.WordTrace tailWord_6103128 prefixEnd_6103128 1044612719971167572444077 := by
  unfold tailWord_6103128
  simp only [CollatzResearch.WordTrace]
  refine ⟨111299682716708531061639019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148399576955611374748852025 111299682716708531061639019)
  ·
    refine ⟨166949524075062796592458529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111299682716708531061639019 166949524075062796592458529)
    ·
      refine ⟨125212143056297097444343897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166949524075062796592458529 125212143056297097444343897)
      ·
        refine ⟨93909107292222823083257923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125212143056297097444343897 93909107292222823083257923)
        ·
          refine ⟨140863660938334234624886885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93909107292222823083257923 140863660938334234624886885)
          ·
            refine ⟨26411936425937668992166291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140863660938334234624886885 26411936425937668992166291)
            ·
              refine ⟨39617904638906503488249437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26411936425937668992166291 39617904638906503488249437)
              ·
                refine ⟨14856714239589938808093539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39617904638906503488249437 14856714239589938808093539)
                ·
                  refine ⟨22285071359384908212140309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14856714239589938808093539 22285071359384908212140309)
                  ·
                    refine ⟨1044612719971167572444077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22285071359384908212140309 1044612719971167572444077)
                    ·
                      rfl

theorem cell23_6103128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 1, 6].length) (baseStart_6103128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103128 prefixEnd_6103128 := by exact prefixLift 6103128
  have htrace : WordTrace (prefixWord ++ tailWord_6103128) baseStart_6103128 baseEnd_6103128 := by
    simpa [prefixWord, tailWord_6103128, baseEnd_6103128] using wordTrace_append hprefix tailTrace_6103128
  have hstable : (prefixWord ++ tailWord_6103128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103128).length < 2 ^ (prefixWord ++ tailWord_6103128).sum := by decide
  have hdescent : baseEnd_6103128 < baseStart_6103128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103146 : List Nat := [3, 1, 3, 2, 3, 1, 2, 3, 1, 1, 3]
def baseStart_6103146 : Nat := 118140960795 + 6103146 * 2 ^ 59
def prefixEnd_6103146 : Nat := 4983230072969 + 3 ^ 40 * 6103146 * 2
def baseEnd_6103146 : Nat := 3133847402565283646907149

theorem tailTrace_6103146 : CollatzResearch.WordTrace tailWord_6103146 prefixEnd_6103146 3133847402565283646907149 := by
  unfold tailWord_6103146
  simp only [CollatzResearch.WordTrace]
  refine ⟨55650005486837962799358323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148400014631567900798288861 55650005486837962799358323)
  ·
    refine ⟨83475008230256944199037485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55650005486837962799358323 83475008230256944199037485)
    ·
      refine ⟨31303128086346354074639057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83475008230256944199037485 31303128086346354074639057)
      ·
        refine ⟨23477346064759765555979293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31303128086346354074639057 23477346064759765555979293)
        ·
          refine ⟨8804004774284912083492235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23477346064759765555979293 8804004774284912083492235)
          ·
            refine ⟨13206007161427368125238353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8804004774284912083492235 13206007161427368125238353)
            ·
              refine ⟨9904505371070526093928765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13206007161427368125238353 9904505371070526093928765)
              ·
                refine ⟨3714189514151447285223287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9904505371070526093928765 3714189514151447285223287)
                ·
                  refine ⟨5571284271227170927834931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3714189514151447285223287 5571284271227170927834931)
                  ·
                    refine ⟨8356926406840756391752397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5571284271227170927834931 8356926406840756391752397)
                    ·
                      refine ⟨3133847402565283646907149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8356926406840756391752397 3133847402565283646907149)
                      ·
                        rfl

theorem cell23_6103146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_6103146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103146 prefixEnd_6103146 := by exact prefixLift 6103146
  have htrace : WordTrace (prefixWord ++ tailWord_6103146) baseStart_6103146 baseEnd_6103146 := by
    simpa [prefixWord, tailWord_6103146, baseEnd_6103146] using wordTrace_append hprefix tailTrace_6103146
  have hstable : (prefixWord ++ tailWord_6103146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103146).length < 2 ^ (prefixWord ++ tailWord_6103146).sum := by decide
  have hdescent : baseEnd_6103146 < baseStart_6103146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103152 : List Nat := [2, 1, 1, 1, 5, 2, 4, 1, 1, 1, 4]
def baseStart_6103152 : Nat := 118140960795 + 6103152 * 2 ^ 59
def prefixEnd_6103152 : Nat := 4983230072969 + 3 ^ 40 * 6103152 * 2
def baseEnd_6103152 : Nat := 3133850483449210623432121

theorem tailTrace_6103152 : CollatzResearch.WordTrace tailWord_6103152 prefixEnd_6103152 3133850483449210623432121 := by
  unfold tailWord_6103152
  simp only [CollatzResearch.WordTrace]
  refine ⟨111300120392665057111075855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148400160523553409481434473 111300120392665057111075855)
  ·
    refine ⟨166950180588997585666613783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111300120392665057111075855 166950180588997585666613783)
    ·
      refine ⟨250425270883496378499920675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166950180588997585666613783 250425270883496378499920675)
      ·
        refine ⟨375637906325244567749881013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250425270883496378499920675 375637906325244567749881013)
        ·
          refine ⟨35216053717991678226551345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 375637906325244567749881013 35216053717991678226551345)
          ·
            refine ⟨26412040288493758669913509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35216053717991678226551345 26412040288493758669913509)
            ·
              refine ⟨4952257554092579750608783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26412040288493758669913509 4952257554092579750608783)
              ·
                refine ⟨7428386331138869625913175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4952257554092579750608783 7428386331138869625913175)
                ·
                  refine ⟨11142579496708304438869763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7428386331138869625913175 11142579496708304438869763)
                  ·
                    refine ⟨16713869245062456658304645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11142579496708304438869763 16713869245062456658304645)
                    ·
                      refine ⟨3133850483449210623432121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16713869245062456658304645 3133850483449210623432121)
                      ·
                        rfl

theorem cell23_6103152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 1, 1, 4].length) (baseStart_6103152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103152 prefixEnd_6103152 := by exact prefixLift 6103152
  have htrace : WordTrace (prefixWord ++ tailWord_6103152) baseStart_6103152 baseEnd_6103152 := by
    simpa [prefixWord, tailWord_6103152, baseEnd_6103152] using wordTrace_append hprefix tailTrace_6103152
  have hstable : (prefixWord ++ tailWord_6103152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103152).length < 2 ^ (prefixWord ++ tailWord_6103152).sum := by decide
  have hdescent : baseEnd_6103152 < baseStart_6103152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103192 : List Nat := [2, 1, 2, 4, 3, 2, 2, 7]
def baseStart_6103192 : Nat := 118140960795 + 6103192 * 2 ^ 59
def prefixEnd_6103192 : Nat := 4983230072969 + 3 ^ 40 * 6103192 * 2
def baseEnd_6103192 : Nat := 116069297136125572849331

theorem tailTrace_6103192 : CollatzResearch.WordTrace tailWord_6103192 prefixEnd_6103192 116069297136125572849331 := by
  unfold tailWord_6103192
  simp only [CollatzResearch.WordTrace]
  refine ⟨111300849852592600526803915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148401133136790134035738553 111300849852592600526803915)
  ·
    refine ⟨166951274778888900790205873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111300849852592600526803915 166951274778888900790205873)
    ·
      refine ⟨125213456084166675592654405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166951274778888900790205873 125213456084166675592654405)
      ·
        refine ⟨23477523015781251673622701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125213456084166675592654405 23477523015781251673622701)
        ·
          refine ⟨8804071130917969377608513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23477523015781251673622701 8804071130917969377608513)
          ·
            refine ⟨6603053348188477033206385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8804071130917969377608513 6603053348188477033206385)
            ·
              refine ⟨4952290011141357774904789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6603053348188477033206385 4952290011141357774904789)
              ·
                refine ⟨116069297136125572849331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4952290011141357774904789 116069297136125572849331)
                ·
                  rfl

theorem cell23_6103192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 7].length) (baseStart_6103192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103192 prefixEnd_6103192 := by exact prefixLift 6103192
  have htrace : WordTrace (prefixWord ++ tailWord_6103192) baseStart_6103192 baseEnd_6103192 := by
    simpa [prefixWord, tailWord_6103192, baseEnd_6103192] using wordTrace_append hprefix tailTrace_6103192
  have hstable : (prefixWord ++ tailWord_6103192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103192).length < 2 ^ (prefixWord ++ tailWord_6103192).sum := by decide
  have hdescent : baseEnd_6103192 < baseStart_6103192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103236 : List Nat := [2, 3, 3, 1, 2, 1, 4, 1, 2, 1, 3]
def baseStart_6103236 : Nat := 118140960795 + 6103236 * 2 ^ 59
def prefixEnd_6103236 : Nat := 4983230072969 + 3 ^ 40 * 6103236 * 2
def baseEnd_6103236 : Nat := 3133893615824188294781735

theorem tailTrace_6103236 : CollatzResearch.WordTrace tailWord_6103236 prefixEnd_6103236 3133893615824188294781735 := by
  unfold tailWord_6103236
  simp only [CollatzResearch.WordTrace]
  refine ⟨111301652258512898284104781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148402203011350531045473041 111301652258512898284104781)
  ·
    refine ⟨41738119596942336856539293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111301652258512898284104781 41738119596942336856539293)
    ·
      refine ⟨15651794848853376321202235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41738119596942336856539293 15651794848853376321202235)
      ·
        refine ⟨23477692273280064481803353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15651794848853376321202235 23477692273280064481803353)
        ·
          refine ⟨17608269204960048361352515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23477692273280064481803353 17608269204960048361352515)
          ·
            refine ⟨26412403807440072542028773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17608269204960048361352515 26412403807440072542028773)
            ·
              refine ⟨4952325713895013601630395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26412403807440072542028773 4952325713895013601630395)
              ·
                refine ⟨7428488570842520402445593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4952325713895013601630395 7428488570842520402445593)
                ·
                  refine ⟨5571366428131890301834195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7428488570842520402445593 5571366428131890301834195)
                  ·
                    refine ⟨8357049642197835452751293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5571366428131890301834195 8357049642197835452751293)
                    ·
                      refine ⟨3133893615824188294781735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8357049642197835452751293 3133893615824188294781735)
                      ·
                        rfl

theorem cell23_6103236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_6103236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103236 prefixEnd_6103236 := by exact prefixLift 6103236
  have htrace : WordTrace (prefixWord ++ tailWord_6103236) baseStart_6103236 baseEnd_6103236 := by
    simpa [prefixWord, tailWord_6103236, baseEnd_6103236] using wordTrace_append hprefix tailTrace_6103236
  have hstable : (prefixWord ++ tailWord_6103236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103236).length < 2 ^ (prefixWord ++ tailWord_6103236).sum := by decide
  have hdescent : baseEnd_6103236 < baseStart_6103236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103242 : List Nat := [3, 1, 2, 1, 3, 1, 2, 3, 1, 4, 2]
def baseStart_6103242 : Nat := 118140960795 + 6103242 * 2 ^ 59
def prefixEnd_6103242 : Nat := 4983230072969 + 3 ^ 40 * 6103242 * 2
def baseEnd_6103242 : Nat := 3133896696708115271306707

theorem tailTrace_6103242 : CollatzResearch.WordTrace tailWord_6103242 prefixEnd_6103242 3133896696708115271306707 := by
  unfold tailWord_6103242
  simp only [CollatzResearch.WordTrace]
  refine ⟨55650880838751014898231995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148402348903336039728618653 55650880838751014898231995)
  ·
    refine ⟨83476321258126522347347993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55650880838751014898231995 83476321258126522347347993)
    ·
      refine ⟨62607240943594891760510995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83476321258126522347347993 62607240943594891760510995)
      ·
        refine ⟨93910861415392337640766493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62607240943594891760510995 93910861415392337640766493)
        ·
          refine ⟨35216573030772126615287435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93910861415392337640766493 35216573030772126615287435)
          ·
            refine ⟨52824859546158189922931153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35216573030772126615287435 52824859546158189922931153)
            ·
              refine ⟨39618644659618642442198365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52824859546158189922931153 39618644659618642442198365)
              ·
                refine ⟨14856991747356990915824387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39618644659618642442198365 14856991747356990915824387)
                ·
                  refine ⟨22285487621035486373736581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14856991747356990915824387 22285487621035486373736581)
                  ·
                    refine ⟨4178528928944153695075609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22285487621035486373736581 4178528928944153695075609)
                    ·
                      refine ⟨3133896696708115271306707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4178528928944153695075609 3133896696708115271306707)
                      ·
                        rfl

theorem cell23_6103242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 4, 2].length) (baseStart_6103242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103242 prefixEnd_6103242 := by exact prefixLift 6103242
  have htrace : WordTrace (prefixWord ++ tailWord_6103242) baseStart_6103242 baseEnd_6103242 := by
    simpa [prefixWord, tailWord_6103242, baseEnd_6103242] using wordTrace_append hprefix tailTrace_6103242
  have hstable : (prefixWord ++ tailWord_6103242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103242).length < 2 ^ (prefixWord ++ tailWord_6103242).sum := by decide
  have hdescent : baseEnd_6103242 < baseStart_6103242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103246 : List Nat := [4, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2]
def baseStart_6103246 : Nat := 118140960795 + 6103246 * 2 ^ 59
def prefixEnd_6103246 : Nat := 4983230072969 + 3 ^ 40 * 6103246 * 2
def baseEnd_6103246 : Nat := 3133898750630733255656689

theorem tailTrace_6103246 : CollatzResearch.WordTrace tailWord_6103246 prefixEnd_6103246 3133898750630733255656689 := by
  unfold tailWord_6103246
  simp only [CollatzResearch.WordTrace]
  refine ⟨27825458655873696034509199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148402446164659712184049061 27825458655873696034509199)
  ·
    refine ⟨41738187983810544051763799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27825458655873696034509199 41738187983810544051763799)
    ·
      refine ⟨62607281975715816077645699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41738187983810544051763799 62607281975715816077645699)
      ·
        refine ⟨93910922963573724116468549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62607281975715816077645699 93910922963573724116468549)
        ·
          refine ⟨17608298055670073271837853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93910922963573724116468549 17608298055670073271837853)
          ·
            refine ⟨6603111770876277476939195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17608298055670073271837853 6603111770876277476939195)
            ·
              refine ⟨9904667656314416215408793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6603111770876277476939195 9904667656314416215408793)
              ·
                refine ⟨7428500742235812161556595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9904667656314416215408793 7428500742235812161556595)
                ·
                  refine ⟨11142751113353718242334893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7428500742235812161556595 11142751113353718242334893)
                  ·
                    refine ⟨4178531667507644340875585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11142751113353718242334893 4178531667507644340875585)
                    ·
                      refine ⟨3133898750630733255656689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4178531667507644340875585 3133898750630733255656689)
                      ·
                        rfl

theorem cell23_6103246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2].length) (baseStart_6103246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103246 prefixEnd_6103246 := by exact prefixLift 6103246
  have htrace : WordTrace (prefixWord ++ tailWord_6103246) baseStart_6103246 baseEnd_6103246 := by
    simpa [prefixWord, tailWord_6103246, baseEnd_6103246] using wordTrace_append hprefix tailTrace_6103246
  have hstable : (prefixWord ++ tailWord_6103246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103246).length < 2 ^ (prefixWord ++ tailWord_6103246).sum := by decide
  have hdescent : baseEnd_6103246 < baseStart_6103246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103275 : List Nat := [1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 3]
def baseStart_6103275 : Nat := 118140960795 + 6103275 * 2 ^ 59
def prefixEnd_6103275 : Nat := 4983230072969 + 3 ^ 40 * 6103275 * 2
def baseEnd_6103275 : Nat := 3133913641569713642194055

theorem tailTrace_6103275 : CollatzResearch.WordTrace tailWord_6103275 prefixEnd_6103275 3133913641569713642194055 := by
  unfold tailWord_6103275
  simp only [CollatzResearch.WordTrace]
  refine ⟨222604726963884506228879279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148403151309256337485919519 222604726963884506228879279)
  ·
    refine ⟨333907090445826759343318919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222604726963884506228879279 333907090445826759343318919)
    ·
      refine ⟨500860635668740139014978379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333907090445826759343318919 500860635668740139014978379)
      ·
        refine ⟨751290953503110208522467569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500860635668740139014978379 751290953503110208522467569)
        ·
          refine ⟨563468215127332656391850677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 751290953503110208522467569 563468215127332656391850677)
          ·
            refine ⟨52825145168187436536736001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 563468215127332656391850677 52825145168187436536736001)
            ·
              refine ⟨39618858876140577402552001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52825145168187436536736001 39618858876140577402552001)
              ·
                refine ⟨29714144157105433051914001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39618858876140577402552001 29714144157105433051914001)
                ·
                  refine ⟨22285608117829074788935501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29714144157105433051914001 22285608117829074788935501)
                  ·
                    refine ⟨8357103044185903045850813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22285608117829074788935501 8357103044185903045850813)
                    ·
                      refine ⟨3133913641569713642194055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8357103044185903045850813 3133913641569713642194055)
                      ·
                        rfl

theorem cell23_6103275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 3].length) (baseStart_6103275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103275 prefixEnd_6103275 := by exact prefixLift 6103275
  have htrace : WordTrace (prefixWord ++ tailWord_6103275) baseStart_6103275 baseEnd_6103275 := by
    simpa [prefixWord, tailWord_6103275, baseEnd_6103275] using wordTrace_append hprefix tailTrace_6103275
  have hstable : (prefixWord ++ tailWord_6103275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103275).length < 2 ^ (prefixWord ++ tailWord_6103275).sum := by decide
  have hdescent : baseEnd_6103275 < baseStart_6103275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103292 : List Nat := [2, 2, 2, 1, 4, 2, 1, 1, 2, 3, 3]
def baseStart_6103292 : Nat := 118140960795 + 6103292 * 2 ^ 59
def prefixEnd_6103292 : Nat := 4983230072969 + 3 ^ 40 * 6103292 * 2
def baseEnd_6103292 : Nat := 3133922370740840075681477

theorem tailTrace_6103292 : CollatzResearch.WordTrace tailWord_6103292 prefixEnd_6103292 3133922370740840075681477 := by
  unfold tailWord_6103292
  simp only [CollatzResearch.WordTrace]
  refine ⟨111302673502411459066124065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148403564669881945421498753 111302673502411459066124065)
  ·
    refine ⟨83477005126808594299593049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111302673502411459066124065 83477005126808594299593049)
    ·
      refine ⟨62607753845106445724694787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83477005126808594299593049 62607753845106445724694787)
      ·
        refine ⟨93911630767659668587042181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62607753845106445724694787 93911630767659668587042181)
        ·
          refine ⟨17608430768936187860070409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93911630767659668587042181 17608430768936187860070409)
          ·
            refine ⟨13206323076702140895052807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17608430768936187860070409 13206323076702140895052807)
            ·
              refine ⟨19809484615053211342579211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13206323076702140895052807 19809484615053211342579211)
              ·
                refine ⟨29714226922579817013868817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19809484615053211342579211 29714226922579817013868817)
                ·
                  refine ⟨22285670191934862760401613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29714226922579817013868817 22285670191934862760401613)
                  ·
                    refine ⟨8357126321975573535150605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22285670191934862760401613 8357126321975573535150605)
                    ·
                      refine ⟨3133922370740840075681477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8357126321975573535150605 3133922370740840075681477)
                      ·
                        rfl

theorem cell23_6103292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_6103292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103292 prefixEnd_6103292 := by exact prefixLift 6103292
  have htrace : WordTrace (prefixWord ++ tailWord_6103292) baseStart_6103292 baseEnd_6103292 := by
    simpa [prefixWord, tailWord_6103292, baseEnd_6103292] using wordTrace_append hprefix tailTrace_6103292
  have hstable : (prefixWord ++ tailWord_6103292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103292).length < 2 ^ (prefixWord ++ tailWord_6103292).sum := by decide
  have hdescent : baseEnd_6103292 < baseStart_6103292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103376 : List Nat := [2, 1, 1, 1, 1, 8, 1, 3, 1, 4]
def baseStart_6103376 : Nat := 118140960795 + 6103376 * 2 ^ 59
def prefixEnd_6103376 : Nat := 4983230072969 + 3 ^ 40 * 6103376 * 2
def baseEnd_6103376 : Nat := 1044655167705272582343697

theorem tailTrace_6103376 : CollatzResearch.WordTrace tailWord_6103376 prefixEnd_6103376 1044655167705272582343697 := by
  unfold tailWord_6103376
  simp only [CollatzResearch.WordTrace]
  refine ⟨111304205368259300239152991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148405607157679066985537321 111304205368259300239152991)
  ·
    refine ⟨166956308052388950358729487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111304205368259300239152991 166956308052388950358729487)
    ·
      refine ⟨250434462078583425538094231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166956308052388950358729487 250434462078583425538094231)
      ·
        refine ⟨375651693117875138307141347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250434462078583425538094231 375651693117875138307141347)
        ·
          refine ⟨563477539676812707460712021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375651693117875138307141347 563477539676812707460712021)
          ·
            refine ⟨6603252418087648915555219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 563477539676812707460712021 6603252418087648915555219)
            ·
              refine ⟨9904878627131473373332829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6603252418087648915555219 9904878627131473373332829)
              ·
                refine ⟨3714329485174302514999811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9904878627131473373332829 3714329485174302514999811)
                ·
                  refine ⟨5571494227761453772499717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3714329485174302514999811 5571494227761453772499717)
                  ·
                    refine ⟨1044655167705272582343697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5571494227761453772499717 1044655167705272582343697)
                    ·
                      rfl

theorem cell23_6103376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 1, 4].length) (baseStart_6103376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103376 prefixEnd_6103376 := by exact prefixLift 6103376
  have htrace : WordTrace (prefixWord ++ tailWord_6103376) baseStart_6103376 baseEnd_6103376 := by
    simpa [prefixWord, tailWord_6103376, baseEnd_6103376] using wordTrace_append hprefix tailTrace_6103376
  have hstable : (prefixWord ++ tailWord_6103376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103376).length < 2 ^ (prefixWord ++ tailWord_6103376).sum := by decide
  have hdescent : baseEnd_6103376 < baseStart_6103376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103385 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 5, 5]
def baseStart_6103385 : Nat := 118140960795 + 6103385 * 2 ^ 59
def prefixEnd_6103385 : Nat := 4983230072969 + 3 ^ 40 * 6103385 * 2
def baseEnd_6103385 : Nat := 1044656708147236070606183

theorem tailTrace_6103385 : CollatzResearch.WordTrace tailWord_6103385 prefixEnd_6103385 1044656708147236070606183 := by
  unfold tailWord_6103385
  simp only [CollatzResearch.WordTrace]
  refine ⟨222608738993485995015383609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148405825995657330010255739 222608738993485995015383609)
  ·
    refine ⟨166956554245114496261537707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222608738993485995015383609 166956554245114496261537707)
    ·
      refine ⟨250434831367671744392306561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166956554245114496261537707 250434831367671744392306561)
      ·
        refine ⟨187826123525753808294229921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250434831367671744392306561 187826123525753808294229921)
        ·
          refine ⟨140869592644315356220672441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187826123525753808294229921 140869592644315356220672441)
          ·
            refine ⟨105652194483236517165504331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140869592644315356220672441 105652194483236517165504331)
            ·
              refine ⟨158478291724854775748256497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105652194483236517165504331 158478291724854775748256497)
              ·
                refine ⟨118858718793641081811192373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158478291724854775748256497 118858718793641081811192373)
                ·
                  refine ⟨11143004886903851419799285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118858718793641081811192373 11143004886903851419799285)
                  ·
                    refine ⟨1044656708147236070606183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11143004886903851419799285 1044656708147236070606183)
                    ·
                      rfl

theorem cell23_6103385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 5].length) (baseStart_6103385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103385 prefixEnd_6103385 := by exact prefixLift 6103385
  have htrace : WordTrace (prefixWord ++ tailWord_6103385) baseStart_6103385 baseEnd_6103385 := by
    simpa [prefixWord, tailWord_6103385, baseEnd_6103385] using wordTrace_append hprefix tailTrace_6103385
  have hstable : (prefixWord ++ tailWord_6103385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103385).length < 2 ^ (prefixWord ++ tailWord_6103385).sum := by decide
  have hdescent : baseEnd_6103385 < baseStart_6103385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103419 : List Nat := [1, 1, 1, 1, 1, 9, 1, 2, 1, 5]
def baseStart_6103419 : Nat := 118140960795 + 6103419 * 2 ^ 59
def prefixEnd_6103419 : Nat := 4983230072969 + 3 ^ 40 * 6103419 * 2
def baseEnd_6103419 : Nat := 1044662527594653692931131

theorem tailTrace_6103419 : CollatzResearch.WordTrace tailWord_6103419 prefixEnd_6103419 1044662527594653692931131 := by
  unfold tailWord_6103419
  simp only [CollatzResearch.WordTrace]
  refine ⟨222609979075362818822121311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148406652716908545881414207 222609979075362818822121311)
  ·
    refine ⟨333914968613044228233181967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222609979075362818822121311 333914968613044228233181967)
    ·
      refine ⟨500872452919566342349772951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333914968613044228233181967 500872452919566342349772951)
      ·
        refine ⟨751308679379349513524659427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500872452919566342349772951 751308679379349513524659427)
        ·
          refine ⟨1126963019069024270286989141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751308679379349513524659427 1126963019069024270286989141)
          ·
            refine ⟨6603298939857564083712827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1126963019069024270286989141 6603298939857564083712827)
            ·
              refine ⟨9904948409786346125569241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6603298939857564083712827 9904948409786346125569241)
              ·
                refine ⟨7428711307339759594176931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9904948409786346125569241 7428711307339759594176931)
                ·
                  refine ⟨11143066961009639391265397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7428711307339759594176931 11143066961009639391265397)
                  ·
                    refine ⟨1044662527594653692931131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11143066961009639391265397 1044662527594653692931131)
                    ·
                      rfl

theorem cell23_6103419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 5].length) (baseStart_6103419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103419 prefixEnd_6103419 := by exact prefixLift 6103419
  have htrace : WordTrace (prefixWord ++ tailWord_6103419) baseStart_6103419 baseEnd_6103419 := by
    simpa [prefixWord, tailWord_6103419, baseEnd_6103419] using wordTrace_append hprefix tailTrace_6103419
  have hstable : (prefixWord ++ tailWord_6103419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103419).length < 2 ^ (prefixWord ++ tailWord_6103419).sum := by decide
  have hdescent : baseEnd_6103419 < baseStart_6103419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103432 : List Nat := [2, 1, 3, 3, 1, 1, 3, 2, 1, 6]
def baseStart_6103432 : Nat := 118140960795 + 6103432 * 2 ^ 59
def prefixEnd_6103432 : Nat := 4983230072969 + 3 ^ 40 * 6103432 * 2
def baseEnd_6103432 : Nat := 1044664752677489842643611

theorem tailTrace_6103432 : CollatzResearch.WordTrace tailWord_6103432 prefixEnd_6103432 1044664752677489842643611 := by
  unfold tailWord_6103432
  simp only [CollatzResearch.WordTrace]
  refine ⟨111305226612157861021172275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148406968816210481361563033 111305226612157861021172275)
  ·
    refine ⟨166957839918236791531758413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111305226612157861021172275 166957839918236791531758413)
    ·
      refine ⟨62609189969338796824409405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166957839918236791531758413 62609189969338796824409405)
      ·
        refine ⟨23478446238502048809153527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62609189969338796824409405 23478446238502048809153527)
        ·
          refine ⟨35217669357753073213730291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23478446238502048809153527 35217669357753073213730291)
          ·
            refine ⟨52826504036629609820595437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35217669357753073213730291 52826504036629609820595437)
            ·
              refine ⟨19809939013736103682723289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52826504036629609820595437 19809939013736103682723289)
              ·
                refine ⟨14857454260302077762042467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19809939013736103682723289 14857454260302077762042467)
                ·
                  refine ⟨22286181390453116643063701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14857454260302077762042467 22286181390453116643063701)
                  ·
                    refine ⟨1044664752677489842643611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22286181390453116643063701 1044664752677489842643611)
                    ·
                      rfl

theorem cell23_6103432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_6103432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103432 prefixEnd_6103432 := by exact prefixLift 6103432
  have htrace : WordTrace (prefixWord ++ tailWord_6103432) baseStart_6103432 baseEnd_6103432 := by
    simpa [prefixWord, tailWord_6103432, baseEnd_6103432] using wordTrace_append hprefix tailTrace_6103432
  have hstable : (prefixWord ++ tailWord_6103432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103432).length < 2 ^ (prefixWord ++ tailWord_6103432).sum := by decide
  have hdescent : baseEnd_6103432 < baseStart_6103432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103449 : List Nat := [1, 2, 1, 2, 1, 4, 4, 2, 2, 4]
def baseStart_6103449 : Nat := 118140960795 + 6103449 * 2 ^ 59
def prefixEnd_6103449 : Nat := 4983230072969 + 3 ^ 40 * 6103449 * 2
def baseEnd_6103449 : Nat := 1044667662401198653806085

theorem tailTrace_6103449 : CollatzResearch.WordTrace tailWord_6103449 prefixEnd_6103449 1044667662401198653806085 := by
  unfold tailWord_6103449
  simp only [CollatzResearch.WordTrace]
  refine ⟨222611073265254133945713401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148407382176836089297142267 222611073265254133945713401)
  ·
    refine ⟨166958304948940600459285051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222611073265254133945713401 166958304948940600459285051)
    ·
      refine ⟨250437457423410900688927577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166958304948940600459285051 250437457423410900688927577)
      ·
        refine ⟨187828093067558175516695683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250437457423410900688927577 187828093067558175516695683)
        ·
          refine ⟨281742139601337263275043525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187828093067558175516695683 281742139601337263275043525)
          ·
            refine ⟨52826651175250736864070661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 281742139601337263275043525 52826651175250736864070661)
            ·
              refine ⟨9904997095359513162013249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52826651175250736864070661 9904997095359513162013249)
              ·
                refine ⟨7428747821519634871509937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9904997095359513162013249 7428747821519634871509937)
                ·
                  refine ⟨5571560866139726153632453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7428747821519634871509937 5571560866139726153632453)
                  ·
                    refine ⟨1044667662401198653806085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5571560866139726153632453 1044667662401198653806085)
                    ·
                      rfl

theorem cell23_6103449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 4].length) (baseStart_6103449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103449 prefixEnd_6103449 := by exact prefixLift 6103449
  have htrace : WordTrace (prefixWord ++ tailWord_6103449) baseStart_6103449 baseEnd_6103449 := by
    simpa [prefixWord, tailWord_6103449, baseEnd_6103449] using wordTrace_append hprefix tailTrace_6103449
  have hstable : (prefixWord ++ tailWord_6103449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103449).length < 2 ^ (prefixWord ++ tailWord_6103449).sum := by decide
  have hdescent : baseEnd_6103449 < baseStart_6103449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103450 : List Nat := [3, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3]
def baseStart_6103450 : Nat := 118140960795 + 6103450 * 2 ^ 59
def prefixEnd_6103450 : Nat := 4983230072969 + 3 ^ 40 * 6103450 * 2
def baseEnd_6103450 : Nat := 3134003500684250457505751

theorem tailTrace_6103450 : CollatzResearch.WordTrace tailWord_6103450 prefixEnd_6103450 3134003500684250457505751 := by
  unfold tailWord_6103450
  simp only [CollatzResearch.WordTrace]
  refine ⟨55652777434562627779124951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148407406492167007410999869 55652777434562627779124951)
  ·
    refine ⟨83479166151843941668687427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55652777434562627779124951 83479166151843941668687427)
    ·
      refine ⟨125218749227765912503031141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83479166151843941668687427 125218749227765912503031141)
      ·
        refine ⟨23478515480206108594318339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125218749227765912503031141 23478515480206108594318339)
        ·
          refine ⟨35217773220309162891477509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23478515480206108594318339 35217773220309162891477509)
          ·
            refine ⟨6603332478807968042152033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35217773220309162891477509 6603332478807968042152033)
            ·
              refine ⟨4952499359105976031614025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6603332478807968042152033 4952499359105976031614025)
              ·
                refine ⟨3714374519329482023710519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4952499359105976031614025 3714374519329482023710519)
                ·
                  refine ⟨5571561778994223035565779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3714374519329482023710519 5571561778994223035565779)
                  ·
                    refine ⟨8357342668491334553348669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5571561778994223035565779 8357342668491334553348669)
                    ·
                      refine ⟨3134003500684250457505751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8357342668491334553348669 3134003500684250457505751)
                      ·
                        rfl

theorem cell23_6103450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_6103450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103450 prefixEnd_6103450 := by exact prefixLift 6103450
  have htrace : WordTrace (prefixWord ++ tailWord_6103450) baseStart_6103450 baseEnd_6103450 := by
    simpa [prefixWord, tailWord_6103450, baseEnd_6103450] using wordTrace_append hprefix tailTrace_6103450
  have hstable : (prefixWord ++ tailWord_6103450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103450).length < 2 ^ (prefixWord ++ tailWord_6103450).sum := by decide
  have hdescent : baseEnd_6103450 < baseStart_6103450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103465 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 2, 2, 6]
def baseStart_6103465 : Nat := 118140960795 + 6103465 * 2 ^ 59
def prefixEnd_6103465 : Nat := 4983230072969 + 3 ^ 40 * 6103465 * 2
def baseEnd_6103465 : Nat := 3134011202894067898818181

theorem tailTrace_6103465 : CollatzResearch.WordTrace tailWord_6103465 prefixEnd_6103465 3134011202894067898818181 := by
  unfold tailWord_6103465
  simp only [CollatzResearch.WordTrace]
  refine ⟨222611656833196168678295849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148407771222130779118863899 222611656833196168678295849)
  ·
    refine ⟨166958742624897126508721887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222611656833196168678295849 166958742624897126508721887)
    ·
      refine ⟨250438113937345689763082831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166958742624897126508721887 250438113937345689763082831)
      ·
        refine ⟨375657170906018534644624247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250438113937345689763082831 375657170906018534644624247)
        ·
          refine ⟨563485756359027801966936371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375657170906018534644624247 563485756359027801966936371)
          ·
            refine ⟨845228634538541702950404557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563485756359027801966936371 845228634538541702950404557)
            ·
              refine ⟨316960737951953138606401709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 845228634538541702950404557 316960737951953138606401709)
              ·
                refine ⟨118860276731982426977400641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 316960737951953138606401709 118860276731982426977400641)
                ·
                  refine ⟨89145207548986820233050481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118860276731982426977400641 89145207548986820233050481)
                  ·
                    refine ⟨66858905661740115174787861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89145207548986820233050481 66858905661740115174787861)
                    ·
                      refine ⟨3134011202894067898818181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66858905661740115174787861 3134011202894067898818181)
                      ·
                        rfl

theorem cell23_6103465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_6103465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103465 prefixEnd_6103465 := by exact prefixLift 6103465
  have htrace : WordTrace (prefixWord ++ tailWord_6103465) baseStart_6103465 baseEnd_6103465 := by
    simpa [prefixWord, tailWord_6103465, baseEnd_6103465] using wordTrace_append hprefix tailTrace_6103465
  have hstable : (prefixWord ++ tailWord_6103465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103465).length < 2 ^ (prefixWord ++ tailWord_6103465).sum := by decide
  have hdescent : baseEnd_6103465 < baseStart_6103465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103523 : List Nat := [1, 1, 1, 6, 4, 1, 1, 1, 1, 3, 3]
def baseStart_6103523 : Nat := 118140960795 + 6103523 * 2 ^ 59
def prefixEnd_6103523 : Nat := 4983230072969 + 3 ^ 40 * 6103523 * 2
def baseEnd_6103523 : Nat := 3134040984772028671892915

theorem tailTrace_6103523 : CollatzResearch.WordTrace tailWord_6103523 prefixEnd_6103523 3134040984772028671892915 := by
  unfold tailWord_6103523
  simp only [CollatzResearch.WordTrace]
  refine ⟨222613772266986044583907223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148409181511324029722604815 222613772266986044583907223)
  ·
    refine ⟨333920658400479066875860835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222613772266986044583907223 333920658400479066875860835)
    ·
      refine ⟨500880987600718600313791253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333920658400479066875860835 500880987600718600313791253)
      ·
        refine ⟨23478796293783684389708965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 500880987600718600313791253 23478796293783684389708965)
        ·
          refine ⟨4402274305084440823070431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23478796293783684389708965 4402274305084440823070431)
          ·
            refine ⟨6603411457626661234605647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4402274305084440823070431 6603411457626661234605647)
            ·
              refine ⟨9905117186439991851908471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6603411457626661234605647 9905117186439991851908471)
              ·
                refine ⟨14857675779659987777862707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9905117186439991851908471 14857675779659987777862707)
                ·
                  refine ⟨22286513669489981666794061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14857675779659987777862707 22286513669489981666794061)
                  ·
                    refine ⟨8357442626058743125047773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22286513669489981666794061 8357442626058743125047773)
                    ·
                      refine ⟨3134040984772028671892915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8357442626058743125047773 3134040984772028671892915)
                      ·
                        rfl

theorem cell23_6103523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_6103523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103523 prefixEnd_6103523 := by exact prefixLift 6103523
  have htrace : WordTrace (prefixWord ++ tailWord_6103523) baseStart_6103523 baseEnd_6103523 := by
    simpa [prefixWord, tailWord_6103523, baseEnd_6103523] using wordTrace_append hprefix tailTrace_6103523
  have hstable : (prefixWord ++ tailWord_6103523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103523).length < 2 ^ (prefixWord ++ tailWord_6103523).sum := by decide
  have hdescent : baseEnd_6103523 < baseStart_6103523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
