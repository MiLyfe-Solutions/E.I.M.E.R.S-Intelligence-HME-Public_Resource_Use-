import V185TrunkScan23Chunk0068

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_409842 : List Nat := [3, 2, 1, 3, 2, 1, 1, 2, 3, 2, 3]
def baseStart_409842 : Nat := 118140960795 + 409842 * 2 ^ 59
def prefixEnd_409842 : Nat := 4983230072969 + 3 ^ 40 * 409842 * 2
def baseEnd_409842 : Nat := 210445938400090724990177

theorem tailTrace_409842 : CollatzResearch.WordTrace tailWord_409842 prefixEnd_409842 210445938400090724990177 := by
  unfold tailWord_409842
  simp only [CollatzResearch.WordTrace]
  refine ⟨3737041445304976071521945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9965443854146602857391853 3737041445304976071521945)
  ·
    refine ⟨2802781083978732053641459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3737041445304976071521945 2802781083978732053641459)
    ·
      refine ⟨4204171625968098080462189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2802781083978732053641459 4204171625968098080462189)
      ·
        refine ⟨1576564359738036780173321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4204171625968098080462189 1576564359738036780173321)
        ·
          refine ⟨1182423269803527585129991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1576564359738036780173321 1182423269803527585129991)
          ·
            refine ⟨1773634904705291377694987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1182423269803527585129991 1773634904705291377694987)
            ·
              refine ⟨2660452357057937066542481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1773634904705291377694987 2660452357057937066542481)
              ·
                refine ⟨1995339267793452799906861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2660452357057937066542481 1995339267793452799906861)
                ·
                  refine ⟨748252225422544799965073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1995339267793452799906861 748252225422544799965073)
                  ·
                    refine ⟨561189169066908599973805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 748252225422544799965073 561189169066908599973805)
                    ·
                      refine ⟨210445938400090724990177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 561189169066908599973805 210445938400090724990177)
                      ·
                        rfl

theorem cell23_409842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_409842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409842 prefixEnd_409842 := by exact prefixLift 409842
  have htrace : WordTrace (prefixWord ++ tailWord_409842) baseStart_409842 baseEnd_409842 := by
    simpa [prefixWord, tailWord_409842, baseEnd_409842] using wordTrace_append hprefix tailTrace_409842
  have hstable : (prefixWord ++ tailWord_409842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409842).length < 2 ^ (prefixWord ++ tailWord_409842).sum := by decide
  have hdescent : baseEnd_409842 < baseStart_409842 := by decide
  rcases family_descends (prefixWord ++ tailWord_409842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409848 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 2, 2, 6]
def baseStart_409848 : Nat := 118140960795 + 409848 * 2 ^ 59
def prefixEnd_409848 : Nat := 4983230072969 + 3 ^ 40 * 409848 * 2
def baseEnd_409848 : Nat := 210449019284017701515149

theorem tailTrace_409848 : CollatzResearch.WordTrace tailWord_409848 prefixEnd_409848 210449019284017701515149 := by
  unfold tailWord_409848
  simp only [CollatzResearch.WordTrace]
  refine ⟨7474192309599083655403099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9965589746132111540537465 7474192309599083655403099)
  ·
    refine ⟨11211288464398625483104649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7474192309599083655403099 11211288464398625483104649)
    ·
      refine ⟨8408466348298969112328487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11211288464398625483104649 8408466348298969112328487)
      ·
        refine ⟨12612699522448453668492731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8408466348298969112328487 12612699522448453668492731)
        ·
          refine ⟨18919049283672680502739097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12612699522448453668492731 18919049283672680502739097)
          ·
            refine ⟨14189286962754510377054323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18919049283672680502739097 14189286962754510377054323)
            ·
              refine ⟨21283930444131765565581485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14189286962754510377054323 21283930444131765565581485)
              ·
                refine ⟨7981473916549412087093057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21283930444131765565581485 7981473916549412087093057)
                ·
                  refine ⟨5986105437412059065319793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7981473916549412087093057 5986105437412059065319793)
                  ·
                    refine ⟨4489579078059044298989845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5986105437412059065319793 4489579078059044298989845)
                    ·
                      refine ⟨210449019284017701515149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4489579078059044298989845 210449019284017701515149)
                      ·
                        rfl

theorem cell23_409848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_409848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409848 prefixEnd_409848 := by exact prefixLift 409848
  have htrace : WordTrace (prefixWord ++ tailWord_409848) baseStart_409848 baseEnd_409848 := by
    simpa [prefixWord, tailWord_409848, baseEnd_409848] using wordTrace_append hprefix tailTrace_409848
  have hstable : (prefixWord ++ tailWord_409848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409848).length < 2 ^ (prefixWord ++ tailWord_409848).sum := by decide
  have hdescent : baseEnd_409848 < baseStart_409848 := by decide
  rcases family_descends (prefixWord ++ tailWord_409848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409852 : List Nat := [2, 2, 2, 1, 4, 2, 2, 1, 1, 2, 4]
def baseStart_409852 : Nat := 118140960795 + 409852 * 2 ^ 59
def prefixEnd_409852 : Nat := 4983230072969 + 3 ^ 40 * 409852 * 2
def baseEnd_409852 : Nat := 210451073206635685865131

theorem tailTrace_409852 : CollatzResearch.WordTrace tailWord_409852 prefixEnd_409852 210451073206635685865131 := by
  unfold tailWord_409852
  simp only [CollatzResearch.WordTrace]
  refine ⟨7474265255591837996975905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9965687007455783995967873 7474265255591837996975905)
  ·
    refine ⟨5605698941693878497731929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7474265255591837996975905 5605698941693878497731929)
    ·
      refine ⟨4204274206270408873298947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5605698941693878497731929 4204274206270408873298947)
      ·
        refine ⟨6306411309405613309948421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4204274206270408873298947 6306411309405613309948421)
        ·
          refine ⟨1182452120513552495615329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6306411309405613309948421 1182452120513552495615329)
          ·
            refine ⟨886839090385164371711497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1182452120513552495615329 886839090385164371711497)
            ·
              refine ⟨665129317788873278783623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 886839090385164371711497 665129317788873278783623)
              ·
                refine ⟨997693976683309918175435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 665129317788873278783623 997693976683309918175435)
                ·
                  refine ⟨1496540965024964877263153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 997693976683309918175435 1496540965024964877263153)
                  ·
                    refine ⟨1122405723768723657947365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1496540965024964877263153 1122405723768723657947365)
                    ·
                      refine ⟨210451073206635685865131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1122405723768723657947365 210451073206635685865131)
                      ·
                        rfl

theorem cell23_409852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_409852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409852 prefixEnd_409852 := by exact prefixLift 409852
  have htrace : WordTrace (prefixWord ++ tailWord_409852) baseStart_409852 baseEnd_409852 := by
    simpa [prefixWord, tailWord_409852, baseEnd_409852] using wordTrace_append hprefix tailTrace_409852
  have hstable : (prefixWord ++ tailWord_409852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409852).length < 2 ^ (prefixWord ++ tailWord_409852).sum := by decide
  have hdescent : baseEnd_409852 < baseStart_409852 := by decide
  rcases family_descends (prefixWord ++ tailWord_409852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409889 : List Nat := [1, 2, 3, 2, 1, 1, 5, 2, 2, 1, 3]
def baseStart_409889 : Nat := 118140960795 + 409889 * 2 ^ 59
def prefixEnd_409889 : Nat := 4983230072969 + 3 ^ 40 * 409889 * 2
def baseEnd_409889 : Nat := 210470071990852041102461

theorem tailTrace_409889 : CollatzResearch.WordTrace tailWord_409889 prefixEnd_409889 210470071990852041102461 := by
  unfold tailWord_409889
  simp only [CollatzResearch.WordTrace]
  refine ⟨14949880012049631313048721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9966586674699754208699147 14949880012049631313048721)
  ·
    refine ⟨11212410009037223484786541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14949880012049631313048721 11212410009037223484786541)
    ·
      refine ⟨4204653753388958806794953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11212410009037223484786541 4204653753388958806794953)
      ·
        refine ⟨3153490315041719105096215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4204653753388958806794953 3153490315041719105096215)
        ·
          refine ⟨4730235472562578657644323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3153490315041719105096215 4730235472562578657644323)
          ·
            refine ⟨7095353208843867986466485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4730235472562578657644323 7095353208843867986466485)
            ·
              refine ⟨665189363329112623731233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7095353208843867986466485 665189363329112623731233)
              ·
                refine ⟨498892022496834467798425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 665189363329112623731233 498892022496834467798425)
                ·
                  refine ⟨374169016872625850848819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498892022496834467798425 374169016872625850848819)
                  ·
                    refine ⟨561253525308938776273229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 374169016872625850848819 561253525308938776273229)
                    ·
                      refine ⟨210470071990852041102461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 561253525308938776273229 210470071990852041102461)
                      ·
                        rfl

theorem cell23_409889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_409889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409889 prefixEnd_409889 := by exact prefixLift 409889
  have htrace : WordTrace (prefixWord ++ tailWord_409889) baseStart_409889 baseEnd_409889 := by
    simpa [prefixWord, tailWord_409889, baseEnd_409889] using wordTrace_append hprefix tailTrace_409889
  have hstable : (prefixWord ++ tailWord_409889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409889).length < 2 ^ (prefixWord ++ tailWord_409889).sum := by decide
  have hdescent : baseEnd_409889 < baseStart_409889 := by decide
  rcases family_descends (prefixWord ++ tailWord_409889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409906 : List Nat := [3, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3]
def baseStart_409906 : Nat := 118140960795 + 409906 * 2 ^ 59
def prefixEnd_409906 : Nat := 4983230072969 + 3 ^ 40 * 409906 * 2
def baseEnd_409906 : Nat := 210478801161978474589883

theorem tailTrace_409906 : CollatzResearch.WordTrace tailWord_409906 prefixEnd_409906 210478801161978474589883 := by
  unfold tailWord_409906
  simp only [CollatzResearch.WordTrace]
  refine ⟨3737625013247010804104393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9967000035325362144278381 3737625013247010804104393)
  ·
    refine ⟨2803218759935258103078295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3737625013247010804104393 2803218759935258103078295)
    ·
      refine ⟨4204828139902887154617443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2803218759935258103078295 4204828139902887154617443)
      ·
        refine ⟨6307242209854330731926165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4204828139902887154617443 6307242209854330731926165)
        ·
          refine ⟨295651978586921753059039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6307242209854330731926165 295651978586921753059039)
          ·
            refine ⟨443477967880382629588559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295651978586921753059039 443477967880382629588559)
            ·
              refine ⟨665216951820573944382839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443477967880382629588559 665216951820573944382839)
              ·
                refine ⟨997825427730860916574259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 665216951820573944382839 997825427730860916574259)
                ·
                  refine ⟨1496738141596291374861389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 997825427730860916574259 1496738141596291374861389)
                  ·
                    refine ⟨561276803098609265573021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1496738141596291374861389 561276803098609265573021)
                    ·
                      refine ⟨210478801161978474589883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 561276803098609265573021 210478801161978474589883)
                      ·
                        rfl

theorem cell23_409906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3].length) (baseStart_409906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409906 prefixEnd_409906 := by exact prefixLift 409906
  have htrace : WordTrace (prefixWord ++ tailWord_409906) baseStart_409906 baseEnd_409906 := by
    simpa [prefixWord, tailWord_409906, baseEnd_409906] using wordTrace_append hprefix tailTrace_409906
  have hstable : (prefixWord ++ tailWord_409906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409906).length < 2 ^ (prefixWord ++ tailWord_409906).sum := by decide
  have hdescent : baseEnd_409906 < baseStart_409906 := by decide
  rcases family_descends (prefixWord ++ tailWord_409906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410005 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 1, 5, 5]
def baseStart_410005 : Nat := 118140960795 + 410005 * 2 ^ 59
def prefixEnd_410005 : Nat := 4983230072969 + 3 ^ 40 * 410005 * 2
def baseEnd_410005 : Nat := 210529635746773587251927

theorem tailTrace_410005 : CollatzResearch.WordTrace tailWord_410005 prefixEnd_410005 210529635746773587251927 := by
  unfold tailWord_410005
  simp only [CollatzResearch.WordTrace]
  refine ⟨14954110879629383124271469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9969407253086255416180979 14954110879629383124271469)
  ·
    refine ⟨5607791579861018671601801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14954110879629383124271469 5607791579861018671601801)
    ·
      refine ⟨4205843684895764003701351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5607791579861018671601801 4205843684895764003701351)
      ·
        refine ⟨6308765527343646005552027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4205843684895764003701351 6308765527343646005552027)
        ·
          refine ⟨9463148291015469008328041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6308765527343646005552027 9463148291015469008328041)
          ·
            refine ⟨7097361218261601756246031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9463148291015469008328041 7097361218261601756246031)
            ·
              refine ⟨10646041827392402634369047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7097361218261601756246031 10646041827392402634369047)
              ·
                refine ⟨15969062741088603951553571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10646041827392402634369047 15969062741088603951553571)
                ·
                  refine ⟨23953594111632905927330357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15969062741088603951553571 23953594111632905927330357)
                  ·
                    refine ⟨2245649447965584930687221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23953594111632905927330357 2245649447965584930687221)
                    ·
                      refine ⟨210529635746773587251927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2245649447965584930687221 210529635746773587251927)
                      ·
                        rfl

theorem cell23_410005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_410005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410005 prefixEnd_410005 := by exact prefixLift 410005
  have htrace : WordTrace (prefixWord ++ tailWord_410005) baseStart_410005 baseEnd_410005 := by
    simpa [prefixWord, tailWord_410005, baseEnd_410005] using wordTrace_append hprefix tailTrace_410005
  have hstable : (prefixWord ++ tailWord_410005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410005).length < 2 ^ (prefixWord ++ tailWord_410005).sum := by decide
  have hdescent : baseEnd_410005 < baseStart_410005 := by decide
  rcases family_descends (prefixWord ++ tailWord_410005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410019 : List Nat := [1, 1, 1, 4, 1, 5, 1, 1, 2, 4, 2]
def baseStart_410019 : Nat := 118140960795 + 410019 * 2 ^ 59
def prefixEnd_410019 : Nat := 4983230072969 + 3 ^ 40 * 410019 * 2
def baseEnd_410019 : Nat := 210536824475936532476863

theorem tailTrace_410019 : CollatzResearch.WordTrace tailWord_410019 prefixEnd_410019 210536824475936532476863 := by
  unfold tailWord_410019
  simp only [CollatzResearch.WordTrace]
  refine ⟨14954621501578663515281111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9969747667719109010187407 14954621501578663515281111)
  ·
    refine ⟨22431932252367995272921667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14954621501578663515281111 22431932252367995272921667)
    ·
      refine ⟨33647898378551992909382501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22431932252367995272921667 33647898378551992909382501)
      ·
        refine ⟨6308980945978498670509219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33647898378551992909382501 6308980945978498670509219)
        ·
          refine ⟨9463471418967748005763829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6308980945978498670509219 9463471418967748005763829)
          ·
            refine ⟨887200445528226375540359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9463471418967748005763829 887200445528226375540359)
            ·
              refine ⟨1330800668292339563310539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 887200445528226375540359 1330800668292339563310539)
              ·
                refine ⟨1996201002438509344965809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1330800668292339563310539 1996201002438509344965809)
                ·
                  refine ⟨1497150751828882008724357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1996201002438509344965809 1497150751828882008724357)
                  ·
                    refine ⟨280715765967915376635817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1497150751828882008724357 280715765967915376635817)
                    ·
                      refine ⟨210536824475936532476863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 280715765967915376635817 210536824475936532476863)
                      ·
                        rfl

theorem cell23_410019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 4, 2].length) (baseStart_410019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410019 prefixEnd_410019 := by exact prefixLift 410019
  have htrace : WordTrace (prefixWord ++ tailWord_410019) baseStart_410019 baseEnd_410019 := by
    simpa [prefixWord, tailWord_410019, baseEnd_410019] using wordTrace_append hprefix tailTrace_410019
  have hstable : (prefixWord ++ tailWord_410019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410019).length < 2 ^ (prefixWord ++ tailWord_410019).sum := by decide
  have hdescent : baseEnd_410019 < baseStart_410019 := by decide
  rcases family_descends (prefixWord ++ tailWord_410019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410039 : List Nat := [1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 3]
def baseStart_410039 : Nat := 118140960795 + 410039 * 2 ^ 59
def prefixEnd_410039 : Nat := 4983230072969 + 3 ^ 40 * 410039 * 2
def baseEnd_410039 : Nat := 210547094089026454226771

theorem tailTrace_410039 : CollatzResearch.WordTrace tailWord_410039 prefixEnd_410039 210547094089026454226771 := by
  unfold tailWord_410039
  simp only [CollatzResearch.WordTrace]
  refine ⟨14955350961506206931009171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9970233974337471287339447 14955350961506206931009171)
  ·
    refine ⟨22433026442259310396513757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14955350961506206931009171 22433026442259310396513757)
    ·
      refine ⟨8412384915847241398692659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22433026442259310396513757 8412384915847241398692659)
      ·
        refine ⟨12618577373770862098038989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8412384915847241398692659 12618577373770862098038989)
        ·
          refine ⟨4731966515164073286764621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12618577373770862098038989 4731966515164073286764621)
          ·
            refine ⟨1774487443186527482536733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4731966515164073286764621 1774487443186527482536733)
            ·
              refine ⟨665432791194947805951275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1774487443186527482536733 665432791194947805951275)
              ·
                refine ⟨998149186792421708926913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 665432791194947805951275 998149186792421708926913)
                ·
                  refine ⟨748611890094316281695185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 998149186792421708926913 748611890094316281695185)
                  ·
                    refine ⟨561458917570737211271389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 748611890094316281695185 561458917570737211271389)
                    ·
                      refine ⟨210547094089026454226771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 561458917570737211271389 210547094089026454226771)
                      ·
                        rfl

theorem cell23_410039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 3].length) (baseStart_410039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410039 prefixEnd_410039 := by exact prefixLift 410039
  have htrace : WordTrace (prefixWord ++ tailWord_410039) baseStart_410039 baseEnd_410039 := by
    simpa [prefixWord, tailWord_410039, baseEnd_410039] using wordTrace_append hprefix tailTrace_410039
  have hstable : (prefixWord ++ tailWord_410039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410039).length < 2 ^ (prefixWord ++ tailWord_410039).sum := by decide
  have hdescent : baseEnd_410039 < baseStart_410039 := by decide
  rcases family_descends (prefixWord ++ tailWord_410039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410046 : List Nat := [4, 2, 1, 1, 1, 1, 3, 5, 1, 4]
def baseStart_410046 : Nat := 118140960795 + 410046 * 2 ^ 59
def prefixEnd_410046 : Nat := 4983230072969 + 3 ^ 40 * 410046 * 2
def baseEnd_410046 : Nat := 70183562817869308946413

theorem tailTrace_410046 : CollatzResearch.WordTrace tailWord_410046 prefixEnd_410046 70183562817869308946413 := by
  unfold tailWord_410046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1869450784060105890814249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9970404181653898084342661 1869450784060105890814249)
  ·
    refine ⟨1402088088045079418110687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1869450784060105890814249 1402088088045079418110687)
    ·
      refine ⟨2103132132067619127166031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1402088088045079418110687 2103132132067619127166031)
      ·
        refine ⟨3154698198101428690749047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2103132132067619127166031 3154698198101428690749047)
        ·
          refine ⟨4732047297152143036123571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3154698198101428690749047 4732047297152143036123571)
          ·
            refine ⟨7098070945728214554185357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4732047297152143036123571 7098070945728214554185357)
            ·
              refine ⟨2661776604648080457819509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7098070945728214554185357 2661776604648080457819509)
              ·
                refine ⟨249541556685757542920579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2661776604648080457819509 249541556685757542920579)
                ·
                  refine ⟨374312335028636314380869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249541556685757542920579 374312335028636314380869)
                  ·
                    refine ⟨70183562817869308946413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 374312335028636314380869 70183562817869308946413)
                    ·
                      rfl

theorem cell23_410046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_410046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410046 prefixEnd_410046 := by exact prefixLift 410046
  have htrace : WordTrace (prefixWord ++ tailWord_410046) baseStart_410046 baseEnd_410046 := by
    simpa [prefixWord, tailWord_410046, baseEnd_410046] using wordTrace_append hprefix tailTrace_410046
  have hstable : (prefixWord ++ tailWord_410046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410046).length < 2 ^ (prefixWord ++ tailWord_410046).sum := by decide
  have hdescent : baseEnd_410046 < baseStart_410046 := by decide
  rcases family_descends (prefixWord ++ tailWord_410046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410079 : List Nat := [1, 1, 2, 3, 3, 2, 1, 2, 1, 5, 2]
def baseStart_410079 : Nat := 118140960795 + 410079 * 2 ^ 59
def prefixEnd_410079 : Nat := 4983230072969 + 3 ^ 40 * 410079 * 2
def baseEnd_410079 : Nat := 210567633315206297726587

theorem tailTrace_410079 : CollatzResearch.WordTrace tailWord_410079 prefixEnd_410079 210567633315206297726587 := by
  unfold tailWord_410079
  simp only [CollatzResearch.WordTrace]
  refine ⟨14956809881361293762465291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9971206587574195841643527 14956809881361293762465291)
  ·
    refine ⟨22435214822041940643697937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14956809881361293762465291 22435214822041940643697937)
    ·
      refine ⟨16826411116531455482773453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22435214822041940643697937 16826411116531455482773453)
      ·
        refine ⟨6309904168699295806040045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16826411116531455482773453 6309904168699295806040045)
        ·
          refine ⟨2366214063262235927265017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6309904168699295806040045 2366214063262235927265017)
          ·
            refine ⟨1774660547446676945448763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2366214063262235927265017 1774660547446676945448763)
            ·
              refine ⟨2661990821170015418173145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1774660547446676945448763 2661990821170015418173145)
              ·
                refine ⟨1996493115877511563629859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2661990821170015418173145 1996493115877511563629859)
                ·
                  refine ⟨2994739673816267345444789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1996493115877511563629859 2994739673816267345444789)
                  ·
                    refine ⟨280756844420275063635449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2994739673816267345444789 280756844420275063635449)
                    ·
                      refine ⟨210567633315206297726587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 280756844420275063635449 210567633315206297726587)
                      ·
                        rfl

theorem cell23_410079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 5, 2].length) (baseStart_410079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410079 prefixEnd_410079 := by exact prefixLift 410079
  have htrace : WordTrace (prefixWord ++ tailWord_410079) baseStart_410079 baseEnd_410079 := by
    simpa [prefixWord, tailWord_410079, baseEnd_410079] using wordTrace_append hprefix tailTrace_410079
  have hstable : (prefixWord ++ tailWord_410079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410079).length < 2 ^ (prefixWord ++ tailWord_410079).sum := by decide
  have hdescent : baseEnd_410079 < baseStart_410079 := by decide
  rcases family_descends (prefixWord ++ tailWord_410079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410109 : List Nat := [1, 4, 1, 1, 1, 3, 1, 5, 1, 1, 4]
def baseStart_410109 : Nat := 118140960795 + 410109 * 2 ^ 59
def prefixEnd_410109 : Nat := 4983230072969 + 3 ^ 40 * 410109 * 2
def baseEnd_410109 : Nat := 210583037734841180351449

theorem tailTrace_410109 : CollatzResearch.WordTrace tailWord_410109 prefixEnd_410109 210583037734841180351449 := by
  unfold tailWord_410109
  simp only [CollatzResearch.WordTrace]
  refine ⟨14957904071252608886057381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9971936047501739257371587 14957904071252608886057381)
  ·
    refine ⟨2804607013359864166135759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14957904071252608886057381 2804607013359864166135759)
    ·
      refine ⟨4206910520039796249203639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2804607013359864166135759 4206910520039796249203639)
      ·
        refine ⟨6310365780059694373805459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4206910520039796249203639 6310365780059694373805459)
        ·
          refine ⟨9465548670089541560708189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6310365780059694373805459 9465548670089541560708189)
          ·
            refine ⟨3549580751283578085265571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9465548670089541560708189 3549580751283578085265571)
            ·
              refine ⟨5324371126925367127898357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3549580751283578085265571 5324371126925367127898357)
              ·
                refine ⟨499159793149253168240471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5324371126925367127898357 499159793149253168240471)
                ·
                  refine ⟨748739689723879752360707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 499159793149253168240471 748739689723879752360707)
                  ·
                    refine ⟨1123109534585819628541061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 748739689723879752360707 1123109534585819628541061)
                    ·
                      refine ⟨210583037734841180351449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1123109534585819628541061 210583037734841180351449)
                      ·
                        rfl

theorem cell23_410109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_410109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410109 prefixEnd_410109 := by exact prefixLift 410109
  have htrace : WordTrace (prefixWord ++ tailWord_410109) baseStart_410109 baseEnd_410109 := by
    simpa [prefixWord, tailWord_410109, baseEnd_410109] using wordTrace_append hprefix tailTrace_410109
  have hstable : (prefixWord ++ tailWord_410109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410109).length < 2 ^ (prefixWord ++ tailWord_410109).sum := by decide
  have hdescent : baseEnd_410109 < baseStart_410109 := by decide
  rcases family_descends (prefixWord ++ tailWord_410109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410122 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 3, 1, 6]
def baseStart_410122 : Nat := 118140960795 + 410122 * 2 ^ 59
def prefixEnd_410122 : Nat := 4983230072969 + 3 ^ 40 * 410122 * 2
def baseEnd_410122 : Nat := 210589712983349629488889

theorem tailTrace_410122 : CollatzResearch.WordTrace tailWord_410122 prefixEnd_410122 210589712983349629488889 := by
  unfold tailWord_410122
  simp only [CollatzResearch.WordTrace]
  refine ⟨3739594555051378026570155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9972252146803674737520413 3739594555051378026570155)
  ·
    refine ⟨5609391832577067039855233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3739594555051378026570155 5609391832577067039855233)
    ·
      refine ⟨4207043874432800279891425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5609391832577067039855233 4207043874432800279891425)
      ·
        refine ⟨3155282905824600209918569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4207043874432800279891425 3155282905824600209918569)
        ·
          refine ⟨2366462179368450157438927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3155282905824600209918569 2366462179368450157438927)
          ·
            refine ⟨3549693269052675236158391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2366462179368450157438927 3549693269052675236158391)
            ·
              refine ⟨5324539903579012854237587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3549693269052675236158391 5324539903579012854237587)
              ·
                refine ⟨7986809855368519281356381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5324539903579012854237587 7986809855368519281356381)
                ·
                  refine ⟨2995053695763194730508643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7986809855368519281356381 2995053695763194730508643)
                  ·
                    refine ⟨4492580543644792095762965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2995053695763194730508643 4492580543644792095762965)
                    ·
                      refine ⟨210589712983349629488889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4492580543644792095762965 210589712983349629488889)
                      ·
                        rfl

theorem cell23_410122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_410122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410122 prefixEnd_410122 := by exact prefixLift 410122
  have htrace : WordTrace (prefixWord ++ tailWord_410122) baseStart_410122 baseEnd_410122 := by
    simpa [prefixWord, tailWord_410122, baseEnd_410122] using wordTrace_append hprefix tailTrace_410122
  have hstable : (prefixWord ++ tailWord_410122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410122).length < 2 ^ (prefixWord ++ tailWord_410122).sum := by decide
  have hdescent : baseEnd_410122 < baseStart_410122 := by decide
  rcases family_descends (prefixWord ++ tailWord_410122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410136 : List Nat := [2, 1, 2, 3, 3, 2, 1, 3, 2, 4]
def baseStart_410136 : Nat := 118140960795 + 410136 * 2 ^ 59
def prefixEnd_410136 : Nat := 4983230072969 + 3 ^ 40 * 410136 * 2
def baseEnd_410136 : Nat := 70198967237504191571275

theorem tailTrace_410136 : CollatzResearch.WordTrace tailWord_410136 prefixEnd_410136 70198967237504191571275 := by
  unfold tailWord_410136
  simp only [CollatzResearch.WordTrace]
  refine ⟨7479444421077396248645131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9972592561436528331526841 7479444421077396248645131)
  ·
    refine ⟨11219166631616094372967697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7479444421077396248645131 11219166631616094372967697)
    ·
      refine ⟨8414374973712070779725773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11219166631616094372967697 8414374973712070779725773)
      ·
        refine ⟨3155390615142026542397165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8414374973712070779725773 3155390615142026542397165)
        ·
          refine ⟨1183271480678259953398937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3155390615142026542397165 1183271480678259953398937)
          ·
            refine ⟨887453610508694965049203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1183271480678259953398937 887453610508694965049203)
            ·
              refine ⟨1331180415763042447573805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 887453610508694965049203 1331180415763042447573805)
              ·
                refine ⟨499192655911140917840177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1331180415763042447573805 499192655911140917840177)
                ·
                  refine ⟨374394491933355688380133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 499192655911140917840177 374394491933355688380133)
                  ·
                    refine ⟨70198967237504191571275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 374394491933355688380133 70198967237504191571275)
                    ·
                      rfl

theorem cell23_410136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 2, 4].length) (baseStart_410136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410136 prefixEnd_410136 := by exact prefixLift 410136
  have htrace : WordTrace (prefixWord ++ tailWord_410136) baseStart_410136 baseEnd_410136 := by
    simpa [prefixWord, tailWord_410136, baseEnd_410136] using wordTrace_append hprefix tailTrace_410136
  have hstable : (prefixWord ++ tailWord_410136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410136).length < 2 ^ (prefixWord ++ tailWord_410136).sum := by decide
  have hdescent : baseEnd_410136 < baseStart_410136 := by decide
  rcases family_descends (prefixWord ++ tailWord_410136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410157 : List Nat := [1, 5, 4, 1, 1, 1, 3, 1, 1, 5]
def baseStart_410157 : Nat := 118140960795 + 410157 * 2 ^ 59
def prefixEnd_410157 : Nat := 4983230072969 + 3 ^ 40 * 410157 * 2
def baseEnd_410157 : Nat := 70202561602085664183743

theorem tailTrace_410157 : CollatzResearch.WordTrace tailWord_410157 prefixEnd_410157 70202561602085664183743 := by
  unfold tailWord_410157
  simp only [CollatzResearch.WordTrace]
  refine ⟨14959654775078713083804725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9973103183385808722536483 14959654775078713083804725)
  ·
    refine ⟨1402467635163629351606693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14959654775078713083804725 1402467635163629351606693)
    ·
      refine ⟨262962681593180503426255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1402467635163629351606693 262962681593180503426255)
      ·
        refine ⟨394444022389770755139383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262962681593180503426255 394444022389770755139383)
        ·
          refine ⟨591666033584656132709075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394444022389770755139383 591666033584656132709075)
          ·
            refine ⟨887499050376984199063613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591666033584656132709075 887499050376984199063613)
            ·
              refine ⟨332812143891369074648855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 887499050376984199063613 332812143891369074648855)
              ·
                refine ⟨499218215837053611973283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332812143891369074648855 499218215837053611973283)
                ·
                  refine ⟨748827323755580417959925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 499218215837053611973283 748827323755580417959925)
                  ·
                    refine ⟨70202561602085664183743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 748827323755580417959925 70202561602085664183743)
                    ·
                      rfl

theorem cell23_410157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_410157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410157 prefixEnd_410157 := by exact prefixLift 410157
  have htrace : WordTrace (prefixWord ++ tailWord_410157) baseStart_410157 baseEnd_410157 := by
    simpa [prefixWord, tailWord_410157, baseEnd_410157] using wordTrace_append hprefix tailTrace_410157
  have hstable : (prefixWord ++ tailWord_410157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410157).length < 2 ^ (prefixWord ++ tailWord_410157).sum := by decide
  have hdescent : baseEnd_410157 < baseStart_410157 := by decide
  rcases family_descends (prefixWord ++ tailWord_410157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410176 : List Nat := [2, 1, 1, 2, 2, 2, 3, 4, 2, 1, 3]
def baseStart_410176 : Nat := 118140960795 + 410176 * 2 ^ 59
def prefixEnd_410176 : Nat := 4983230072969 + 3 ^ 40 * 410176 * 2
def baseEnd_410176 : Nat := 210617440938692418213641

theorem tailTrace_410176 : CollatzResearch.WordTrace tailWord_410176 prefixEnd_410176 210617440938692418213641 := by
  unfold tailWord_410176
  simp only [CollatzResearch.WordTrace]
  refine ⟨7480173881004939664373191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9973565174673252885830921 7480173881004939664373191)
  ·
    refine ⟨11220260821507409496559787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7480173881004939664373191 11220260821507409496559787)
    ·
      refine ⟨16830391232261114244839681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11220260821507409496559787 16830391232261114244839681)
      ·
        refine ⟨12622793424195835683629761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16830391232261114244839681 12622793424195835683629761)
        ·
          refine ⟨9467095068146876762722321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12622793424195835683629761 9467095068146876762722321)
          ·
            refine ⟨7100321301110157572041741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9467095068146876762722321 7100321301110157572041741)
            ·
              refine ⟨2662620487916309089515653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7100321301110157572041741 2662620487916309089515653)
              ·
                refine ⟨499241341484307954284185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2662620487916309089515653 499241341484307954284185)
                ·
                  refine ⟨374431006113230965713139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 499241341484307954284185 374431006113230965713139)
                  ·
                    refine ⟨561646509169846448569709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 374431006113230965713139 561646509169846448569709)
                    ·
                      refine ⟨210617440938692418213641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 561646509169846448569709 210617440938692418213641)
                      ·
                        rfl

theorem cell23_410176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 2, 1, 3].length) (baseStart_410176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410176 prefixEnd_410176 := by exact prefixLift 410176
  have htrace : WordTrace (prefixWord ++ tailWord_410176) baseStart_410176 baseEnd_410176 := by
    simpa [prefixWord, tailWord_410176, baseEnd_410176] using wordTrace_append hprefix tailTrace_410176
  have hstable : (prefixWord ++ tailWord_410176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410176).length < 2 ^ (prefixWord ++ tailWord_410176).sum := by decide
  have hdescent : baseEnd_410176 < baseStart_410176 := by decide
  rcases family_descends (prefixWord ++ tailWord_410176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410177 : List Nat := [1, 2, 5, 1, 1, 2, 4, 2, 1, 2, 2]
def baseStart_410177 : Nat := 118140960795 + 410177 * 2 ^ 59
def prefixEnd_410177 : Nat := 4983230072969 + 3 ^ 40 * 410177 * 2
def baseEnd_410177 : Nat := 210617954419346914301137

theorem tailTrace_410177 : CollatzResearch.WordTrace tailWord_410177 prefixEnd_410177 210617954419346914301137 := by
  unfold tailWord_410177
  simp only [CollatzResearch.WordTrace]
  refine ⟨14960384235006256499532785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9973589490004170999688523 14960384235006256499532785)
  ·
    refine ⟨11220288176254692374649589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14960384235006256499532785 11220288176254692374649589)
    ·
      refine ⟨1051902016523877410123399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11220288176254692374649589 1051902016523877410123399)
      ·
        refine ⟨1577853024785816115185099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1051902016523877410123399 1577853024785816115185099)
        ·
          refine ⟨2366779537178724172777649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1577853024785816115185099 2366779537178724172777649)
          ·
            refine ⟨1775084652884043129583237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2366779537178724172777649 1775084652884043129583237)
            ·
              refine ⟨332828372415758086796857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1775084652884043129583237 332828372415758086796857)
              ·
                refine ⟨249621279311818565097643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 332828372415758086796857 249621279311818565097643)
                ·
                  refine ⟨374431918967727847646465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249621279311818565097643 374431918967727847646465)
                  ·
                    refine ⟨280823939225795885734849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 374431918967727847646465 280823939225795885734849)
                    ·
                      refine ⟨210617954419346914301137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 280823939225795885734849 210617954419346914301137)
                      ·
                        rfl

theorem cell23_410177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_410177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410177 prefixEnd_410177 := by exact prefixLift 410177
  have htrace : WordTrace (prefixWord ++ tailWord_410177) baseStart_410177 baseEnd_410177 := by
    simpa [prefixWord, tailWord_410177, baseEnd_410177] using wordTrace_append hprefix tailTrace_410177
  have hstable : (prefixWord ++ tailWord_410177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410177).length < 2 ^ (prefixWord ++ tailWord_410177).sum := by decide
  have hdescent : baseEnd_410177 < baseStart_410177 := by decide
  rcases family_descends (prefixWord ++ tailWord_410177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410186 : List Nat := [3, 1, 2, 1, 1, 4, 1, 2, 3, 3, 2]
def baseStart_410186 : Nat := 118140960795 + 410186 * 2 ^ 59
def prefixEnd_410186 : Nat := 4983230072969 + 3 ^ 40 * 410186 * 2
def baseEnd_410186 : Nat := 210622575745237379088595

theorem tailTrace_410186 : CollatzResearch.WordTrace tailWord_410186 prefixEnd_410186 210622575745237379088595 := by
  unfold tailWord_410186
  simp only [CollatzResearch.WordTrace]
  refine ⟨3740178122993412759152603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9973808327982434024406941 3740178122993412759152603)
  ·
    refine ⟨5610267184490119138728905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3740178122993412759152603 5610267184490119138728905)
    ·
      refine ⟨4207700388367589354046679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5610267184490119138728905 4207700388367589354046679)
      ·
        refine ⟨6311550582551384031070019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4207700388367589354046679 6311550582551384031070019)
        ·
          refine ⟨9467325873827076046605029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6311550582551384031070019 9467325873827076046605029)
          ·
            refine ⟨1775123601342576758738443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9467325873827076046605029 1775123601342576758738443)
            ·
              refine ⟨2662685402013865138107665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1775123601342576758738443 2662685402013865138107665)
              ·
                refine ⟨1997014051510398853580749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2662685402013865138107665 1997014051510398853580749)
                ·
                  refine ⟨748880269316399570092781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1997014051510398853580749 748880269316399570092781)
                  ·
                    refine ⟨280830100993649838784793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 748880269316399570092781 280830100993649838784793)
                    ·
                      refine ⟨210622575745237379088595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 280830100993649838784793 210622575745237379088595)
                      ·
                        rfl

theorem cell23_410186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 3, 3, 2].length) (baseStart_410186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410186 prefixEnd_410186 := by exact prefixLift 410186
  have htrace : WordTrace (prefixWord ++ tailWord_410186) baseStart_410186 baseEnd_410186 := by
    simpa [prefixWord, tailWord_410186, baseEnd_410186] using wordTrace_append hprefix tailTrace_410186
  have hstable : (prefixWord ++ tailWord_410186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410186).length < 2 ^ (prefixWord ++ tailWord_410186).sum := by decide
  have hdescent : baseEnd_410186 < baseStart_410186 := by decide
  rcases family_descends (prefixWord ++ tailWord_410186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410232 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 1, 2, 7]
def baseStart_410232 : Nat := 118140960795 + 410232 * 2 ^ 59
def prefixEnd_410232 : Nat := 4983230072969 + 3 ^ 40 * 410232 * 2
def baseEnd_410232 : Nat := 210646195855344199113383

theorem tailTrace_410232 : CollatzResearch.WordTrace tailWord_410232 prefixEnd_410232 210646195855344199113383 := by
  unfold tailWord_410232
  simp only [CollatzResearch.WordTrace]
  refine ⟨7481195124903500446392475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9974926833204667261856633 7481195124903500446392475)
  ·
    refine ⟨11221792687355250669588713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7481195124903500446392475 11221792687355250669588713)
    ·
      refine ⟨8416344515516438002191535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11221792687355250669588713 8416344515516438002191535)
      ·
        refine ⟨12624516773274657003287303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8416344515516438002191535 12624516773274657003287303)
        ·
          refine ⟨18936775159911985504930955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12624516773274657003287303 18936775159911985504930955)
          ·
            refine ⟨28405162739867978257396433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18936775159911985504930955 28405162739867978257396433)
            ·
              refine ⟨21303872054900983693047325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28405162739867978257396433 21303872054900983693047325)
              ·
                refine ⟨7988952020587868884892747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21303872054900983693047325 7988952020587868884892747)
                ·
                  refine ⟨11983428030881803327339121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7988952020587868884892747 11983428030881803327339121)
                  ·
                    refine ⟨8987571023161352495504341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11983428030881803327339121 8987571023161352495504341)
                    ·
                      refine ⟨210646195855344199113383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 8987571023161352495504341 210646195855344199113383)
                      ·
                        rfl

theorem cell23_410232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_410232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410232 prefixEnd_410232 := by exact prefixLift 410232
  have htrace : WordTrace (prefixWord ++ tailWord_410232) baseStart_410232 baseEnd_410232 := by
    simpa [prefixWord, tailWord_410232, baseEnd_410232] using wordTrace_append hprefix tailTrace_410232
  have hstable : (prefixWord ++ tailWord_410232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410232).length < 2 ^ (prefixWord ++ tailWord_410232).sum := by decide
  have hdescent : baseEnd_410232 < baseStart_410232 := by decide
  rcases family_descends (prefixWord ++ tailWord_410232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410233 : List Nat := [1, 2, 1, 3, 3, 3, 1, 1, 4, 2, 2]
def baseStart_410233 : Nat := 118140960795 + 410233 * 2 ^ 59
def prefixEnd_410233 : Nat := 4983230072969 + 3 ^ 40 * 410233 * 2
def baseEnd_410233 : Nat := 210646709335998695200879

theorem tailTrace_410233 : CollatzResearch.WordTrace tailWord_410233 prefixEnd_410233 210646709335998695200879 := by
  unfold tailWord_410233
  simp only [CollatzResearch.WordTrace]
  refine ⟨14962426722803378063571353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9974951148535585375714235 14962426722803378063571353)
  ·
    refine ⟨11221820042102533547678515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14962426722803378063571353 11221820042102533547678515)
    ·
      refine ⟨16832730063153800321517773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11221820042102533547678515 16832730063153800321517773)
      ·
        refine ⟨6312273773682675120569165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16832730063153800321517773 6312273773682675120569165)
        ·
          refine ⟨2367102665131003170213437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6312273773682675120569165 2367102665131003170213437)
          ·
            refine ⟨887663499424126188830039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2367102665131003170213437 887663499424126188830039)
            ·
              refine ⟨1331495249136189283245059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 887663499424126188830039 1331495249136189283245059)
              ·
                refine ⟨1997242873704283924867589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1331495249136189283245059 1997242873704283924867589)
                ·
                  refine ⟨374483038819553235912673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1997242873704283924867589 374483038819553235912673)
                  ·
                    refine ⟨280862279114664926934505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 374483038819553235912673 280862279114664926934505)
                    ·
                      refine ⟨210646709335998695200879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 280862279114664926934505 210646709335998695200879)
                      ·
                        rfl

theorem cell23_410233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 2, 2].length) (baseStart_410233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410233 prefixEnd_410233 := by exact prefixLift 410233
  have htrace : WordTrace (prefixWord ++ tailWord_410233) baseStart_410233 baseEnd_410233 := by
    simpa [prefixWord, tailWord_410233, baseEnd_410233] using wordTrace_append hprefix tailTrace_410233
  have hstable : (prefixWord ++ tailWord_410233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410233).length < 2 ^ (prefixWord ++ tailWord_410233).sum := by decide
  have hdescent : baseEnd_410233 < baseStart_410233 := by decide
  rcases family_descends (prefixWord ++ tailWord_410233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410250 : List Nat := [3, 1, 2, 3, 3, 2, 1, 1, 1, 4, 2]
def baseStart_410250 : Nat := 118140960795 + 410250 * 2 ^ 59
def prefixEnd_410250 : Nat := 4983230072969 + 3 ^ 40 * 410250 * 2
def baseEnd_410250 : Nat := 210655438507125128688301

theorem tailTrace_410250 : CollatzResearch.WordTrace tailWord_410250 prefixEnd_410250 210655438507125128688301 := by
  unfold tailWord_410250
  simp only [CollatzResearch.WordTrace]
  refine ⟨3740761690935447491735051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9975364509161193311293469 3740761690935447491735051)
  ·
    refine ⟨5611142536403171237602577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3740761690935447491735051 5611142536403171237602577)
    ·
      refine ⟨4208356902302378428201933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5611142536403171237602577 4208356902302378428201933)
      ·
        refine ⟨1578133838363391910575725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4208356902302378428201933 1578133838363391910575725)
        ·
          refine ⟨591800189386271966465897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1578133838363391910575725 591800189386271966465897)
          ·
            refine ⟨443850142039703974849423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 591800189386271966465897 443850142039703974849423)
            ·
              refine ⟨665775213059555962274135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443850142039703974849423 665775213059555962274135)
              ·
                refine ⟨998662819589333943411203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 665775213059555962274135 998662819589333943411203)
                ·
                  refine ⟨1497994229384000915116805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 998662819589333943411203 1497994229384000915116805)
                  ·
                    refine ⟨280873918009500171584401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1497994229384000915116805 280873918009500171584401)
                    ·
                      refine ⟨210655438507125128688301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 280873918009500171584401 210655438507125128688301)
                      ·
                        rfl

theorem cell23_410250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_410250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410250 prefixEnd_410250 := by exact prefixLift 410250
  have htrace : WordTrace (prefixWord ++ tailWord_410250) baseStart_410250 baseEnd_410250 := by
    simpa [prefixWord, tailWord_410250, baseEnd_410250] using wordTrace_append hprefix tailTrace_410250
  have hstable : (prefixWord ++ tailWord_410250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410250).length < 2 ^ (prefixWord ++ tailWord_410250).sum := by decide
  have hdescent : baseEnd_410250 < baseStart_410250 := by decide
  rcases family_descends (prefixWord ++ tailWord_410250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410269 : List Nat := [1, 4, 2, 1, 1, 1, 4, 1, 1, 7]
def baseStart_410269 : Nat := 118140960795 + 410269 * 2 ^ 59
def prefixEnd_410269 : Nat := 4983230072969 + 3 ^ 40 * 410269 * 2
def baseEnd_410269 : Nat := 70221731546520184783571

theorem tailTrace_410269 : CollatzResearch.WordTrace tailWord_410269 prefixEnd_410269 70221731546520184783571 := by
  unfold tailWord_410269
  simp only [CollatzResearch.WordTrace]
  refine ⟨14963739750672956211881861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9975826500448637474587907 14963739750672956211881861)
  ·
    refine ⟨2805701203251179289727849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14963739750672956211881861 2805701203251179289727849)
    ·
      refine ⟨2104275902438384467295887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2805701203251179289727849 2104275902438384467295887)
      ·
        refine ⟨3156413853657576700943831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2104275902438384467295887 3156413853657576700943831)
        ·
          refine ⟨4734620780486365051415747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3156413853657576700943831 4734620780486365051415747)
          ·
            refine ⟨7101931170729547577123621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4734620780486365051415747 7101931170729547577123621)
            ·
              refine ⟨1331612094511790170710679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7101931170729547577123621 1331612094511790170710679)
              ·
                refine ⟨1997418141767685256066019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1331612094511790170710679 1997418141767685256066019)
                ·
                  refine ⟨2996127212651527884099029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1997418141767685256066019 2996127212651527884099029)
                  ·
                    refine ⟨70221731546520184783571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2996127212651527884099029 70221731546520184783571)
                    ·
                      rfl

theorem cell23_410269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_410269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410269 prefixEnd_410269 := by exact prefixLift 410269
  have htrace : WordTrace (prefixWord ++ tailWord_410269) baseStart_410269 baseEnd_410269 := by
    simpa [prefixWord, tailWord_410269, baseEnd_410269] using wordTrace_append hprefix tailTrace_410269
  have hstable : (prefixWord ++ tailWord_410269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410269).length < 2 ^ (prefixWord ++ tailWord_410269).sum := by decide
  have hdescent : baseEnd_410269 < baseStart_410269 := by decide
  rcases family_descends (prefixWord ++ tailWord_410269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410350 : List Nat := [4, 1, 2, 1, 1, 4, 1, 4, 1, 4]
def baseStart_410350 : Nat := 118140960795 + 410350 * 2 ^ 59
def prefixEnd_410350 : Nat := 4983230072969 + 3 ^ 40 * 410350 * 2
def baseEnd_410350 : Nat := 70235595524191579145947

theorem tailTrace_410350 : CollatzResearch.WordTrace tailWord_410350 prefixEnd_410350 70235595524191579145947 := by
  unfold tailWord_410350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1870836757922438380697563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9977796042253004697053669 1870836757922438380697563)
  ·
    refine ⟨2806255136883657571046345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1870836757922438380697563 2806255136883657571046345)
    ·
      refine ⟨2104691352662743178284759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2806255136883657571046345 2104691352662743178284759)
      ·
        refine ⟨3157037028994114767427139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2104691352662743178284759 3157037028994114767427139)
        ·
          refine ⟨4735555543491172151140709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3157037028994114767427139 4735555543491172151140709)
          ·
            refine ⟨887916664404594778338883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4735555543491172151140709 887916664404594778338883)
            ·
              refine ⟨1331874996606892167508325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 887916664404594778338883 1331874996606892167508325)
              ·
                refine ⟨249726561863792281407811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1331874996606892167508325 249726561863792281407811)
                ·
                  refine ⟨374589842795688422111717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249726561863792281407811 374589842795688422111717)
                  ·
                    refine ⟨70235595524191579145947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 374589842795688422111717 70235595524191579145947)
                    ·
                      rfl

theorem cell23_410350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_410350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410350 prefixEnd_410350 := by exact prefixLift 410350
  have htrace : WordTrace (prefixWord ++ tailWord_410350) baseStart_410350 baseEnd_410350 := by
    simpa [prefixWord, tailWord_410350, baseEnd_410350] using wordTrace_append hprefix tailTrace_410350
  have hstable : (prefixWord ++ tailWord_410350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410350).length < 2 ^ (prefixWord ++ tailWord_410350).sum := by decide
  have hdescent : baseEnd_410350 < baseStart_410350 := by decide
  rcases family_descends (prefixWord ++ tailWord_410350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410369 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_410369 : Nat := 118140960795 + 410369 * 2 ^ 59
def prefixEnd_410369 : Nat := 4983230072969 + 3 ^ 40 * 410369 * 2
def baseEnd_410369 : Nat := 210716542705010163100253

theorem tailTrace_410369 : CollatzResearch.WordTrace tailWord_410369 prefixEnd_410369 210716542705010163100253 := by
  unfold tailWord_410369
  simp only [CollatzResearch.WordTrace]
  refine ⟨14967387050310673290522161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9978258033540448860348107 14967387050310673290522161)
  ·
    refine ⟨11225540287733004967891621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14967387050310673290522161 11225540287733004967891621)
    ·
      refine ⟨2104788803949938431479679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11225540287733004967891621 2104788803949938431479679)
      ·
        refine ⟨3157183205924907647219519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2104788803949938431479679 3157183205924907647219519)
        ·
          refine ⟨4735774808887361470829279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3157183205924907647219519 4735774808887361470829279)
          ·
            refine ⟨7103662213331042206243919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4735774808887361470829279 7103662213331042206243919)
            ·
              refine ⟨10655493319996563309365879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7103662213331042206243919 10655493319996563309365879)
              ·
                refine ⟨15983239979994844964048819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10655493319996563309365879 15983239979994844964048819)
                ·
                  refine ⟨23974859969992267446073229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15983239979994844964048819 23974859969992267446073229)
                  ·
                    refine ⟨8990572488747100292277461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23974859969992267446073229 8990572488747100292277461)
                    ·
                      refine ⟨210716542705010163100253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 8990572488747100292277461 210716542705010163100253)
                      ·
                        rfl

theorem cell23_410369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_410369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410369 prefixEnd_410369 := by exact prefixLift 410369
  have htrace : WordTrace (prefixWord ++ tailWord_410369) baseStart_410369 baseEnd_410369 := by
    simpa [prefixWord, tailWord_410369, baseEnd_410369] using wordTrace_append hprefix tailTrace_410369
  have hstable : (prefixWord ++ tailWord_410369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410369).length < 2 ^ (prefixWord ++ tailWord_410369).sum := by decide
  have hdescent : baseEnd_410369 < baseStart_410369 := by decide
  rcases family_descends (prefixWord ++ tailWord_410369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410376 : List Nat := [2, 1, 3, 2, 2, 2, 2, 1, 3, 5]
def baseStart_410376 : Nat := 118140960795 + 410376 * 2 ^ 59
def prefixEnd_410376 : Nat := 4983230072969 + 3 ^ 40 * 410376 * 2
def baseEnd_410376 : Nat := 70240045689863878570907

theorem tailTrace_410376 : CollatzResearch.WordTrace tailWord_410376 prefixEnd_410376 70240045689863878570907 := by
  unfold tailWord_410376
  simp only [CollatzResearch.WordTrace]
  refine ⟨7483821180642656743013491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9978428240856875657351321 7483821180642656743013491)
  ·
    refine ⟨11225731770963985114520237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7483821180642656743013491 11225731770963985114520237)
    ·
      refine ⟨4209649414111494417945089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11225731770963985114520237 4209649414111494417945089)
      ·
        refine ⟨3157237060583620813458817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4209649414111494417945089 3157237060583620813458817)
        ·
          refine ⟨2367927795437715610094113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3157237060583620813458817 2367927795437715610094113)
          ·
            refine ⟨1775945846578286707570585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2367927795437715610094113 1775945846578286707570585)
            ·
              refine ⟨1331959384933715030677939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1775945846578286707570585 1331959384933715030677939)
              ·
                refine ⟨1997939077400572546016909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1331959384933715030677939 1997939077400572546016909)
                ·
                  refine ⟨749227154025214704756341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1997939077400572546016909 749227154025214704756341)
                  ·
                    refine ⟨70240045689863878570907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 749227154025214704756341 70240045689863878570907)
                    ·
                      rfl

theorem cell23_410376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_410376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410376 prefixEnd_410376 := by exact prefixLift 410376
  have htrace : WordTrace (prefixWord ++ tailWord_410376) baseStart_410376 baseEnd_410376 := by
    simpa [prefixWord, tailWord_410376, baseEnd_410376] using wordTrace_append hprefix tailTrace_410376
  have hstable : (prefixWord ++ tailWord_410376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410376).length < 2 ^ (prefixWord ++ tailWord_410376).sum := by decide
  have hdescent : baseEnd_410376 < baseStart_410376 := by decide
  rcases family_descends (prefixWord ++ tailWord_410376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410397 : List Nat := [1, 4, 2, 4, 2, 1, 1, 2, 6]
def baseStart_410397 : Nat := 118140960795 + 410397 * 2 ^ 59
def prefixEnd_410397 : Nat := 4983230072969 + 3 ^ 40 * 410397 * 2
def baseEnd_410397 : Nat := 23414546684815117061125

theorem tailTrace_410397 : CollatzResearch.WordTrace tailWord_410397 prefixEnd_410397 23414546684815117061125 := by
  unfold tailWord_410397
  simp only [CollatzResearch.WordTrace]
  refine ⟨14968408294209234072541445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9978938862806156048360963 14968408294209234072541445)
  ·
    refine ⟨2806576555164231388601521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14968408294209234072541445 2806576555164231388601521)
    ·
      refine ⟨2104932416373173541451141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2806576555164231388601521 2104932416373173541451141)
      ·
        refine ⟨394674828069970039022089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2104932416373173541451141 394674828069970039022089)
        ·
          refine ⟨296006121052477529266567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394674828069970039022089 296006121052477529266567)
          ·
            refine ⟨444009181578716293899851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296006121052477529266567 444009181578716293899851)
            ·
              refine ⟨666013772368074440849777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 444009181578716293899851 666013772368074440849777)
              ·
                refine ⟨499510329276055830637333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 666013772368074440849777 499510329276055830637333)
                ·
                  refine ⟨23414546684815117061125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 499510329276055830637333 23414546684815117061125)
                  ·
                    rfl

theorem cell23_410397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 6].length) (baseStart_410397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410397 prefixEnd_410397 := by exact prefixLift 410397
  have htrace : WordTrace (prefixWord ++ tailWord_410397) baseStart_410397 baseEnd_410397 := by
    simpa [prefixWord, tailWord_410397, baseEnd_410397] using wordTrace_append hprefix tailTrace_410397
  have hstable : (prefixWord ++ tailWord_410397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410397).length < 2 ^ (prefixWord ++ tailWord_410397).sum := by decide
  have hdescent : baseEnd_410397 < baseStart_410397 := by decide
  rcases family_descends (prefixWord ++ tailWord_410397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410409 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 3, 1, 6]
def baseStart_410409 : Nat := 118140960795 + 410409 * 2 ^ 59
def prefixEnd_410409 : Nat := 4983230072969 + 3 ^ 40 * 410409 * 2
def baseEnd_410409 : Nat := 210737081931190006600069

theorem tailTrace_410409 : CollatzResearch.WordTrace tailWord_410409 prefixEnd_410409 210737081931190006600069 := by
  unfold tailWord_410409
  simp only [CollatzResearch.WordTrace]
  refine ⟨14968845970165760121978281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9979230646777173414652187 14968845970165760121978281)
  ·
    refine ⟨11226634477624320091483711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14968845970165760121978281 11226634477624320091483711)
    ·
      refine ⟨16839951716436480137225567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11226634477624320091483711 16839951716436480137225567)
      ·
        refine ⟨25259927574654720205838351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16839951716436480137225567 25259927574654720205838351)
        ·
          refine ⟨37889891361982080308757527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25259927574654720205838351 37889891361982080308757527)
          ·
            refine ⟨56834837042973120463136291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37889891361982080308757527 56834837042973120463136291)
            ·
              refine ⟨85252255564459680694704437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56834837042973120463136291 85252255564459680694704437)
              ·
                refine ⟨7992398959168095065128541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85252255564459680694704437 7992398959168095065128541)
                ·
                  refine ⟨2997149609688035649423203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7992398959168095065128541 2997149609688035649423203)
                  ·
                    refine ⟨4495724414532053474134805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2997149609688035649423203 4495724414532053474134805)
                    ·
                      refine ⟨210737081931190006600069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4495724414532053474134805 210737081931190006600069)
                      ·
                        rfl

theorem cell23_410409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 1, 6].length) (baseStart_410409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410409 prefixEnd_410409 := by exact prefixLift 410409
  have htrace : WordTrace (prefixWord ++ tailWord_410409) baseStart_410409 baseEnd_410409 := by
    simpa [prefixWord, tailWord_410409, baseEnd_410409] using wordTrace_append hprefix tailTrace_410409
  have hstable : (prefixWord ++ tailWord_410409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410409).length < 2 ^ (prefixWord ++ tailWord_410409).sum := by decide
  have hdescent : baseEnd_410409 < baseStart_410409 := by decide
  rcases family_descends (prefixWord ++ tailWord_410409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410416 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 3]
def baseStart_410416 : Nat := 118140960795 + 410416 * 2 ^ 59
def prefixEnd_410416 : Nat := 4983230072969 + 3 ^ 40 * 410416 * 2
def baseEnd_410416 : Nat := 210740676295771479212537

theorem tailTrace_410416 : CollatzResearch.WordTrace tailWord_410416 prefixEnd_410416 210740676295771479212537 := by
  unfold tailWord_410416
  simp only [CollatzResearch.WordTrace]
  refine ⟨7484550640570200158741551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9979400854093600211655401 7484550640570200158741551)
  ·
    refine ⟨11226825960855300238112327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7484550640570200158741551 11226825960855300238112327)
    ·
      refine ⟨16840238941282950357168491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11226825960855300238112327 16840238941282950357168491)
      ·
        refine ⟨25260358411924425535752737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16840238941282950357168491 25260358411924425535752737)
        ·
          refine ⟨18945268808943319151814553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25260358411924425535752737 18945268808943319151814553)
          ·
            refine ⟨14208951606707489363860915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18945268808943319151814553 14208951606707489363860915)
            ·
              refine ⟨21313427410061234045791373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14208951606707489363860915 21313427410061234045791373)
              ·
                refine ⟨7992535278772962767171765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21313427410061234045791373 7992535278772962767171765)
                ·
                  refine ⟨749300182384965259422353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7992535278772962767171765 749300182384965259422353)
                  ·
                    refine ⟨561975136788723944566765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 749300182384965259422353 561975136788723944566765)
                    ·
                      refine ⟨210740676295771479212537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 561975136788723944566765 210740676295771479212537)
                      ·
                        rfl

theorem cell23_410416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 3].length) (baseStart_410416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410416 prefixEnd_410416 := by exact prefixLift 410416
  have htrace : WordTrace (prefixWord ++ tailWord_410416) baseStart_410416 baseEnd_410416 := by
    simpa [prefixWord, tailWord_410416, baseEnd_410416] using wordTrace_append hprefix tailTrace_410416
  have hstable : (prefixWord ++ tailWord_410416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410416).length < 2 ^ (prefixWord ++ tailWord_410416).sum := by decide
  have hdescent : baseEnd_410416 < baseStart_410416 := by decide
  rcases family_descends (prefixWord ++ tailWord_410416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410463 : List Nat := [1, 1, 2, 3, 1, 3, 1, 3, 4, 1, 3]
def baseStart_410463 : Nat := 118140960795 + 410463 * 2 ^ 59
def prefixEnd_410463 : Nat := 4983230072969 + 3 ^ 40 * 410463 * 2
def baseEnd_410463 : Nat := 210764809886532795324821

theorem tailTrace_410463 : CollatzResearch.WordTrace tailWord_410463 prefixEnd_410463 210764809886532795324821 := by
  unfold tailWord_410463
  simp only [CollatzResearch.WordTrace]
  refine ⟨14970815511970127344444043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9980543674646751562962695 14970815511970127344444043)
  ·
    refine ⟨22456223267955191016666065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14970815511970127344444043 22456223267955191016666065)
    ·
      refine ⟨16842167450966393262499549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22456223267955191016666065 16842167450966393262499549)
      ·
        refine ⟨6315812794112397473437331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16842167450966393262499549 6315812794112397473437331)
        ·
          refine ⟨9473719191168596210155997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6315812794112397473437331 9473719191168596210155997)
          ·
            refine ⟨3552644696688223578808499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9473719191168596210155997 3552644696688223578808499)
            ·
              refine ⟨5328967045032335368212749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3552644696688223578808499 5328967045032335368212749)
              ·
                refine ⟨1998362641887125763079781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5328967045032335368212749 1998362641887125763079781)
                ·
                  refine ⟨374692995353836080577459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1998362641887125763079781 374692995353836080577459)
                  ·
                    refine ⟨562039493030754120866189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 374692995353836080577459 562039493030754120866189)
                    ·
                      refine ⟨210764809886532795324821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 562039493030754120866189 210764809886532795324821)
                      ·
                        rfl

theorem cell23_410463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_410463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410463 prefixEnd_410463 := by exact prefixLift 410463
  have htrace : WordTrace (prefixWord ++ tailWord_410463) baseStart_410463 baseEnd_410463 := by
    simpa [prefixWord, tailWord_410463, baseEnd_410463] using wordTrace_append hprefix tailTrace_410463
  have hstable : (prefixWord ++ tailWord_410463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410463).length < 2 ^ (prefixWord ++ tailWord_410463).sum := by decide
  have hdescent : baseEnd_410463 < baseStart_410463 := by decide
  rcases family_descends (prefixWord ++ tailWord_410463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410464 : List Nat := [2, 1, 1, 3, 3, 1, 5, 2, 1, 2, 2]
def baseStart_410464 : Nat := 118140960795 + 410464 * 2 ^ 59
def prefixEnd_410464 : Nat := 4983230072969 + 3 ^ 40 * 410464 * 2
def baseEnd_410464 : Nat := 210765323367187291412317

theorem tailTrace_410464 : CollatzResearch.WordTrace tailWord_410464 prefixEnd_410464 210765323367187291412317 := by
  unfold tailWord_410464
  simp only [CollatzResearch.WordTrace]
  refine ⟨7485425992483252257615223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9980567989977669676820297 7485425992483252257615223)
  ·
    refine ⟨11228138988724878386422835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7485425992483252257615223 11228138988724878386422835)
    ·
      refine ⟨16842208483087317579634253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11228138988724878386422835 16842208483087317579634253)
      ·
        refine ⟨6315828181157744092362845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16842208483087317579634253 6315828181157744092362845)
        ·
          refine ⟨2368435567934154034636067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6315828181157744092362845 2368435567934154034636067)
          ·
            refine ⟨3552653351901231051954101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2368435567934154034636067 3552653351901231051954101)
            ·
              refine ⟨333061251740740411120697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3552653351901231051954101 333061251740740411120697)
              ·
                refine ⟨249795938805555308340523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333061251740740411120697 249795938805555308340523)
                ·
                  refine ⟨374693908208332962510785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249795938805555308340523 374693908208332962510785)
                  ·
                    refine ⟨281020431156249721883089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 374693908208332962510785 281020431156249721883089)
                    ·
                      refine ⟨210765323367187291412317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 281020431156249721883089 210765323367187291412317)
                      ·
                        rfl

theorem cell23_410464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 1, 2, 2].length) (baseStart_410464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410464 prefixEnd_410464 := by exact prefixLift 410464
  have htrace : WordTrace (prefixWord ++ tailWord_410464) baseStart_410464 baseEnd_410464 := by
    simpa [prefixWord, tailWord_410464, baseEnd_410464] using wordTrace_append hprefix tailTrace_410464
  have hstable : (prefixWord ++ tailWord_410464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410464).length < 2 ^ (prefixWord ++ tailWord_410464).sum := by decide
  have hdescent : baseEnd_410464 < baseStart_410464 := by decide
  rcases family_descends (prefixWord ++ tailWord_410464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410514 : List Nat := [3, 2, 3, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_410514 : Nat := 118140960795 + 410514 * 2 ^ 59
def prefixEnd_410514 : Nat := 4983230072969 + 3 ^ 40 * 410514 * 2
def baseEnd_410514 : Nat := 210790997399912095787087

theorem tailTrace_410514 : CollatzResearch.WordTrace tailWord_410514 prefixEnd_410514 210790997399912095787087 := by
  unfold tailWord_410514
  simp only [CollatzResearch.WordTrace]
  refine ⟨3743168908696340763637649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9981783756523575369700397 3743168908696340763637649)
  ·
    refine ⟨2807376681522255572728237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3743168908696340763637649 2807376681522255572728237)
    ·
      refine ⟨1052766255570845839773089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2807376681522255572728237 1052766255570845839773089)
      ·
        refine ⟨789574691678134379829817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1052766255570845839773089 789574691678134379829817)
        ·
          refine ⟨592181018758600784872363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 789574691678134379829817 592181018758600784872363)
          ·
            refine ⟨888271528137901177308545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592181018758600784872363 888271528137901177308545)
            ·
              refine ⟨666203646103425882981409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 888271528137901177308545 666203646103425882981409)
              ·
                refine ⟨499652734577569412236057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 666203646103425882981409 499652734577569412236057)
                ·
                  refine ⟨374739550933177059177043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 499652734577569412236057 374739550933177059177043)
                  ·
                    refine ⟨562109326399765588765565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 374739550933177059177043 562109326399765588765565)
                    ·
                      refine ⟨210790997399912095787087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 562109326399765588765565 210790997399912095787087)
                      ·
                        rfl

theorem cell23_410514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_410514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410514 prefixEnd_410514 := by exact prefixLift 410514
  have htrace : WordTrace (prefixWord ++ tailWord_410514) baseStart_410514 baseEnd_410514 := by
    simpa [prefixWord, tailWord_410514, baseEnd_410514] using wordTrace_append hprefix tailTrace_410514
  have hstable : (prefixWord ++ tailWord_410514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410514).length < 2 ^ (prefixWord ++ tailWord_410514).sum := by decide
  have hdescent : baseEnd_410514 < baseStart_410514 := by decide
  rcases family_descends (prefixWord ++ tailWord_410514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410560 : List Nat := [2, 1, 1, 2, 3, 4, 2, 3, 5]
def baseStart_410560 : Nat := 118140960795 + 410560 * 2 ^ 59
def prefixEnd_410560 : Nat := 4983230072969 + 3 ^ 40 * 410560 * 2
def baseEnd_410560 : Nat := 23423846390002101756875

theorem tailTrace_410560 : CollatzResearch.WordTrace tailWord_410560 prefixEnd_410560 23423846390002101756875 := by
  unfold tailWord_410560
  simp only [CollatzResearch.WordTrace]
  refine ⟨7487176696309356455362567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9982902261745808607150089 7487176696309356455362567)
  ·
    refine ⟨11230765044464034683043851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7487176696309356455362567 11230765044464034683043851)
    ·
      refine ⟨16846147566696052024565777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11230765044464034683043851 16846147566696052024565777)
      ·
        refine ⟨12634610675022039018424333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16846147566696052024565777 12634610675022039018424333)
        ·
          refine ⟨4737979003133264631909125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12634610675022039018424333 4737979003133264631909125)
          ·
            refine ⟨888371063087487118482961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4737979003133264631909125 888371063087487118482961)
            ·
              refine ⟨666278297315615338862221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 888371063087487118482961 666278297315615338862221)
              ·
                refine ⟨249854361493355752073333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 666278297315615338862221 249854361493355752073333)
                ·
                  refine ⟨23423846390002101756875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 249854361493355752073333 23423846390002101756875)
                  ·
                    rfl

theorem cell23_410560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 5].length) (baseStart_410560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410560 prefixEnd_410560 := by exact prefixLift 410560
  have htrace : WordTrace (prefixWord ++ tailWord_410560) baseStart_410560 baseEnd_410560 := by
    simpa [prefixWord, tailWord_410560, baseEnd_410560] using wordTrace_append hprefix tailTrace_410560
  have hstable : (prefixWord ++ tailWord_410560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410560).length < 2 ^ (prefixWord ++ tailWord_410560).sum := by decide
  have hdescent : baseEnd_410560 < baseStart_410560 := by decide
  rcases family_descends (prefixWord ++ tailWord_410560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410563 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 4, 5, 2]
def baseStart_410563 : Nat := 118140960795 + 410563 * 2 ^ 59
def prefixEnd_410563 : Nat := 4983230072969 + 3 ^ 40 * 410563 * 2
def baseEnd_410563 : Nat := 210816157951982404074361

theorem tailTrace_410563 : CollatzResearch.WordTrace tailWord_410563 prefixEnd_410563 210816157951982404074361 := by
  unfold tailWord_410563
  simp only [CollatzResearch.WordTrace]
  refine ⟨14974462811607844423084343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9982975207738562948722895 14974462811607844423084343)
  ·
    refine ⟨22461694217411766634626515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14974462811607844423084343 22461694217411766634626515)
    ·
      refine ⟨33692541326117649951939773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22461694217411766634626515 33692541326117649951939773)
      ·
        refine ⟨12634702997294118731977415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33692541326117649951939773 12634702997294118731977415)
        ·
          refine ⟨18952054495941178097966123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12634702997294118731977415 18952054495941178097966123)
          ·
            refine ⟨28428081743911767146949185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18952054495941178097966123 28428081743911767146949185)
            ·
              refine ⟨21321061307933825360211889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28428081743911767146949185 21321061307933825360211889)
              ·
                refine ⟨15990795980950369020158917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21321061307933825360211889 15990795980950369020158917)
                ·
                  refine ⟨2998274246428194191279797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15990795980950369020158917 2998274246428194191279797)
                  ·
                    refine ⟨281088210602643205432481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2998274246428194191279797 281088210602643205432481)
                    ·
                      refine ⟨210816157951982404074361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 281088210602643205432481 210816157951982404074361)
                      ·
                        rfl

theorem cell23_410563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 5, 2].length) (baseStart_410563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410563 prefixEnd_410563 := by exact prefixLift 410563
  have htrace : WordTrace (prefixWord ++ tailWord_410563) baseStart_410563 baseEnd_410563 := by
    simpa [prefixWord, tailWord_410563, baseEnd_410563] using wordTrace_append hprefix tailTrace_410563
  have hstable : (prefixWord ++ tailWord_410563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410563).length < 2 ^ (prefixWord ++ tailWord_410563).sum := by decide
  have hdescent : baseEnd_410563 < baseStart_410563 := by decide
  rcases family_descends (prefixWord ++ tailWord_410563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410683 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 4]
def baseStart_410683 : Nat := 118140960795 + 410683 * 2 ^ 59
def prefixEnd_410683 : Nat := 4983230072969 + 3 ^ 40 * 410683 * 2
def baseEnd_410683 : Nat := 210877775630521934573809

theorem tailTrace_410683 : CollatzResearch.WordTrace tailWord_410683 prefixEnd_410683 210877775630521934573809 := by
  unfold tailWord_410683
  simp only [CollatzResearch.WordTrace]
  refine ⟨14978839571173104917452703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9985893047448736611635135 14978839571173104917452703)
  ·
    refine ⟨22468259356759657376179055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14978839571173104917452703 22468259356759657376179055)
    ·
      refine ⟨33702389035139486064268583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22468259356759657376179055 33702389035139486064268583)
      ·
        refine ⟨50553583552709229096402875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33702389035139486064268583 50553583552709229096402875)
        ·
          refine ⟨75830375329063843644604313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50553583552709229096402875 75830375329063843644604313)
          ·
            refine ⟨56872781496797882733453235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75830375329063843644604313 56872781496797882733453235)
            ·
              refine ⟨85309172245196824100179853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56872781496797882733453235 85309172245196824100179853)
              ·
                refine ⟨31990939591948809037567445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85309172245196824100179853 31990939591948809037567445)
                ·
                  refine ⟨749787646686300211817987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 31990939591948809037567445 749787646686300211817987)
                  ·
                    refine ⟨1124681470029450317726981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 749787646686300211817987 1124681470029450317726981)
                    ·
                      refine ⟨210877775630521934573809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1124681470029450317726981 210877775630521934573809)
                      ·
                        rfl

theorem cell23_410683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 4].length) (baseStart_410683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410683 prefixEnd_410683 := by exact prefixLift 410683
  have htrace : WordTrace (prefixWord ++ tailWord_410683) baseStart_410683 baseEnd_410683 := by
    simpa [prefixWord, tailWord_410683, baseEnd_410683] using wordTrace_append hprefix tailTrace_410683
  have hstable : (prefixWord ++ tailWord_410683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410683).length < 2 ^ (prefixWord ++ tailWord_410683).sum := by decide
  have hdescent : baseEnd_410683 < baseStart_410683 := by decide
  rcases family_descends (prefixWord ++ tailWord_410683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410700 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 2, 6, 2]
def baseStart_410700 : Nat := 118140960795 + 410700 * 2 ^ 59
def prefixEnd_410700 : Nat := 4983230072969 + 3 ^ 40 * 410700 * 2
def baseEnd_410700 : Nat := 210886504801648368061231

theorem tailTrace_410700 : CollatzResearch.WordTrace tailWord_410700 prefixEnd_410700 210886504801648368061231 := by
  unfold tailWord_410700
  simp only [CollatzResearch.WordTrace]
  refine ⟨7489729806055758410410777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9986306408074344547214369 7489729806055758410410777)
  ·
    refine ⟨5617297354541818807808083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7489729806055758410410777 5617297354541818807808083)
    ·
      refine ⟨8425946031812728211712125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5617297354541818807808083 8425946031812728211712125)
      ·
        refine ⟨3159729761929773079392047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8425946031812728211712125 3159729761929773079392047)
        ·
          refine ⟨4739594642894659619088071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3159729761929773079392047 4739594642894659619088071)
          ·
            refine ⟨7109391964341989428632107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4739594642894659619088071 7109391964341989428632107)
            ·
              refine ⟨10664087946512984142948161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7109391964341989428632107 10664087946512984142948161)
              ·
                refine ⟨7998065959884738107211121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10664087946512984142948161 7998065959884738107211121)
                ·
                  refine ⟨5998549469913553580408341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7998065959884738107211121 5998549469913553580408341)
                  ·
                    refine ⟨281182006402197824081641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5998549469913553580408341 281182006402197824081641)
                    ·
                      refine ⟨210886504801648368061231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 281182006402197824081641 210886504801648368061231)
                      ·
                        rfl

theorem cell23_410700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_410700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410700 prefixEnd_410700 := by exact prefixLift 410700
  have htrace : WordTrace (prefixWord ++ tailWord_410700) baseStart_410700 baseEnd_410700 := by
    simpa [prefixWord, tailWord_410700, baseEnd_410700] using wordTrace_append hprefix tailTrace_410700
  have hstable : (prefixWord ++ tailWord_410700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410700).length < 2 ^ (prefixWord ++ tailWord_410700).sum := by decide
  have hdescent : baseEnd_410700 < baseStart_410700 := by decide
  rcases family_descends (prefixWord ++ tailWord_410700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410703 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 3]
def baseStart_410703 : Nat := 118140960795 + 410703 * 2 ^ 59
def prefixEnd_410703 : Nat := 4983230072969 + 3 ^ 40 * 410703 * 2
def baseEnd_410703 : Nat := 210888045243611856323717

theorem tailTrace_410703 : CollatzResearch.WordTrace tailWord_410703 prefixEnd_410703 210888045243611856323717 := by
  unfold tailWord_410703
  simp only [CollatzResearch.WordTrace]
  refine ⟨14979569031100648333180763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9986379354067098888787175 14979569031100648333180763)
  ·
    refine ⟨22469353546650972499771145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14979569031100648333180763 22469353546650972499771145)
    ·
      refine ⟨16852015159988229374828359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22469353546650972499771145 16852015159988229374828359)
      ·
        refine ⟨25278022739982344062242539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16852015159988229374828359 25278022739982344062242539)
        ·
          refine ⟨37917034109973516093363809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25278022739982344062242539 37917034109973516093363809)
          ·
            refine ⟨28437775582480137070022857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37917034109973516093363809 28437775582480137070022857)
            ·
              refine ⟨21328331686860102802517143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28437775582480137070022857 21328331686860102802517143)
              ·
                refine ⟨31992497530290154203775715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21328331686860102802517143 31992497530290154203775715)
                ·
                  refine ⟨47988746295435231305663573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31992497530290154203775715 47988746295435231305663573)
                  ·
                    refine ⟨562368120649631616863245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47988746295435231305663573 562368120649631616863245)
                    ·
                      refine ⟨210888045243611856323717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 562368120649631616863245 210888045243611856323717)
                      ·
                        rfl

theorem cell23_410703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 3].length) (baseStart_410703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410703 prefixEnd_410703 := by exact prefixLift 410703
  have htrace : WordTrace (prefixWord ++ tailWord_410703) baseStart_410703 baseEnd_410703 := by
    simpa [prefixWord, tailWord_410703, baseEnd_410703] using wordTrace_append hprefix tailTrace_410703
  have hstable : (prefixWord ++ tailWord_410703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410703).length < 2 ^ (prefixWord ++ tailWord_410703).sum := by decide
  have hdescent : baseEnd_410703 < baseStart_410703 := by decide
  rcases family_descends (prefixWord ++ tailWord_410703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410720 : List Nat := [2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 3]
def baseStart_410720 : Nat := 118140960795 + 410720 * 2 ^ 59
def prefixEnd_410720 : Nat := 4983230072969 + 3 ^ 40 * 410720 * 2
def baseEnd_410720 : Nat := 210896774414738289811139

theorem tailTrace_410720 : CollatzResearch.WordTrace tailWord_410720 prefixEnd_410720 210896774414738289811139 := by
  unfold tailWord_410720
  simp only [CollatzResearch.WordTrace]
  refine ⟨7490094536019530118274807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9986792714692706824366409 7490094536019530118274807)
  ·
    refine ⟨11235141804029295177412211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7490094536019530118274807 11235141804029295177412211)
    ·
      refine ⟨16852712706043942766118317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11235141804029295177412211 16852712706043942766118317)
      ·
        refine ⟨6319767264766478537294369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16852712706043942766118317 6319767264766478537294369)
        ·
          refine ⟨4739825448574858902970777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6319767264766478537294369 4739825448574858902970777)
          ·
            refine ⟨3554869086431144177228083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4739825448574858902970777 3554869086431144177228083)
            ·
              refine ⟨5332303629646716265842125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3554869086431144177228083 5332303629646716265842125)
              ·
                refine ⟨1999613861117518599690797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5332303629646716265842125 1999613861117518599690797)
                ·
                  refine ⟨749855197919069474884049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1999613861117518599690797 749855197919069474884049)
                  ·
                    refine ⟨562391398439302106163037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 749855197919069474884049 562391398439302106163037)
                    ·
                      refine ⟨210896774414738289811139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 562391398439302106163037 210896774414738289811139)
                      ·
                        rfl

theorem cell23_410720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_410720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410720 prefixEnd_410720 := by exact prefixLift 410720
  have htrace : WordTrace (prefixWord ++ tailWord_410720) baseStart_410720 baseEnd_410720 := by
    simpa [prefixWord, tailWord_410720, baseEnd_410720] using wordTrace_append hprefix tailTrace_410720
  have hstable : (prefixWord ++ tailWord_410720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410720).length < 2 ^ (prefixWord ++ tailWord_410720).sum := by decide
  have hdescent : baseEnd_410720 < baseStart_410720 := by decide
  rcases family_descends (prefixWord ++ tailWord_410720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410728 : List Nat := [2, 1, 4, 4, 1, 1, 2, 3, 1, 1, 3]
def baseStart_410728 : Nat := 118140960795 + 410728 * 2 ^ 59
def prefixEnd_410728 : Nat := 4983230072969 + 3 ^ 40 * 410728 * 2
def baseEnd_410728 : Nat := 210900882259974258511103

theorem tailTrace_410728 : CollatzResearch.WordTrace tailWord_410728 prefixEnd_410728 210900882259974258511103 := by
  unfold tailWord_410728
  simp only [CollatzResearch.WordTrace]
  refine ⟨7490240428005038801420419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9986987237340051735227225 7490240428005038801420419)
  ·
    refine ⟨11235360642007558202130629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7490240428005038801420419 11235360642007558202130629)
    ·
      refine ⟨2106630120376417162899493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11235360642007558202130629 2106630120376417162899493)
      ·
        refine ⟨394993147570578218043655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2106630120376417162899493 394993147570578218043655)
        ·
          refine ⟨592489721355867327065483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394993147570578218043655 592489721355867327065483)
          ·
            refine ⟨888734582033800990598225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592489721355867327065483 888734582033800990598225)
            ·
              refine ⟨666550936525350742948669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 888734582033800990598225 666550936525350742948669)
              ·
                refine ⟨249956601197006528605751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 666550936525350742948669 249956601197006528605751)
                ·
                  refine ⟨374934901795509792908627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249956601197006528605751 374934901795509792908627)
                  ·
                    refine ⟨562402352693264689362941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 374934901795509792908627 562402352693264689362941)
                    ·
                      refine ⟨210900882259974258511103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 562402352693264689362941 210900882259974258511103)
                      ·
                        rfl

theorem cell23_410728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_410728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410728 prefixEnd_410728 := by exact prefixLift 410728
  have htrace : WordTrace (prefixWord ++ tailWord_410728) baseStart_410728 baseEnd_410728 := by
    simpa [prefixWord, tailWord_410728, baseEnd_410728] using wordTrace_append hprefix tailTrace_410728
  have hstable : (prefixWord ++ tailWord_410728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410728).length < 2 ^ (prefixWord ++ tailWord_410728).sum := by decide
  have hdescent : baseEnd_410728 < baseStart_410728 := by decide
  rcases family_descends (prefixWord ++ tailWord_410728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410734 : List Nat := [4, 1, 2, 2, 1, 2, 4, 1, 1, 1, 4]
def baseStart_410734 : Nat := 118140960795 + 410734 * 2 ^ 59
def prefixEnd_410734 : Nat := 4983230072969 + 3 ^ 40 * 410734 * 2
def baseEnd_410734 : Nat := 210903963143901235036075

theorem tailTrace_410734 : CollatzResearch.WordTrace tailWord_410734 prefixEnd_410734 210903963143901235036075 := by
  unfold tailWord_410734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1872587461748542578444907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9987133129325560418372837 1872587461748542578444907)
  ·
    refine ⟨2808881192622813867667361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1872587461748542578444907 2808881192622813867667361)
    ·
      refine ⟨2106660894467110400750521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2808881192622813867667361 2106660894467110400750521)
      ·
        refine ⟨1579995670850332800562891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2106660894467110400750521 1579995670850332800562891)
        ·
          refine ⟨2369993506275499200844337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1579995670850332800562891 2369993506275499200844337)
          ·
            refine ⟨1777495129706624400633253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2369993506275499200844337 1777495129706624400633253)
            ·
              refine ⟨333280336819992075118735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1777495129706624400633253 333280336819992075118735)
              ·
                refine ⟨499920505229988112678103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333280336819992075118735 499920505229988112678103)
                ·
                  refine ⟨749880757844982169017155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 499920505229988112678103 749880757844982169017155)
                  ·
                    refine ⟨1124821136767473253525733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 749880757844982169017155 1124821136767473253525733)
                    ·
                      refine ⟨210903963143901235036075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1124821136767473253525733 210903963143901235036075)
                      ·
                        rfl

theorem cell23_410734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_410734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410734 prefixEnd_410734 := by exact prefixLift 410734
  have htrace : WordTrace (prefixWord ++ tailWord_410734) baseStart_410734 baseEnd_410734 := by
    simpa [prefixWord, tailWord_410734, baseEnd_410734] using wordTrace_append hprefix tailTrace_410734
  have hstable : (prefixWord ++ tailWord_410734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410734).length < 2 ^ (prefixWord ++ tailWord_410734).sum := by decide
  have hdescent : baseEnd_410734 < baseStart_410734 := by decide
  rcases family_descends (prefixWord ++ tailWord_410734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410763 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 5]
def baseStart_410763 : Nat := 118140960795 + 410763 * 2 ^ 59
def prefixEnd_410763 : Nat := 4983230072969 + 3 ^ 40 * 410763 * 2
def baseEnd_410763 : Nat := 210918854082881621573441

theorem tailTrace_410763 : CollatzResearch.WordTrace tailWord_410763 prefixEnd_410763 210918854082881621573441 := by
  unfold tailWord_410763
  simp only [CollatzResearch.WordTrace]
  refine ⟨14981757410883278580364943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9987838273922185720243295 14981757410883278580364943)
  ·
    refine ⟨22472636116324917870547415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14981757410883278580364943 22472636116324917870547415)
    ·
      refine ⟨33708954174487376805821123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22472636116324917870547415 33708954174487376805821123)
      ·
        refine ⟨50563431261731065208731685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33708954174487376805821123 50563431261731065208731685)
        ·
          refine ⟨9480643361574574726637191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50563431261731065208731685 9480643361574574726637191)
          ·
            refine ⟨14220965042361862089955787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9480643361574574726637191 14220965042361862089955787)
            ·
              refine ⟨21331447563542793134933681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14220965042361862089955787 21331447563542793134933681)
              ·
                refine ⟨15998585672657094851200261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21331447563542793134933681 15998585672657094851200261)
                ·
                  refine ⟨2999734813623205284600049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15998585672657094851200261 2999734813623205284600049)
                  ·
                    refine ⟨2249801110217403963450037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2999734813623205284600049 2249801110217403963450037)
                    ·
                      refine ⟨210918854082881621573441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2249801110217403963450037 210918854082881621573441)
                      ·
                        rfl

theorem cell23_410763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 5].length) (baseStart_410763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410763 prefixEnd_410763 := by exact prefixLift 410763
  have htrace : WordTrace (prefixWord ++ tailWord_410763) baseStart_410763 baseEnd_410763 := by
    simpa [prefixWord, tailWord_410763, baseEnd_410763] using wordTrace_append hprefix tailTrace_410763
  have hstable : (prefixWord ++ tailWord_410763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410763).length < 2 ^ (prefixWord ++ tailWord_410763).sum := by decide
  have hdescent : baseEnd_410763 < baseStart_410763 := by decide
  rcases family_descends (prefixWord ++ tailWord_410763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410773 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 1, 2, 8]
def baseStart_410773 : Nat := 118140960795 + 410773 * 2 ^ 59
def prefixEnd_410773 : Nat := 4983230072969 + 3 ^ 40 * 410773 * 2
def baseEnd_410773 : Nat := 210923988889426582448395

theorem tailTrace_410773 : CollatzResearch.WordTrace tailWord_410773 prefixEnd_410773 210923988889426582448395 := by
  unfold tailWord_410773
  simp only [CollatzResearch.WordTrace]
  refine ⟨14982122140847050288228973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9988081427231366858819315 14982122140847050288228973)
  ·
    refine ⟨5618295802817643858085865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14982122140847050288228973 5618295802817643858085865)
    ·
      refine ⟨4213721852113232893564399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5618295802817643858085865 4213721852113232893564399)
      ·
        refine ⟨6320582778169849340346599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4213721852113232893564399 6320582778169849340346599)
        ·
          refine ⟨9480874167254774010519899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6320582778169849340346599 9480874167254774010519899)
          ·
            refine ⟨14221311250882161015779849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9480874167254774010519899 14221311250882161015779849)
            ·
              refine ⟨10665983438161620761834887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14221311250882161015779849 10665983438161620761834887)
              ·
                refine ⟨15998975157242431142752331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10665983438161620761834887 15998975157242431142752331)
                ·
                  refine ⟨23998462735863646714128497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15998975157242431142752331 23998462735863646714128497)
                  ·
                    refine ⟨17998847051897735035596373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23998462735863646714128497 17998847051897735035596373)
                    ·
                      refine ⟨210923988889426582448395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 17998847051897735035596373 210923988889426582448395)
                      ·
                        rfl

theorem cell23_410773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_410773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410773 prefixEnd_410773 := by exact prefixLift 410773
  have htrace : WordTrace (prefixWord ++ tailWord_410773) baseStart_410773 baseEnd_410773 := by
    simpa [prefixWord, tailWord_410773, baseEnd_410773] using wordTrace_append hprefix tailTrace_410773
  have hstable : (prefixWord ++ tailWord_410773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410773).length < 2 ^ (prefixWord ++ tailWord_410773).sum := by decide
  have hdescent : baseEnd_410773 < baseStart_410773 := by decide
  rcases family_descends (prefixWord ++ tailWord_410773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410780 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_410780 : Nat := 118140960795 + 410780 * 2 ^ 59
def prefixEnd_410780 : Nat := 4983230072969 + 3 ^ 40 * 410780 * 2
def baseEnd_410780 : Nat := 210927583254008055060863

theorem tailTrace_410780 : CollatzResearch.WordTrace tailWord_410780 prefixEnd_410780 210927583254008055060863 := by
  unfold tailWord_410780
  simp only [CollatzResearch.WordTrace]
  refine ⟨7491188725910845241866897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9988251634547793655822529 7491188725910845241866897)
  ·
    refine ⟨5618391544433133931400173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7491188725910845241866897 5618391544433133931400173)
    ·
      refine ⟨2106896829162425224275065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5618391544433133931400173 2106896829162425224275065)
      ·
        refine ⟨1580172621871818918206299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2106896829162425224275065 1580172621871818918206299)
        ·
          refine ⟨2370258932807728377309449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1580172621871818918206299 2370258932807728377309449)
          ·
            refine ⟨1777694199605796282982087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2370258932807728377309449 1777694199605796282982087)
            ·
              refine ⟨2666541299408694424473131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1777694199605796282982087 2666541299408694424473131)
              ·
                refine ⟨3999811949113041636709697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2666541299408694424473131 3999811949113041636709697)
                ·
                  refine ⟨2999858961834781227532273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3999811949113041636709697 2999858961834781227532273)
                  ·
                    refine ⟨2249894221376085920649205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2999858961834781227532273 2249894221376085920649205)
                    ·
                      refine ⟨210927583254008055060863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2249894221376085920649205 210927583254008055060863)
                      ·
                        rfl

theorem cell23_410780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_410780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410780 prefixEnd_410780 := by exact prefixLift 410780
  have htrace : WordTrace (prefixWord ++ tailWord_410780) baseStart_410780 baseEnd_410780 := by
    simpa [prefixWord, tailWord_410780, baseEnd_410780] using wordTrace_append hprefix tailTrace_410780
  have hstable : (prefixWord ++ tailWord_410780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410780).length < 2 ^ (prefixWord ++ tailWord_410780).sum := by decide
  have hdescent : baseEnd_410780 < baseStart_410780 := by decide
  rcases family_descends (prefixWord ++ tailWord_410780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410810 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3]
def baseStart_410810 : Nat := 118140960795 + 410810 * 2 ^ 59
def prefixEnd_410810 : Nat := 4983230072969 + 3 ^ 40 * 410810 * 2
def baseEnd_410810 : Nat := 210942987673642937685725

theorem tailTrace_410810 : CollatzResearch.WordTrace tailWord_410810 prefixEnd_410810 210942987673642937685725 := by
  unfold tailWord_410810
  simp only [CollatzResearch.WordTrace]
  refine ⟨3745867910428251401831471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9988981094475337071550589 3745867910428251401831471)
  ·
    refine ⟨5618801865642377102747207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3745867910428251401831471 5618801865642377102747207)
    ·
      refine ⟨8428202798463565654120811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5618801865642377102747207 8428202798463565654120811)
      ·
        refine ⟨12642304197695348481181217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8428202798463565654120811 12642304197695348481181217)
        ·
          refine ⟨9481728148271511360885913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12642304197695348481181217 9481728148271511360885913)
          ·
            refine ⟨7111296111203633520664435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9481728148271511360885913 7111296111203633520664435)
            ·
              refine ⟨10666944166805450280996653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7111296111203633520664435 10666944166805450280996653)
              ·
                refine ⟨4000104062552043855373745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10666944166805450280996653 4000104062552043855373745)
                ·
                  refine ⟨3000078046914032891530309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4000104062552043855373745 3000078046914032891530309)
                  ·
                    refine ⟨562514633796381167161933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3000078046914032891530309 562514633796381167161933)
                    ·
                      refine ⟨210942987673642937685725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 562514633796381167161933 210942987673642937685725)
                      ·
                        rfl

theorem cell23_410810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3].length) (baseStart_410810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410810 prefixEnd_410810 := by exact prefixLift 410810
  have htrace : WordTrace (prefixWord ++ tailWord_410810) baseStart_410810 baseEnd_410810 := by
    simpa [prefixWord, tailWord_410810, baseEnd_410810] using wordTrace_append hprefix tailTrace_410810
  have hstable : (prefixWord ++ tailWord_410810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410810).length < 2 ^ (prefixWord ++ tailWord_410810).sum := by decide
  have hdescent : baseEnd_410810 < baseStart_410810 := by decide
  rcases family_descends (prefixWord ++ tailWord_410810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410822 : List Nat := [6, 1, 2, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_410822 : Nat := 118140960795 + 410822 * 2 ^ 59
def prefixEnd_410822 : Nat := 4983230072969 + 3 ^ 40 * 410822 * 2
def baseEnd_410822 : Nat := 210949149441496890735671

theorem tailTrace_410822 : CollatzResearch.WordTrace tailWord_410822 prefixEnd_410822 210949149441496890735671 := by
  unfold tailWord_410822
  simp only [CollatzResearch.WordTrace]
  refine ⟨468247166177172864273835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9989272878446354437841813 468247166177172864273835)
  ·
    refine ⟨702370749265759296410753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 468247166177172864273835 702370749265759296410753)
    ·
      refine ⟨526778061949319472308065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 702370749265759296410753 526778061949319472308065)
      ·
        refine ⟨395083546461989604231049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 526778061949319472308065 395083546461989604231049)
        ·
          refine ⟨296312659846492203173287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395083546461989604231049 296312659846492203173287)
          ·
            refine ⟨444468989769738304759931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296312659846492203173287 444468989769738304759931)
            ·
              refine ⟨666703484654607457139897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 444468989769738304759931 666703484654607457139897)
              ·
                refine ⟨500027613490955592854923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 666703484654607457139897 500027613490955592854923)
                ·
                  refine ⟨750041420236433389282385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 500027613490955592854923 750041420236433389282385)
                  ·
                    refine ⟨562531065177325041961789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 750041420236433389282385 562531065177325041961789)
                    ·
                      refine ⟨210949149441496890735671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 562531065177325041961789 210949149441496890735671)
                      ·
                        rfl

theorem cell23_410822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_410822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410822 prefixEnd_410822 := by exact prefixLift 410822
  have htrace : WordTrace (prefixWord ++ tailWord_410822) baseStart_410822 baseEnd_410822 := by
    simpa [prefixWord, tailWord_410822, baseEnd_410822] using wordTrace_append hprefix tailTrace_410822
  have hstable : (prefixWord ++ tailWord_410822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410822).length < 2 ^ (prefixWord ++ tailWord_410822).sum := by decide
  have hdescent : baseEnd_410822 < baseStart_410822 := by decide
  rcases family_descends (prefixWord ++ tailWord_410822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410867 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 2, 5, 2]
def baseStart_410867 : Nat := 118140960795 + 410867 * 2 ^ 59
def prefixEnd_410867 : Nat := 4983230072969 + 3 ^ 40 * 410867 * 2
def baseEnd_410867 : Nat := 210972256070949214672963

theorem tailTrace_410867 : CollatzResearch.WordTrace tailWord_410867 prefixEnd_410867 210972256070949214672963 := by
  unfold tailWord_410867
  simp only [CollatzResearch.WordTrace]
  refine ⟨14985550602506504342150855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9990367068337669561433903 14985550602506504342150855)
  ·
    refine ⟨22478325903759756513226283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14985550602506504342150855 22478325903759756513226283)
    ·
      refine ⟨33717488855639634769839425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22478325903759756513226283 33717488855639634769839425)
      ·
        refine ⟨25288116641729726077379569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33717488855639634769839425 25288116641729726077379569)
        ·
          refine ⟨18966087481297294558034677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25288116641729726077379569 18966087481297294558034677)
          ·
            refine ⟨1778070701371621364815751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18966087481297294558034677 1778070701371621364815751)
            ·
              refine ⟨2667106052057432047223627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1778070701371621364815751 2667106052057432047223627)
              ·
                refine ⟨4000659078086148070835441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2667106052057432047223627 4000659078086148070835441)
                ·
                  refine ⟨3000494308564611053126581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4000659078086148070835441 3000494308564611053126581)
                  ·
                    refine ⟨281296341427932286230617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3000494308564611053126581 281296341427932286230617)
                    ·
                      refine ⟨210972256070949214672963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 281296341427932286230617 210972256070949214672963)
                      ·
                        rfl

theorem cell23_410867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 5, 2].length) (baseStart_410867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410867 prefixEnd_410867 := by exact prefixLift 410867
  have htrace : WordTrace (prefixWord ++ tailWord_410867) baseStart_410867 baseEnd_410867 := by
    simpa [prefixWord, tailWord_410867, baseEnd_410867] using wordTrace_append hprefix tailTrace_410867
  have hstable : (prefixWord ++ tailWord_410867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410867).length < 2 ^ (prefixWord ++ tailWord_410867).sum := by decide
  have hdescent : baseEnd_410867 < baseStart_410867 := by decide
  rcases family_descends (prefixWord ++ tailWord_410867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410880 : List Nat := [2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 4]
def baseStart_410880 : Nat := 118140960795 + 410880 * 2 ^ 59
def prefixEnd_410880 : Nat := 4983230072969 + 3 ^ 40 * 410880 * 2
def baseEnd_410880 : Nat := 210978931319457663810403

theorem tailTrace_410880 : CollatzResearch.WordTrace tailWord_410880 prefixEnd_410880 210978931319457663810403 := by
  unfold tailWord_410880
  simp only [CollatzResearch.WordTrace]
  refine ⟨7493012375729703781187047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9990683167639605041582729 7493012375729703781187047)
  ·
    refine ⟨11239518563594555671780571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7493012375729703781187047 11239518563594555671780571)
    ·
      refine ⟨16859277845391833507670857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11239518563594555671780571 16859277845391833507670857)
      ·
        refine ⟨12644458384043875130753143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16859277845391833507670857 12644458384043875130753143)
        ·
          refine ⟨18966687576065812696129715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12644458384043875130753143 18966687576065812696129715)
          ·
            refine ⟨28450031364098719044194573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18966687576065812696129715 28450031364098719044194573)
            ·
              refine ⟨10668761761537019641572965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28450031364098719044194573 10668761761537019641572965)
              ·
                refine ⟨2000392830288191182794931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10668761761537019641572965 2000392830288191182794931)
                ·
                  refine ⟨3000589245432286774192397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2000392830288191182794931 3000589245432286774192397)
                  ·
                    refine ⟨1125220967037107540322149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3000589245432286774192397 1125220967037107540322149)
                    ·
                      refine ⟨210978931319457663810403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1125220967037107540322149 210978931319457663810403)
                      ·
                        rfl

theorem cell23_410880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_410880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410880 prefixEnd_410880 := by exact prefixLift 410880
  have htrace : WordTrace (prefixWord ++ tailWord_410880) baseStart_410880 baseEnd_410880 := by
    simpa [prefixWord, tailWord_410880, baseEnd_410880] using wordTrace_append hprefix tailTrace_410880
  have hstable : (prefixWord ++ tailWord_410880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410880).length < 2 ^ (prefixWord ++ tailWord_410880).sum := by decide
  have hdescent : baseEnd_410880 < baseStart_410880 := by decide
  rcases family_descends (prefixWord ++ tailWord_410880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410894 : List Nat := [4, 1, 1, 2, 1, 5, 1, 1, 2, 5]
def baseStart_410894 : Nat := 118140960795 + 410894 * 2 ^ 59
def prefixEnd_410894 : Nat := 4983230072969 + 3 ^ 40 * 410894 * 2
def baseEnd_410894 : Nat := 70328706682873536345113

theorem tailTrace_410894 : CollatzResearch.WordTrace tailWord_410894 prefixEnd_410894 70328706682873536345113 := by
  unfold tailWord_410894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1873316921676085994172967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9991023582272458635589157 1873316921676085994172967)
  ·
    refine ⟨2809975382514128991259451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1873316921676085994172967 2809975382514128991259451)
    ·
      refine ⟨4214963073771193486889177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2809975382514128991259451 4214963073771193486889177)
      ·
        refine ⟨3161222305328395115166883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4214963073771193486889177 3161222305328395115166883)
        ·
          refine ⟨4741833457992592672750325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3161222305328395115166883 4741833457992592672750325)
          ·
            refine ⟨444546886686805563070343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4741833457992592672750325 444546886686805563070343)
            ·
              refine ⟨666820330030208344605515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 444546886686805563070343 666820330030208344605515)
              ·
                refine ⟨1000230495045312516908273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 666820330030208344605515 1000230495045312516908273)
                ·
                  refine ⟨750172871283984387681205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1000230495045312516908273 750172871283984387681205)
                  ·
                    refine ⟨70328706682873536345113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 750172871283984387681205 70328706682873536345113)
                    ·
                      rfl

theorem cell23_410894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_410894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410894 prefixEnd_410894 := by exact prefixLift 410894
  have htrace : WordTrace (prefixWord ++ tailWord_410894) baseStart_410894 baseEnd_410894 := by
    simpa [prefixWord, tailWord_410894, baseEnd_410894] using wordTrace_append hprefix tailTrace_410894
  have hstable : (prefixWord ++ tailWord_410894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410894).length < 2 ^ (prefixWord ++ tailWord_410894).sum := by decide
  have hdescent : baseEnd_410894 < baseStart_410894 := by decide
  rcases family_descends (prefixWord ++ tailWord_410894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410897 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 1, 6, 2]
def baseStart_410897 : Nat := 118140960795 + 410897 * 2 ^ 59
def prefixEnd_410897 : Nat := 4983230072969 + 3 ^ 40 * 410897 * 2
def baseEnd_410897 : Nat := 210987660490584097297825

theorem tailTrace_410897 : CollatzResearch.WordTrace tailWord_410897 prefixEnd_410897 210987660490584097297825 := by
  unfold tailWord_410897
  simp only [CollatzResearch.WordTrace]
  refine ⟨14986644792397819465742945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9991096528265212977161963 14986644792397819465742945)
  ·
    refine ⟨11239983594298364599307209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14986644792397819465742945 11239983594298364599307209)
    ·
      refine ⟨8429987695723773449480407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11239983594298364599307209 8429987695723773449480407)
      ·
        refine ⟨12644981543585660174220611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8429987695723773449480407 12644981543585660174220611)
        ·
          refine ⟨18967472315378490261330917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12644981543585660174220611 18967472315378490261330917)
          ·
            refine ⟨3556401059133466923999547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18967472315378490261330917 3556401059133466923999547)
            ·
              refine ⟨5334601588700200385999321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3556401059133466923999547 5334601588700200385999321)
              ·
                refine ⟨4000951191525150289499491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5334601588700200385999321 4000951191525150289499491)
                ·
                  refine ⟨6001426787287725434249237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4000951191525150289499491 6001426787287725434249237)
                  ·
                    refine ⟨281316880654112129730433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6001426787287725434249237 281316880654112129730433)
                    ·
                      refine ⟨210987660490584097297825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 281316880654112129730433 210987660490584097297825)
                      ·
                        rfl

theorem cell23_410897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 6, 2].length) (baseStart_410897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410897 prefixEnd_410897 := by exact prefixLift 410897
  have htrace : WordTrace (prefixWord ++ tailWord_410897) baseStart_410897 baseEnd_410897 := by
    simpa [prefixWord, tailWord_410897, baseEnd_410897] using wordTrace_append hprefix tailTrace_410897
  have hstable : (prefixWord ++ tailWord_410897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410897).length < 2 ^ (prefixWord ++ tailWord_410897).sum := by decide
  have hdescent : baseEnd_410897 < baseStart_410897 := by decide
  rcases family_descends (prefixWord ++ tailWord_410897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410898 : List Nat := [3, 2, 4, 2, 1, 1, 2, 3, 5]
def baseStart_410898 : Nat := 118140960795 + 410898 * 2 ^ 59
def prefixEnd_410898 : Nat := 4983230072969 + 3 ^ 40 * 410898 * 2
def baseEnd_410898 : Nat := 23443130441248732598369

theorem tailTrace_410898 : CollatzResearch.WordTrace tailWord_410898 prefixEnd_410898 23443130441248732598369 := by
  unfold tailWord_410898
  simp only [CollatzResearch.WordTrace]
  refine ⟨3746670316348549159132337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9991120843596131091019565 3746670316348549159132337)
  ·
    refine ⟨2810002737261411869349253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3746670316348549159132337 2810002737261411869349253)
    ·
      refine ⟨526875513236514725502985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2810002737261411869349253 526875513236514725502985)
      ·
        refine ⟨395156634927386044127239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 526875513236514725502985 395156634927386044127239)
        ·
          refine ⟨592734952391079066190859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395156634927386044127239 592734952391079066190859)
          ·
            refine ⟨889102428586618599286289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592734952391079066190859 889102428586618599286289)
            ·
              refine ⟨666826821439963949464717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 889102428586618599286289 666826821439963949464717)
              ·
                refine ⟨250060058039986481049269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 666826821439963949464717 250060058039986481049269)
                ·
                  refine ⟨23443130441248732598369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 250060058039986481049269 23443130441248732598369)
                  ·
                    rfl

theorem cell23_410898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 5].length) (baseStart_410898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_410898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_410898 prefixEnd_410898 := by exact prefixLift 410898
  have htrace : WordTrace (prefixWord ++ tailWord_410898) baseStart_410898 baseEnd_410898 := by
    simpa [prefixWord, tailWord_410898, baseEnd_410898] using wordTrace_append hprefix tailTrace_410898
  have hstable : (prefixWord ++ tailWord_410898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410898).length < 2 ^ (prefixWord ++ tailWord_410898).sum := by decide
  have hdescent : baseEnd_410898 < baseStart_410898 := by decide
  rcases family_descends (prefixWord ++ tailWord_410898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411032 : List Nat := [2, 1, 2, 5, 2, 2, 2, 2, 1, 1, 3]
def baseStart_411032 : Nat := 118140960795 + 411032 * 2 ^ 59
def prefixEnd_411032 : Nat := 4983230072969 + 3 ^ 40 * 411032 * 2
def baseEnd_411032 : Nat := 211056980378941069109705

theorem tailTrace_411032 : CollatzResearch.WordTrace tailWord_411032 prefixEnd_411032 211056980378941069109705 := by
  unfold tailWord_411032
  simp only [CollatzResearch.WordTrace]
  refine ⟨7495784323454368760953675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9994379097939158347938233 7495784323454368760953675)
  ·
    refine ⟨11243676485181553141430513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7495784323454368760953675 11243676485181553141430513)
    ·
      refine ⟨8432757363886164856072885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11243676485181553141430513 8432757363886164856072885)
      ·
        refine ⟨790571002864327955256833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8432757363886164856072885 790571002864327955256833)
        ·
          refine ⟨592928252148245966442625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 790571002864327955256833 592928252148245966442625)
          ·
            refine ⟨444696189111184474831969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 592928252148245966442625 444696189111184474831969)
            ·
              refine ⟨333522141833388356123977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 444696189111184474831969 333522141833388356123977)
              ·
                refine ⟨250141606375041267092983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333522141833388356123977 250141606375041267092983)
                ·
                  refine ⟨375212409562561900639475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250141606375041267092983 375212409562561900639475)
                  ·
                    refine ⟨562818614343842850959213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 375212409562561900639475 562818614343842850959213)
                    ·
                      refine ⟨211056980378941069109705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 562818614343842850959213 211056980378941069109705)
                      ·
                        rfl

theorem cell23_411032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_411032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411032 prefixEnd_411032 := by exact prefixLift 411032
  have htrace : WordTrace (prefixWord ++ tailWord_411032) baseStart_411032 baseEnd_411032 := by
    simpa [prefixWord, tailWord_411032, baseEnd_411032] using wordTrace_append hprefix tailTrace_411032
  have hstable : (prefixWord ++ tailWord_411032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411032).length < 2 ^ (prefixWord ++ tailWord_411032).sum := by decide
  have hdescent : baseEnd_411032 < baseStart_411032 := by decide
  rcases family_descends (prefixWord ++ tailWord_411032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411057 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 2, 7]
def baseStart_411057 : Nat := 118140960795 + 411057 * 2 ^ 59
def prefixEnd_411057 : Nat := 4983230072969 + 3 ^ 40 * 411057 * 2
def baseEnd_411057 : Nat := 70356605798434490432363

theorem tailTrace_411057 : CollatzResearch.WordTrace tailWord_411057 prefixEnd_411057 70356605798434490432363 := by
  unfold tailWord_411057
  simp only [CollatzResearch.WordTrace]
  refine ⟨14992480471818166791567425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9994986981212111194378283 14992480471818166791567425)
  ·
    refine ⟨11244360353863625093675569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14992480471818166791567425 11244360353863625093675569)
    ·
      refine ⟨8433270265397718820256677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11244360353863625093675569 8433270265397718820256677)
      ·
        refine ⟨1581238174762072278798127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8433270265397718820256677 1581238174762072278798127)
        ·
          refine ⟨2371857262143108418197191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1581238174762072278798127 2371857262143108418197191)
          ·
            refine ⟨3557785893214662627295787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2371857262143108418197191 3557785893214662627295787)
            ·
              refine ⟨5336678839821993940943681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3557785893214662627295787 5336678839821993940943681)
              ·
                refine ⟨4002509129866495455707761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5336678839821993940943681 4002509129866495455707761)
                ·
                  refine ⟨3001881847399871591780821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4002509129866495455707761 3001881847399871591780821)
                  ·
                    refine ⟨70356605798434490432363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3001881847399871591780821 70356605798434490432363)
                    ·
                      rfl

theorem cell23_411057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_411057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411057 prefixEnd_411057 := by exact prefixLift 411057
  have htrace : WordTrace (prefixWord ++ tailWord_411057) baseStart_411057 baseEnd_411057 := by
    simpa [prefixWord, tailWord_411057, baseEnd_411057] using wordTrace_append hprefix tailTrace_411057
  have hstable : (prefixWord ++ tailWord_411057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411057).length < 2 ^ (prefixWord ++ tailWord_411057).sum := by decide
  have hdescent : baseEnd_411057 < baseStart_411057 := by decide
  rcases family_descends (prefixWord ++ tailWord_411057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411087 : List Nat := [1, 1, 2, 1, 1, 4, 3, 2, 2, 6]
def baseStart_411087 : Nat := 118140960795 + 411087 * 2 ^ 59
def prefixEnd_411087 : Nat := 4983230072969 + 3 ^ 40 * 411087 * 2
def baseEnd_411087 : Nat := 70361740604979451307317

theorem tailTrace_411087 : CollatzResearch.WordTrace tailWord_411087 prefixEnd_411087 70361740604979451307317 := by
  unfold tailWord_411087
  simp only [CollatzResearch.WordTrace]
  refine ⟨14993574661709481915159515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9995716441139654610106343 14993574661709481915159515)
  ·
    refine ⟨22490361992564222872739273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14993574661709481915159515 22490361992564222872739273)
    ·
      refine ⟨16867771494423167154554455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22490361992564222872739273 16867771494423167154554455)
      ·
        refine ⟨25301657241634750731831683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16867771494423167154554455 25301657241634750731831683)
        ·
          refine ⟨37952485862452126097747525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25301657241634750731831683 37952485862452126097747525)
          ·
            refine ⟨7116091099209773643327661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37952485862452126097747525 7116091099209773643327661)
            ·
              refine ⟨2668534162203665116247873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7116091099209773643327661 2668534162203665116247873)
              ·
                refine ⟨2001400621652748837185905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2668534162203665116247873 2001400621652748837185905)
                ·
                  refine ⟨1501050466239561627889429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2001400621652748837185905 1501050466239561627889429)
                  ·
                    refine ⟨70361740604979451307317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1501050466239561627889429 70361740604979451307317)
                    ·
                      rfl

theorem cell23_411087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 6].length) (baseStart_411087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411087 prefixEnd_411087 := by exact prefixLift 411087
  have htrace : WordTrace (prefixWord ++ tailWord_411087) baseStart_411087 baseEnd_411087 := by
    simpa [prefixWord, tailWord_411087, baseEnd_411087] using wordTrace_append hprefix tailTrace_411087
  have hstable : (prefixWord ++ tailWord_411087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411087).length < 2 ^ (prefixWord ++ tailWord_411087).sum := by decide
  have hdescent : baseEnd_411087 < baseStart_411087 := by decide
  rcases family_descends (prefixWord ++ tailWord_411087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411144 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 4, 3, 3]
def baseStart_411144 : Nat := 118140960795 + 411144 * 2 ^ 59
def prefixEnd_411144 : Nat := 4983230072969 + 3 ^ 40 * 411144 * 2
def baseEnd_411144 : Nat := 211114490212244630909189

theorem tailTrace_411144 : CollatzResearch.WordTrace tailWord_411144 prefixEnd_411144 211114490212244630909189 := by
  unfold tailWord_411144
  simp only [CollatzResearch.WordTrace]
  refine ⟨7497826811251490324992243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9997102415001987099989657 7497826811251490324992243)
  ·
    refine ⟨11246740216877235487488365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7497826811251490324992243 11246740216877235487488365)
    ·
      refine ⟨4217527581328963307808137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11246740216877235487488365 4217527581328963307808137)
      ·
        refine ⟨3163145685996722480856103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4217527581328963307808137 3163145685996722480856103)
        ·
          refine ⟨4744718528995083721284155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3163145685996722480856103 4744718528995083721284155)
          ·
            refine ⟨7117077793492625581926233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4744718528995083721284155 7117077793492625581926233)
            ·
              refine ⟨5337808345119469186444675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7117077793492625581926233 5337808345119469186444675)
              ·
                refine ⟨8006712517679203779667013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5337808345119469186444675 8006712517679203779667013)
                ·
                  refine ⟨1501258597064850708687565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8006712517679203779667013 1501258597064850708687565)
                  ·
                    refine ⟨562971973899319015757837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1501258597064850708687565 562971973899319015757837)
                    ·
                      refine ⟨211114490212244630909189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 562971973899319015757837 211114490212244630909189)
                      ·
                        rfl

theorem cell23_411144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_411144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411144 prefixEnd_411144 := by exact prefixLift 411144
  have htrace : WordTrace (prefixWord ++ tailWord_411144) baseStart_411144 baseEnd_411144 := by
    simpa [prefixWord, tailWord_411144, baseEnd_411144] using wordTrace_append hprefix tailTrace_411144
  have hstable : (prefixWord ++ tailWord_411144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411144).length < 2 ^ (prefixWord ++ tailWord_411144).sum := by decide
  have hdescent : baseEnd_411144 < baseStart_411144 := by decide
  rcases family_descends (prefixWord ++ tailWord_411144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411164 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 4, 5]
def baseStart_411164 : Nat := 118140960795 + 411164 * 2 ^ 59
def prefixEnd_411164 : Nat := 4983230072969 + 3 ^ 40 * 411164 * 2
def baseEnd_411164 : Nat := 70374919941778184219699

theorem tailTrace_411164 : CollatzResearch.WordTrace tailWord_411164 prefixEnd_411164 70374919941778184219699 := by
  unfold tailWord_411164
  simp only [CollatzResearch.WordTrace]
  refine ⟨7498191541215262032856273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9997588721620349377141697 7498191541215262032856273)
  ·
    refine ⟨5623643655911446524642205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7498191541215262032856273 5623643655911446524642205)
    ·
      refine ⟨2108866370966792446740827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5623643655911446524642205 2108866370966792446740827)
      ·
        refine ⟨3163299556450188670111241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2108866370966792446740827 3163299556450188670111241)
        ·
          refine ⟨2372474667337641502583431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3163299556450188670111241 2372474667337641502583431)
          ·
            refine ⟨3558712001006462253875147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2372474667337641502583431 3558712001006462253875147)
            ·
              refine ⟨5338068001509693380812721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3558712001006462253875147 5338068001509693380812721)
              ·
                refine ⟨4003551001132270035609541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5338068001509693380812721 4003551001132270035609541)
                ·
                  refine ⟨750665812712300631676789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4003551001132270035609541 750665812712300631676789)
                  ·
                    refine ⟨70374919941778184219699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 750665812712300631676789 70374919941778184219699)
                    ·
                      rfl

theorem cell23_411164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_411164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411164 prefixEnd_411164 := by exact prefixLift 411164
  have htrace : WordTrace (prefixWord ++ tailWord_411164) baseStart_411164 baseEnd_411164 := by
    simpa [prefixWord, tailWord_411164, baseEnd_411164] using wordTrace_append hprefix tailTrace_411164
  have hstable : (prefixWord ++ tailWord_411164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411164).length < 2 ^ (prefixWord ++ tailWord_411164).sum := by decide
  have hdescent : baseEnd_411164 < baseStart_411164 := by decide
  rcases family_descends (prefixWord ++ tailWord_411164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411166 : List Nat := [4, 3, 3, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_411166 : Nat := 118140960795 + 411166 * 2 ^ 59
def prefixEnd_411166 : Nat := 4983230072969 + 3 ^ 40 * 411166 * 2
def baseEnd_411166 : Nat := 211125786786643544834089

theorem tailTrace_411166 : CollatzResearch.WordTrace tailWord_411166 prefixEnd_411166 211125786786643544834089 := by
  unfold tailWord_411166
  simp only [CollatzResearch.WordTrace]
  refine ⟨1874557003552909800910669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9997637352282185604856901 1874557003552909800910669)
  ·
    refine ⟨702958876332341175341501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1874557003552909800910669 702958876332341175341501)
    ·
      refine ⟨263609578624627940753063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 702958876332341175341501 263609578624627940753063)
      ·
        refine ⟨395414367936941911129595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263609578624627940753063 395414367936941911129595)
        ·
          refine ⟨593121551905412866694393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395414367936941911129595 593121551905412866694393)
          ·
            refine ⟨444841163929059650020795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 593121551905412866694393 444841163929059650020795)
            ·
              refine ⟨667261745893589475031193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 444841163929059650020795 667261745893589475031193)
              ·
                refine ⟨500446309420192106273395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 667261745893589475031193 500446309420192106273395)
                ·
                  refine ⟨750669464130288159410093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 500446309420192106273395 750669464130288159410093)
                  ·
                    refine ⟨281501049048858059778785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 750669464130288159410093 281501049048858059778785)
                    ·
                      refine ⟨211125786786643544834089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 281501049048858059778785 211125786786643544834089)
                      ·
                        rfl

theorem cell23_411166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_411166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411166 prefixEnd_411166 := by exact prefixLift 411166
  have htrace : WordTrace (prefixWord ++ tailWord_411166) baseStart_411166 baseEnd_411166 := by
    simpa [prefixWord, tailWord_411166, baseEnd_411166] using wordTrace_append hprefix tailTrace_411166
  have hstable : (prefixWord ++ tailWord_411166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411166).length < 2 ^ (prefixWord ++ tailWord_411166).sum := by decide
  have hdescent : baseEnd_411166 < baseStart_411166 := by decide
  rcases family_descends (prefixWord ++ tailWord_411166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411201 : List Nat := [1, 2, 5, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_411201 : Nat := 118140960795 + 411201 * 2 ^ 59
def prefixEnd_411201 : Nat := 4983230072969 + 3 ^ 40 * 411201 * 2
def baseEnd_411201 : Nat := 211143758609550907896427

theorem tailTrace_411201 : CollatzResearch.WordTrace tailWord_411201 prefixEnd_411201 211143758609550907896427 := by
  unfold tailWord_411201
  simp only [CollatzResearch.WordTrace]
  refine ⟨14997732583296479384809457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9998488388864319589872971 14997732583296479384809457)
  ·
    refine ⟨11248299437472359538607093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14997732583296479384809457 11248299437472359538607093)
    ·
      refine ⟨1054528072263033706744415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11248299437472359538607093 1054528072263033706744415)
      ·
        refine ⟨1581792108394550560116623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1054528072263033706744415 1581792108394550560116623)
        ·
          refine ⟨2372688162591825840174935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1581792108394550560116623 2372688162591825840174935)
          ·
            refine ⟨3559032243887738760262403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2372688162591825840174935 3559032243887738760262403)
            ·
              refine ⟨5338548365831608140393605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3559032243887738760262403 5338548365831608140393605)
              ·
                refine ⟨1000977818593426526323801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5338548365831608140393605 1000977818593426526323801)
                ·
                  refine ⟨750733363945069894742851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1000977818593426526323801 750733363945069894742851)
                  ·
                    refine ⟨1126100045917604842114277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 750733363945069894742851 1126100045917604842114277)
                    ·
                      refine ⟨211143758609550907896427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1126100045917604842114277 211143758609550907896427)
                      ·
                        rfl

theorem cell23_411201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_411201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411201 prefixEnd_411201 := by exact prefixLift 411201
  have htrace : WordTrace (prefixWord ++ tailWord_411201) baseStart_411201 baseEnd_411201 := by
    simpa [prefixWord, tailWord_411201, baseEnd_411201] using wordTrace_append hprefix tailTrace_411201
  have hstable : (prefixWord ++ tailWord_411201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411201).length < 2 ^ (prefixWord ++ tailWord_411201).sum := by decide
  have hdescent : baseEnd_411201 < baseStart_411201 := by decide
  rcases family_descends (prefixWord ++ tailWord_411201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411214 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4]
def baseStart_411214 : Nat := 118140960795 + 411214 * 2 ^ 59
def prefixEnd_411214 : Nat := 4983230072969 + 3 ^ 40 * 411214 * 2
def baseEnd_411214 : Nat := 211150433858059357033867

theorem tailTrace_411214 : CollatzResearch.WordTrace tailWord_411214 prefixEnd_411214 211150433858059357033867 := by
  unfold tailWord_411214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1874775841531172825629087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9998804488166255070021797 1874775841531172825629087)
  ·
    refine ⟨2812163762296759238443631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1874775841531172825629087 2812163762296759238443631)
    ·
      refine ⟨4218245643445138857665447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2812163762296759238443631 4218245643445138857665447)
      ·
        refine ⟨6327368465167708286498171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4218245643445138857665447 6327368465167708286498171)
        ·
          refine ⟨9491052697751562429747257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6327368465167708286498171 9491052697751562429747257)
          ·
            refine ⟨7118289523313671822310443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9491052697751562429747257 7118289523313671822310443)
            ·
              refine ⟨10677434284970507733465665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7118289523313671822310443 10677434284970507733465665)
              ·
                refine ⟨8008075713727880800099249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10677434284970507733465665 8008075713727880800099249)
                ·
                  refine ⟨6006056785295910600074437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8008075713727880800099249 6006056785295910600074437)
                  ·
                    refine ⟨1126135647242983237513957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6006056785295910600074437 1126135647242983237513957)
                    ·
                      refine ⟨211150433858059357033867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1126135647242983237513957 211150433858059357033867)
                      ·
                        rfl

theorem cell23_411214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_411214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411214 prefixEnd_411214 := by exact prefixLift 411214
  have htrace : WordTrace (prefixWord ++ tailWord_411214) baseStart_411214 baseEnd_411214 := by
    simpa [prefixWord, tailWord_411214, baseEnd_411214] using wordTrace_append hprefix tailTrace_411214
  have hstable : (prefixWord ++ tailWord_411214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411214).length < 2 ^ (prefixWord ++ tailWord_411214).sum := by decide
  have hdescent : baseEnd_411214 < baseStart_411214 := by decide
  rcases family_descends (prefixWord ++ tailWord_411214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411218 : List Nat := [3, 2, 2, 1, 2, 3, 1, 1, 2, 4, 2]
def baseStart_411218 : Nat := 118140960795 + 411218 * 2 ^ 59
def prefixEnd_411218 : Nat := 4983230072969 + 3 ^ 40 * 411218 * 2
def baseEnd_411218 : Nat := 211152487780677341383849

theorem tailTrace_411218 : CollatzResearch.WordTrace tailWord_411218 prefixEnd_411218 211152487780677341383849 := by
  unfold tailWord_411218
  simp only [CollatzResearch.WordTrace]
  refine ⟨3749588156058722822044577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9998901749489927525452205 3749588156058722822044577)
  ·
    refine ⟨2812191117044042116533433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3749588156058722822044577 2812191117044042116533433)
    ·
      refine ⟨2109143337783031587400075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2812191117044042116533433 2109143337783031587400075)
      ·
        refine ⟨3163715006674547381100113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2109143337783031587400075 3163715006674547381100113)
        ·
          refine ⟨2372786255005910535825085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3163715006674547381100113 2372786255005910535825085)
          ·
            refine ⟨889794845627216450934407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2372786255005910535825085 889794845627216450934407)
            ·
              refine ⟨1334692268440824676401611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 889794845627216450934407 1334692268440824676401611)
              ·
                refine ⟨2002038402661237014602417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1334692268440824676401611 2002038402661237014602417)
                ·
                  refine ⟨1501528801995927760951813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2002038402661237014602417 1501528801995927760951813)
                  ·
                    refine ⟨281536650374236455178465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1501528801995927760951813 281536650374236455178465)
                    ·
                      refine ⟨211152487780677341383849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 281536650374236455178465 211152487780677341383849)
                      ·
                        rfl

theorem cell23_411218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_411218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411218 prefixEnd_411218 := by exact prefixLift 411218
  have htrace : WordTrace (prefixWord ++ tailWord_411218) baseStart_411218 baseEnd_411218 := by
    simpa [prefixWord, tailWord_411218, baseEnd_411218] using wordTrace_append hprefix tailTrace_411218
  have hstable : (prefixWord ++ tailWord_411218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411218).length < 2 ^ (prefixWord ++ tailWord_411218).sum := by decide
  have hdescent : baseEnd_411218 < baseStart_411218 := by decide
  rcases family_descends (prefixWord ++ tailWord_411218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411228 : List Nat := [2, 2, 4, 1, 2, 2, 1, 2, 3, 4]
def baseStart_411228 : Nat := 118140960795 + 411228 * 2 ^ 59
def prefixEnd_411228 : Nat := 4983230072969 + 3 ^ 40 * 411228 * 2
def baseEnd_411228 : Nat := 70385874195740767419601

theorem tailTrace_411228 : CollatzResearch.WordTrace tailWord_411228 prefixEnd_411228 70385874195740767419601 := by
  unfold tailWord_411228
  simp only [CollatzResearch.WordTrace]
  refine ⟨7499358677099331498021169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9999144902799108664028225 7499358677099331498021169)
  ·
    refine ⟨5624519007824498623515877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7499358677099331498021169 5624519007824498623515877)
    ·
      refine ⟨1054597313967093491909227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5624519007824498623515877 1054597313967093491909227)
      ·
        refine ⟨1581895970950640237863841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1054597313967093491909227 1581895970950640237863841)
        ·
          refine ⟨1186421978212980178397881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1581895970950640237863841 1186421978212980178397881)
          ·
            refine ⟨889816483659735133798411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1186421978212980178397881 889816483659735133798411)
            ·
              refine ⟨1334724725489602700697617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 889816483659735133798411 1334724725489602700697617)
              ·
                refine ⟨1001043544117202025523213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1334724725489602700697617 1001043544117202025523213)
                ·
                  refine ⟨375391329043950759571205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1001043544117202025523213 375391329043950759571205)
                  ·
                    refine ⟨70385874195740767419601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 375391329043950759571205 70385874195740767419601)
                    ·
                      rfl

theorem cell23_411228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_411228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411228 prefixEnd_411228 := by exact prefixLift 411228
  have htrace : WordTrace (prefixWord ++ tailWord_411228) baseStart_411228 baseEnd_411228 := by
    simpa [prefixWord, tailWord_411228, baseEnd_411228] using wordTrace_append hprefix tailTrace_411228
  have hstable : (prefixWord ++ tailWord_411228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411228).length < 2 ^ (prefixWord ++ tailWord_411228).sum := by decide
  have hdescent : baseEnd_411228 < baseStart_411228 := by decide
  rcases family_descends (prefixWord ++ tailWord_411228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411278 : List Nat := [4, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2]
def baseStart_411278 : Nat := 118140960795 + 411278 * 2 ^ 59
def prefixEnd_411278 : Nat := 4983230072969 + 3 ^ 40 * 411278 * 2
def baseEnd_411278 : Nat := 211183296619947106633573

theorem tailTrace_411278 : CollatzResearch.WordTrace tailWord_411278 prefixEnd_411278 211183296619947106633573 := by
  unfold tailWord_411278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1875067625502190191920311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10000360669345014356908325 1875067625502190191920311)
  ·
    refine ⟨2812601438253285287880467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1875067625502190191920311 2812601438253285287880467)
    ·
      refine ⟨4218902157379927931820701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2812601438253285287880467 4218902157379927931820701)
      ·
        refine ⟨1582088309017472974432763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4218902157379927931820701 1582088309017472974432763)
        ·
          refine ⟨2373132463526209461649145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1582088309017472974432763 2373132463526209461649145)
          ·
            refine ⟨1779849347644657096236859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2373132463526209461649145 1779849347644657096236859)
            ·
              refine ⟨2669774021466985644355289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1779849347644657096236859 2669774021466985644355289)
              ·
                refine ⟨2002330516100239233266467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2669774021466985644355289 2002330516100239233266467)
                ·
                  refine ⟨3003495774150358849899701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2002330516100239233266467 3003495774150358849899701)
                  ·
                    refine ⟨281577728826596142178097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3003495774150358849899701 281577728826596142178097)
                    ·
                      refine ⟨211183296619947106633573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 281577728826596142178097 211183296619947106633573)
                      ·
                        rfl

theorem cell23_411278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_411278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411278 prefixEnd_411278 := by exact prefixLift 411278
  have htrace : WordTrace (prefixWord ++ tailWord_411278) baseStart_411278 baseEnd_411278 := by
    simpa [prefixWord, tailWord_411278, baseEnd_411278] using wordTrace_append hprefix tailTrace_411278
  have hstable : (prefixWord ++ tailWord_411278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411278).length < 2 ^ (prefixWord ++ tailWord_411278).sum := by decide
  have hdescent : baseEnd_411278 < baseStart_411278 := by decide
  rcases family_descends (prefixWord ++ tailWord_411278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411288 : List Nat := [2, 1, 2, 4, 1, 3, 2, 2, 1, 5]
def baseStart_411288 : Nat := 118140960795 + 411288 * 2 ^ 59
def prefixEnd_411288 : Nat := 4983230072969 + 3 ^ 40 * 411288 * 2
def baseEnd_411288 : Nat := 70396143808830689169509

theorem tailTrace_411288 : CollatzResearch.WordTrace tailWord_411288 prefixEnd_411288 70396143808830689169509 := by
  unfold tailWord_411288
  simp only [CollatzResearch.WordTrace]
  refine ⟨7500452866990646621613259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10000603822654195495484345 7500452866990646621613259)
  ·
    refine ⟨11250679300485969932419889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7500452866990646621613259 11250679300485969932419889)
    ·
      refine ⟨8438009475364477449314917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11250679300485969932419889 8438009475364477449314917)
      ·
        refine ⟨1582126776630839521746547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8438009475364477449314917 1582126776630839521746547)
        ·
          refine ⟨2373190164946259282619821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1582126776630839521746547 2373190164946259282619821)
          ·
            refine ⟨889946311854847230982433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2373190164946259282619821 889946311854847230982433)
            ·
              refine ⟨667459733891135423236825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 889946311854847230982433 667459733891135423236825)
              ·
                refine ⟨500594800418351567427619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 667459733891135423236825 500594800418351567427619)
                ·
                  refine ⟨750892200627527351141429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 500594800418351567427619 750892200627527351141429)
                  ·
                    refine ⟨70396143808830689169509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 750892200627527351141429 70396143808830689169509)
                    ·
                      rfl

theorem cell23_411288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 1, 5].length) (baseStart_411288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411288 prefixEnd_411288 := by exact prefixLift 411288
  have htrace : WordTrace (prefixWord ++ tailWord_411288) baseStart_411288 baseEnd_411288 := by
    simpa [prefixWord, tailWord_411288, baseEnd_411288] using wordTrace_append hprefix tailTrace_411288
  have hstable : (prefixWord ++ tailWord_411288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411288).length < 2 ^ (prefixWord ++ tailWord_411288).sum := by decide
  have hdescent : baseEnd_411288 < baseStart_411288 := by decide
  rcases family_descends (prefixWord ++ tailWord_411288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411301 : List Nat := [1, 3, 1, 2, 1, 2, 3, 2, 4, 4]
def baseStart_411301 : Nat := 118140960795 + 411301 * 2 ^ 59
def prefixEnd_411301 : Nat := 4983230072969 + 3 ^ 40 * 411301 * 2
def baseEnd_411301 : Nat := 70398368891666838881989

theorem tailTrace_411301 : CollatzResearch.WordTrace tailWord_411301 prefixEnd_411301 70398368891666838881989 := by
  unfold tailWord_411301
  simp only [CollatzResearch.WordTrace]
  refine ⟨15001379882934196463449757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10000919921956130975633171 15001379882934196463449757)
  ·
    refine ⟨5625517456100323673793659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15001379882934196463449757 5625517456100323673793659)
    ·
      refine ⟨8438276184150485510690489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5625517456100323673793659 8438276184150485510690489)
      ·
        refine ⟨6328707138112864133017867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8438276184150485510690489 6328707138112864133017867)
        ·
          refine ⟨9493060707169296199526801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6328707138112864133017867 9493060707169296199526801)
          ·
            refine ⟨7119795530376972149645101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9493060707169296199526801 7119795530376972149645101)
            ·
              refine ⟨2669923323891364556116913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7119795530376972149645101 2669923323891364556116913)
              ·
                refine ⟨2002442492918523417087685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2669923323891364556116913 2002442492918523417087685)
                ·
                  refine ⟨375457967422223140703941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2002442492918523417087685 375457967422223140703941)
                  ·
                    refine ⟨70398368891666838881989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 375457967422223140703941 70398368891666838881989)
                    ·
                      rfl

theorem cell23_411301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 4].length) (baseStart_411301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411301 prefixEnd_411301 := by exact prefixLift 411301
  have htrace : WordTrace (prefixWord ++ tailWord_411301) baseStart_411301 baseEnd_411301 := by
    simpa [prefixWord, tailWord_411301, baseEnd_411301] using wordTrace_append hprefix tailTrace_411301
  have hstable : (prefixWord ++ tailWord_411301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411301).length < 2 ^ (prefixWord ++ tailWord_411301).sum := by decide
  have hdescent : baseEnd_411301 < baseStart_411301 := by decide
  rcases family_descends (prefixWord ++ tailWord_411301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411311 : List Nat := [1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 5]
def baseStart_411311 : Nat := 118140960795 + 411311 * 2 ^ 59
def prefixEnd_411311 : Nat := 4983230072969 + 3 ^ 40 * 411311 * 2
def baseEnd_411311 : Nat := 211200241481545477520921

theorem tailTrace_411311 : CollatzResearch.WordTrace tailWord_411311 prefixEnd_411311 211200241481545477520921 := by
  unfold tailWord_411311
  simp only [CollatzResearch.WordTrace]
  refine ⟨15001744612897968171313787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10001163075265312114209191 15001744612897968171313787)
  ·
    refine ⟨22502616919346952256970681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15001744612897968171313787 22502616919346952256970681)
    ·
      refine ⟨16876962689510214192728011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22502616919346952256970681 16876962689510214192728011)
      ·
        refine ⟨25315444034265321289092017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16876962689510214192728011 25315444034265321289092017)
        ·
          refine ⟨18986583025698990966819013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25315444034265321289092017 18986583025698990966819013)
          ·
            refine ⟨3559984317318560806278565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18986583025698990966819013 3559984317318560806278565)
            ·
              refine ⟨667497059497230151177231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3559984317318560806278565 667497059497230151177231)
              ·
                refine ⟨1001245589245845226765847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667497059497230151177231 1001245589245845226765847)
                ·
                  refine ⟨1501868383868767840148771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1001245589245845226765847 1501868383868767840148771)
                  ·
                    refine ⟨2252802575803151760223157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1501868383868767840148771 2252802575803151760223157)
                    ·
                      refine ⟨211200241481545477520921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2252802575803151760223157 211200241481545477520921)
                      ·
                        rfl

theorem cell23_411311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 5].length) (baseStart_411311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411311 prefixEnd_411311 := by exact prefixLift 411311
  have htrace : WordTrace (prefixWord ++ tailWord_411311) baseStart_411311 baseEnd_411311 := by
    simpa [prefixWord, tailWord_411311, baseEnd_411311] using wordTrace_append hprefix tailTrace_411311
  have hstable : (prefixWord ++ tailWord_411311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411311).length < 2 ^ (prefixWord ++ tailWord_411311).sum := by decide
  have hdescent : baseEnd_411311 < baseStart_411311 := by decide
  rcases family_descends (prefixWord ++ tailWord_411311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411314 : List Nat := [3, 2, 1, 1, 1, 2, 13]
def baseStart_411314 : Nat := 118140960795 + 411314 * 2 ^ 59
def prefixEnd_411314 : Nat := 4983230072969 + 3 ^ 40 * 411314 * 2
def baseEnd_411314 : Nat := 2607429406463073651647

theorem tailTrace_411314 : CollatzResearch.WordTrace tailWord_411314 prefixEnd_411314 2607429406463073651647 := by
  unfold tailWord_411314
  simp only [CollatzResearch.WordTrace]
  refine ⟨3750463507971774920918249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10001236021258066455781997 3750463507971774920918249)
  ·
    refine ⟨2812847630978831190688687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3750463507971774920918249 2812847630978831190688687)
    ·
      refine ⟨4219271446468246786033031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2812847630978831190688687 4219271446468246786033031)
      ·
        refine ⟨6328907169702370179049547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4219271446468246786033031 6328907169702370179049547)
        ·
          refine ⟨9493360754553555268574321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6328907169702370179049547 9493360754553555268574321)
          ·
            refine ⟨7120020565915166451430741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9493360754553555268574321 7120020565915166451430741)
            ·
              refine ⟨2607429406463073651647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 7120020565915166451430741 2607429406463073651647)
              ·
                rfl

theorem cell23_411314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 13].length) (baseStart_411314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411314 prefixEnd_411314 := by exact prefixLift 411314
  have htrace : WordTrace (prefixWord ++ tailWord_411314) baseStart_411314 baseEnd_411314 := by
    simpa [prefixWord, tailWord_411314, baseEnd_411314] using wordTrace_append hprefix tailTrace_411314
  have hstable : (prefixWord ++ tailWord_411314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411314).length < 2 ^ (prefixWord ++ tailWord_411314).sum := by decide
  have hdescent : baseEnd_411314 < baseStart_411314 := by decide
  rcases family_descends (prefixWord ++ tailWord_411314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411344 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 4, 7]
def baseStart_411344 : Nat := 118140960795 + 411344 * 2 ^ 59
def prefixEnd_411344 : Nat := 4983230072969 + 3 ^ 40 * 411344 * 2
def baseEnd_411344 : Nat := 70405728781047949469423

theorem tailTrace_411344 : CollatzResearch.WordTrace tailWord_411344 prefixEnd_411344 70405728781047949469423 := by
  unfold tailWord_411344
  simp only [CollatzResearch.WordTrace]
  refine ⟨7501474110889207403632543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10001965481185609871510057 7501474110889207403632543)
  ·
    refine ⟨11252211166333811105448815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7501474110889207403632543 11252211166333811105448815)
    ·
      refine ⟨16878316749500716658173223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11252211166333811105448815 16878316749500716658173223)
      ·
        refine ⟨25317475124251074987259835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16878316749500716658173223 25317475124251074987259835)
        ·
          refine ⟨37976212686376612480889753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25317475124251074987259835 37976212686376612480889753)
          ·
            refine ⟨28482159514782459360667315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37976212686376612480889753 28482159514782459360667315)
            ·
              refine ⟨42723239272173689041000973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28482159514782459360667315 42723239272173689041000973)
              ·
                refine ⟨16021214727065133390375365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42723239272173689041000973 16021214727065133390375365)
                ·
                  refine ⟨3003977761324712510695381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16021214727065133390375365 3003977761324712510695381)
                  ·
                    refine ⟨70405728781047949469423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3003977761324712510695381 70405728781047949469423)
                    ·
                      rfl

theorem cell23_411344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 4, 7].length) (baseStart_411344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411344 prefixEnd_411344 := by exact prefixLift 411344
  have htrace : WordTrace (prefixWord ++ tailWord_411344) baseStart_411344 baseEnd_411344 := by
    simpa [prefixWord, tailWord_411344, baseEnd_411344] using wordTrace_append hprefix tailTrace_411344
  have hstable : (prefixWord ++ tailWord_411344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411344).length < 2 ^ (prefixWord ++ tailWord_411344).sum := by decide
  have hdescent : baseEnd_411344 < baseStart_411344 := by decide
  rcases family_descends (prefixWord ++ tailWord_411344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411345 : List Nat := [1, 2, 2, 1, 2, 6, 1, 2, 1, 2, 3]
def baseStart_411345 : Nat := 118140960795 + 411345 * 2 ^ 59
def prefixEnd_411345 : Nat := 4983230072969 + 3 ^ 40 * 411345 * 2
def baseEnd_411345 : Nat := 211217699823798344495765

theorem tailTrace_411345 : CollatzResearch.WordTrace tailWord_411345 prefixEnd_411345 211217699823798344495765 := by
  unfold tailWord_411345
  simp only [CollatzResearch.WordTrace]
  refine ⟨15002984694774791978051489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10001989796516527985367659 15002984694774791978051489)
  ·
    refine ⟨11252238521081093983538617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15002984694774791978051489 11252238521081093983538617)
    ·
      refine ⟨8439178890810820487653963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11252238521081093983538617 8439178890810820487653963)
      ·
        refine ⟨12658768336216230731480945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8439178890810820487653963 12658768336216230731480945)
        ·
          refine ⟨9494076252162173048610709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12658768336216230731480945 9494076252162173048610709)
          ·
            refine ⟨445034824320101861653627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9494076252162173048610709 445034824320101861653627)
            ·
              refine ⟨667552236480152792480441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 445034824320101861653627 667552236480152792480441)
              ·
                refine ⟨500664177360114594360331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 667552236480152792480441 500664177360114594360331)
                ·
                  refine ⟨750996266040171891540497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 500664177360114594360331 750996266040171891540497)
                  ·
                    refine ⟨563247199530128918655373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 750996266040171891540497 563247199530128918655373)
                    ·
                      refine ⟨211217699823798344495765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 563247199530128918655373 211217699823798344495765)
                      ·
                        rfl

theorem cell23_411345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 2, 3].length) (baseStart_411345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411345 prefixEnd_411345 := by exact prefixLift 411345
  have htrace : WordTrace (prefixWord ++ tailWord_411345) baseStart_411345 baseEnd_411345 := by
    simpa [prefixWord, tailWord_411345, baseEnd_411345] using wordTrace_append hprefix tailTrace_411345
  have hstable : (prefixWord ++ tailWord_411345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411345).length < 2 ^ (prefixWord ++ tailWord_411345).sum := by decide
  have hdescent : baseEnd_411345 < baseStart_411345 := by decide
  rcases family_descends (prefixWord ++ tailWord_411345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411375 : List Nat := [1, 1, 2, 1, 5, 1, 4, 2, 2, 1, 3]
def baseStart_411375 : Nat := 118140960795 + 411375 * 2 ^ 59
def prefixEnd_411375 : Nat := 4983230072969 + 3 ^ 40 * 411375 * 2
def baseEnd_411375 : Nat := 211233104243433227120627

theorem tailTrace_411375 : CollatzResearch.WordTrace tailWord_411375 prefixEnd_411375 211233104243433227120627 := by
  unfold tailWord_411375
  simp only [CollatzResearch.WordTrace]
  refine ⟨15004078884666107101643579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10002719256444071401095719 15004078884666107101643579)
  ·
    refine ⟨22506118326999160652465369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15004078884666107101643579 22506118326999160652465369)
    ·
      refine ⟨16879588745249370489349027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22506118326999160652465369 16879588745249370489349027)
      ·
        refine ⟨25319383117874055734023541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16879588745249370489349027 25319383117874055734023541)
        ·
          refine ⟨2373692167300692725064707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25319383117874055734023541 2373692167300692725064707)
          ·
            refine ⟨3560538250951039087597061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2373692167300692725064707 3560538250951039087597061)
            ·
              refine ⟨667600922053319828924449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3560538250951039087597061 667600922053319828924449)
              ·
                refine ⟨500700691539989871693337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 667600922053319828924449 500700691539989871693337)
                ·
                  refine ⟨375525518654992403770003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 500700691539989871693337 375525518654992403770003)
                  ·
                    refine ⟨563288277982488605655005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 375525518654992403770003 563288277982488605655005)
                    ·
                      refine ⟨211233104243433227120627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 563288277982488605655005 211233104243433227120627)
                      ·
                        rfl

theorem cell23_411375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 1, 3].length) (baseStart_411375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411375 prefixEnd_411375 := by exact prefixLift 411375
  have htrace : WordTrace (prefixWord ++ tailWord_411375) baseStart_411375 baseEnd_411375 := by
    simpa [prefixWord, tailWord_411375, baseEnd_411375] using wordTrace_append hprefix tailTrace_411375
  have hstable : (prefixWord ++ tailWord_411375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411375).length < 2 ^ (prefixWord ++ tailWord_411375).sum := by decide
  have hdescent : baseEnd_411375 < baseStart_411375 := by decide
  rcases family_descends (prefixWord ++ tailWord_411375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411401 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 4, 4, 3]
def baseStart_411401 : Nat := 118140960795 + 411401 * 2 ^ 59
def prefixEnd_411401 : Nat := 4983230072969 + 3 ^ 40 * 411401 * 2
def baseEnd_411401 : Nat := 211246454740450125395507

theorem tailTrace_411401 : CollatzResearch.WordTrace tailWord_411401 prefixEnd_411401 211246454740450125395507 := by
  unfold tailWord_411401
  simp only [CollatzResearch.WordTrace]
  refine ⟨15005027182571913542090057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10003351455047942361393371 15005027182571913542090057)
  ·
    refine ⟨11253770386928935156567543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15005027182571913542090057 11253770386928935156567543)
    ·
      refine ⟨16880655580393402734851315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11253770386928935156567543 16880655580393402734851315)
      ·
        refine ⟨25320983370590104102276973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16880655580393402734851315 25320983370590104102276973)
        ·
          refine ⟨9495368763971289038353865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25320983370590104102276973 9495368763971289038353865)
          ·
            refine ⟨7121526572978466778765399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9495368763971289038353865 7121526572978466778765399)
            ·
              refine ⟨10682289859467700168148099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7121526572978466778765399 10682289859467700168148099)
              ·
                refine ⟨16023434789201550252222149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10682289859467700168148099 16023434789201550252222149)
                ·
                  refine ⟨3004394022975290672291653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16023434789201550252222149 3004394022975290672291653)
                  ·
                    refine ⟨563323879307867001054685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3004394022975290672291653 563323879307867001054685)
                    ·
                      refine ⟨211246454740450125395507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 563323879307867001054685 211246454740450125395507)
                      ·
                        rfl

theorem cell23_411401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 4, 3].length) (baseStart_411401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411401 prefixEnd_411401 := by exact prefixLift 411401
  have htrace : WordTrace (prefixWord ++ tailWord_411401) baseStart_411401 baseEnd_411401 := by
    simpa [prefixWord, tailWord_411401, baseEnd_411401] using wordTrace_append hprefix tailTrace_411401
  have hstable : (prefixWord ++ tailWord_411401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411401).length < 2 ^ (prefixWord ++ tailWord_411401).sum := by decide
  have hdescent : baseEnd_411401 < baseStart_411401 := by decide
  rcases family_descends (prefixWord ++ tailWord_411401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411415 : List Nat := [1, 1, 3, 4, 2, 1, 2, 2, 1, 4, 2]
def baseStart_411415 : Nat := 118140960795 + 411415 * 2 ^ 59
def prefixEnd_411415 : Nat := 4983230072969 + 3 ^ 40 * 411415 * 2
def baseEnd_411415 : Nat := 211253643469613070620443

theorem tailTrace_411415 : CollatzResearch.WordTrace tailWord_411415 prefixEnd_411415 211253643469613070620443 := by
  unfold tailWord_411415
  simp only [CollatzResearch.WordTrace]
  refine ⟨15005537804521193933099699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10003691869680795955399799 15005537804521193933099699)
  ·
    refine ⟨22508306706781790899649549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15005537804521193933099699 22508306706781790899649549)
    ·
      refine ⟨8440615015043171587368581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22508306706781790899649549 8440615015043171587368581)
      ·
        refine ⟨1582615315320594672631609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8440615015043171587368581 1582615315320594672631609)
        ·
          refine ⟨1186961486490446004473707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1582615315320594672631609 1186961486490446004473707)
          ·
            refine ⟨1780442229735669006710561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1186961486490446004473707 1780442229735669006710561)
            ·
              refine ⟨1335331672301751755032921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1780442229735669006710561 1335331672301751755032921)
              ·
                refine ⟨1001498754226313816274691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1335331672301751755032921 1001498754226313816274691)
                ·
                  refine ⟨1502248131339470724412037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1001498754226313816274691 1502248131339470724412037)
                  ·
                    refine ⟨281671524626150760827257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1502248131339470724412037 281671524626150760827257)
                    ·
                      refine ⟨211253643469613070620443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 281671524626150760827257 211253643469613070620443)
                      ·
                        rfl

theorem cell23_411415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_411415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411415 prefixEnd_411415 := by exact prefixLift 411415
  have htrace : WordTrace (prefixWord ++ tailWord_411415) baseStart_411415 baseEnd_411415 := by
    simpa [prefixWord, tailWord_411415, baseEnd_411415] using wordTrace_append hprefix tailTrace_411415
  have hstable : (prefixWord ++ tailWord_411415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411415).length < 2 ^ (prefixWord ++ tailWord_411415).sum := by decide
  have hdescent : baseEnd_411415 < baseStart_411415 := by decide
  rcases family_descends (prefixWord ++ tailWord_411415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411428 : List Nat := [2, 3, 1, 3, 2, 1, 1, 2, 2, 2, 4]
def baseStart_411428 : Nat := 118140960795 + 411428 * 2 ^ 59
def prefixEnd_411428 : Nat := 4983230072969 + 3 ^ 40 * 411428 * 2
def baseEnd_411428 : Nat := 211260318718121519757883

theorem tailTrace_411428 : CollatzResearch.WordTrace tailWord_411428 prefixEnd_411428 211260318718121519757883 := by
  unfold tailWord_411428
  simp only [CollatzResearch.WordTrace]
  refine ⟨7503005976737048576661469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10004007968982731435548625 7503005976737048576661469)
  ·
    refine ⟨2813627241276393216248051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7503005976737048576661469 2813627241276393216248051)
    ·
      refine ⟨4220440861914589824372077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2813627241276393216248051 4220440861914589824372077)
      ·
        refine ⟨1582665323217971184139529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4220440861914589824372077 1582665323217971184139529)
        ·
          refine ⟨1186998992413478388104647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1582665323217971184139529 1186998992413478388104647)
          ·
            refine ⟨1780498488620217582156971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1186998992413478388104647 1780498488620217582156971)
            ·
              refine ⟨2670747732930326373235457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1780498488620217582156971 2670747732930326373235457)
              ·
                refine ⟨2003060799697744779926593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2670747732930326373235457 2003060799697744779926593)
                ·
                  refine ⟨1502295599773308584944945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2003060799697744779926593 1502295599773308584944945)
                  ·
                    refine ⟨1126721699829981438708709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1502295599773308584944945 1126721699829981438708709)
                    ·
                      refine ⟨211260318718121519757883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1126721699829981438708709 211260318718121519757883)
                      ·
                        rfl

theorem cell23_411428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_411428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411428 prefixEnd_411428 := by exact prefixLift 411428
  have htrace : WordTrace (prefixWord ++ tailWord_411428) baseStart_411428 baseEnd_411428 := by
    simpa [prefixWord, tailWord_411428, baseEnd_411428] using wordTrace_append hprefix tailTrace_411428
  have hstable : (prefixWord ++ tailWord_411428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411428).length < 2 ^ (prefixWord ++ tailWord_411428).sum := by decide
  have hdescent : baseEnd_411428 < baseStart_411428 := by decide
  rcases family_descends (prefixWord ++ tailWord_411428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411432 : List Nat := [2, 1, 5, 1, 1, 3, 1, 1, 4, 2, 2]
def baseStart_411432 : Nat := 118140960795 + 411432 * 2 ^ 59
def prefixEnd_411432 : Nat := 4983230072969 + 3 ^ 40 * 411432 * 2
def baseEnd_411432 : Nat := 211262372640739504107865

theorem tailTrace_411432 : CollatzResearch.WordTrace tailWord_411432 prefixEnd_411432 211262372640739504107865 := by
  unfold tailWord_411432
  simp only [CollatzResearch.WordTrace]
  refine ⟨7503078922729802918234275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10004105230306403890979033 7503078922729802918234275)
  ·
    refine ⟨11254618384094704377351413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7503078922729802918234275 11254618384094704377351413)
    ·
      refine ⟨1055120473508878535376695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11254618384094704377351413 1055120473508878535376695)
      ·
        refine ⟨1582680710263317803065043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1055120473508878535376695 1582680710263317803065043)
        ·
          refine ⟨2374021065394976704597565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1582680710263317803065043 2374021065394976704597565)
          ·
            refine ⟨890257899523116264224087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2374021065394976704597565 890257899523116264224087)
            ·
              refine ⟨1335386849284674396336131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890257899523116264224087 1335386849284674396336131)
              ·
                refine ⟨2003080273927011594504197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335386849284674396336131 2003080273927011594504197)
                ·
                  refine ⟨375577551361314673969537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2003080273927011594504197 375577551361314673969537)
                  ·
                    refine ⟨281683163520986005477153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 375577551361314673969537 281683163520986005477153)
                    ·
                      refine ⟨211262372640739504107865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 281683163520986005477153 211262372640739504107865)
                      ·
                        rfl

theorem cell23_411432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_411432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411432 prefixEnd_411432 := by exact prefixLift 411432
  have htrace : WordTrace (prefixWord ++ tailWord_411432) baseStart_411432 baseEnd_411432 := by
    simpa [prefixWord, tailWord_411432, baseEnd_411432] using wordTrace_append hprefix tailTrace_411432
  have hstable : (prefixWord ++ tailWord_411432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411432).length < 2 ^ (prefixWord ++ tailWord_411432).sum := by decide
  have hdescent : baseEnd_411432 < baseStart_411432 := by decide
  rcases family_descends (prefixWord ++ tailWord_411432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411448 : List Nat := [2, 1, 2, 1, 3, 3, 2, 1, 2, 3, 3]
def baseStart_411448 : Nat := 118140960795 + 411448 * 2 ^ 59
def prefixEnd_411448 : Nat := 4983230072969 + 3 ^ 40 * 411448 * 2
def baseEnd_411448 : Nat := 211270588331211441507791

theorem tailTrace_411448 : CollatzResearch.WordTrace tailWord_411448 prefixEnd_411448 211270588331211441507791 := by
  unfold tailWord_411448
  simp only [CollatzResearch.WordTrace]
  refine ⟨7503370706700820284525499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10004494275601093712700665 7503370706700820284525499)
  ·
    refine ⟨11255056060051230426788249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7503370706700820284525499 11255056060051230426788249)
    ·
      refine ⟨8441292045038422820091187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11255056060051230426788249 8441292045038422820091187)
      ·
        refine ⟨12661938067557634230136781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8441292045038422820091187 12661938067557634230136781)
        ·
          refine ⟨4748226775334112836301293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12661938067557634230136781 4748226775334112836301293)
          ·
            refine ⟨1780585040750292313612985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4748226775334112836301293 1780585040750292313612985)
            ·
              refine ⟨1335438780562719235209739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1780585040750292313612985 1335438780562719235209739)
              ·
                refine ⟨2003158170844078852814609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335438780562719235209739 2003158170844078852814609)
                ·
                  refine ⟨1502368628133059139610957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2003158170844078852814609 1502368628133059139610957)
                  ·
                    refine ⟨563388235549897177354109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1502368628133059139610957 563388235549897177354109)
                    ·
                      refine ⟨211270588331211441507791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 563388235549897177354109 211270588331211441507791)
                      ·
                        rfl

theorem cell23_411448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 2, 3, 3].length) (baseStart_411448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411448 prefixEnd_411448 := by exact prefixLift 411448
  have htrace : WordTrace (prefixWord ++ tailWord_411448) baseStart_411448 baseEnd_411448 := by
    simpa [prefixWord, tailWord_411448, baseEnd_411448] using wordTrace_append hprefix tailTrace_411448
  have hstable : (prefixWord ++ tailWord_411448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411448).length < 2 ^ (prefixWord ++ tailWord_411448).sum := by decide
  have hdescent : baseEnd_411448 < baseStart_411448 := by decide
  rcases family_descends (prefixWord ++ tailWord_411448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411449 : List Nat := [1, 2, 1, 7, 1, 2, 1, 1, 1, 4, 2]
def baseStart_411449 : Nat := 118140960795 + 411449 * 2 ^ 59
def prefixEnd_411449 : Nat := 4983230072969 + 3 ^ 40 * 411449 * 2
def baseEnd_411449 : Nat := 211271101811865937595287

theorem tailTrace_411449 : CollatzResearch.WordTrace tailWord_411449 prefixEnd_411449 211271101811865937595287 := by
  unfold tailWord_411449
  simp only [CollatzResearch.WordTrace]
  refine ⟨15006777886398017739837401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10004518590932011826558267 15006777886398017739837401)
  ·
    refine ⟨11255083414798513304878051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15006777886398017739837401 11255083414798513304878051)
    ·
      refine ⟨16882625122197769957317077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11255083414798513304878051 16882625122197769957317077)
      ·
        refine ⟨395686526301510233374619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 16882625122197769957317077 395686526301510233374619)
        ·
          refine ⟨593529789452265350061929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395686526301510233374619 593529789452265350061929)
          ·
            refine ⟨445147342089199012546447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 593529789452265350061929 445147342089199012546447)
            ·
              refine ⟨667721013133798518819671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 445147342089199012546447 667721013133798518819671)
              ·
                refine ⟨1001581519700697778229507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667721013133798518819671 1001581519700697778229507)
                ·
                  refine ⟨1502372279551046667344261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1001581519700697778229507 1502372279551046667344261)
                  ·
                    refine ⟨281694802415821250127049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1502372279551046667344261 281694802415821250127049)
                    ·
                      refine ⟨211271101811865937595287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 281694802415821250127049 211271101811865937595287)
                      ·
                        rfl

theorem cell23_411449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_411449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411449 prefixEnd_411449 := by exact prefixLift 411449
  have htrace : WordTrace (prefixWord ++ tailWord_411449) baseStart_411449 baseEnd_411449 := by
    simpa [prefixWord, tailWord_411449, baseEnd_411449] using wordTrace_append hprefix tailTrace_411449
  have hstable : (prefixWord ++ tailWord_411449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411449).length < 2 ^ (prefixWord ++ tailWord_411449).sum := by decide
  have hdescent : baseEnd_411449 < baseStart_411449 := by decide
  rcases family_descends (prefixWord ++ tailWord_411449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411488 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 4]
def baseStart_411488 : Nat := 118140960795 + 411488 * 2 ^ 59
def prefixEnd_411488 : Nat := 4983230072969 + 3 ^ 40 * 411488 * 2
def baseEnd_411488 : Nat := 211291127557391285007607

theorem tailTrace_411488 : CollatzResearch.WordTrace tailWord_411488 prefixEnd_411488 211291127557391285007607 := by
  unfold tailWord_411488
  simp only [CollatzResearch.WordTrace]
  refine ⟨7504100166628363700253559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10005466888837818267004745 7504100166628363700253559)
  ·
    refine ⟨11256150249942545550380339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7504100166628363700253559 11256150249942545550380339)
    ·
      refine ⟨16884225374913818325570509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11256150249942545550380339 16884225374913818325570509)
      ·
        refine ⟨6331584515592681872088941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16884225374913818325570509 6331584515592681872088941)
        ·
          refine ⟨2374344193347255702033353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6331584515592681872088941 2374344193347255702033353)
          ·
            refine ⟨1780758145010441776525015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2374344193347255702033353 1780758145010441776525015)
            ·
              refine ⟨2671137217515662664787523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1780758145010441776525015 2671137217515662664787523)
              ·
                refine ⟨4006705826273493997181285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2671137217515662664787523 4006705826273493997181285)
                ·
                  refine ⟨751257342426280124471491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4006705826273493997181285 751257342426280124471491)
                  ·
                    refine ⟨1126886013639420186707237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 751257342426280124471491 1126886013639420186707237)
                    ·
                      refine ⟨211291127557391285007607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1126886013639420186707237 211291127557391285007607)
                      ·
                        rfl

theorem cell23_411488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_411488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411488 prefixEnd_411488 := by exact prefixLift 411488
  have htrace : WordTrace (prefixWord ++ tailWord_411488) baseStart_411488 baseEnd_411488 := by
    simpa [prefixWord, tailWord_411488, baseEnd_411488] using wordTrace_append hprefix tailTrace_411488
  have hstable : (prefixWord ++ tailWord_411488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411488).length < 2 ^ (prefixWord ++ tailWord_411488).sum := by decide
  have hdescent : baseEnd_411488 < baseStart_411488 := by decide
  rcases family_descends (prefixWord ++ tailWord_411488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411525 : List Nat := [1, 3, 1, 1, 3, 2, 4, 1, 2, 2, 3]
def baseStart_411525 : Nat := 118140960795 + 411525 * 2 ^ 59
def prefixEnd_411525 : Nat := 4983230072969 + 3 ^ 40 * 411525 * 2
def baseEnd_411525 : Nat := 211310126341607640244937

theorem tailTrace_411525 : CollatzResearch.WordTrace tailWord_411525 prefixEnd_411525 211310126341607640244937 := by
  unfold tailWord_411525
  simp only [CollatzResearch.WordTrace]
  refine ⟨15009549834122682719604029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10006366556081788479736019 15009549834122682719604029)
  ·
    refine ⟨5628581187796006019851511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15009549834122682719604029 5628581187796006019851511)
    ·
      refine ⟨8442871781694009029777267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5628581187796006019851511 8442871781694009029777267)
      ·
        refine ⟨12664307672541013544665901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8442871781694009029777267 12664307672541013544665901)
        ·
          refine ⟨4749115377202880079249713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12664307672541013544665901 4749115377202880079249713)
          ·
            refine ⟨3561836532902160059437285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4749115377202880079249713 3561836532902160059437285)
            ·
              refine ⟨667844349919155011144491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3561836532902160059437285 667844349919155011144491)
              ·
                refine ⟨1001766524878732516716737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667844349919155011144491 1001766524878732516716737)
                ·
                  refine ⟨751324893659049387537553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1001766524878732516716737 751324893659049387537553)
                  ·
                    refine ⟨563493670244287040653165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 751324893659049387537553 563493670244287040653165)
                    ·
                      refine ⟨211310126341607640244937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 563493670244287040653165 211310126341607640244937)
                      ·
                        rfl

theorem cell23_411525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 2, 3].length) (baseStart_411525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411525 prefixEnd_411525 := by exact prefixLift 411525
  have htrace : WordTrace (prefixWord ++ tailWord_411525) baseStart_411525 baseEnd_411525 := by
    simpa [prefixWord, tailWord_411525, baseEnd_411525] using wordTrace_append hprefix tailTrace_411525
  have hstable : (prefixWord ++ tailWord_411525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411525).length < 2 ^ (prefixWord ++ tailWord_411525).sum := by decide
  have hdescent : baseEnd_411525 < baseStart_411525 := by decide
  rcases family_descends (prefixWord ++ tailWord_411525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411531 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 8]
def baseStart_411531 : Nat := 118140960795 + 411531 * 2 ^ 59
def prefixEnd_411531 : Nat := 4983230072969 + 3 ^ 40 * 411531 * 2
def baseEnd_411531 : Nat := 211313207225534616769909

theorem tailTrace_411531 : CollatzResearch.WordTrace tailWord_411531 prefixEnd_411531 211313207225534616769909 := by
  unfold tailWord_411531
  simp only [CollatzResearch.WordTrace]
  refine ⟨15009768672100945744322447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10006512448067297162881631 15009768672100945744322447)
  ·
    refine ⟨22514653008151418616483671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15009768672100945744322447 22514653008151418616483671)
    ·
      refine ⟨33771979512227127924725507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22514653008151418616483671 33771979512227127924725507)
      ·
        refine ⟨50657969268340691887088261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33771979512227127924725507 50657969268340691887088261)
        ·
          refine ⟨9498369237813879728829049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50657969268340691887088261 9498369237813879728829049)
          ·
            refine ⟨7123776928360409796621787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9498369237813879728829049 7123776928360409796621787)
            ·
              refine ⟨10685665392540614694932681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7123776928360409796621787 10685665392540614694932681)
              ·
                refine ⟨8014249044405461021199511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10685665392540614694932681 8014249044405461021199511)
                ·
                  refine ⟨12021373566608191531799267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8014249044405461021199511 12021373566608191531799267)
                  ·
                    refine ⟨18032060349912287297698901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12021373566608191531799267 18032060349912287297698901)
                    ·
                      refine ⟨211313207225534616769909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 18032060349912287297698901 211313207225534616769909)
                      ·
                        rfl

theorem cell23_411531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 8].length) (baseStart_411531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411531 prefixEnd_411531 := by exact prefixLift 411531
  have htrace : WordTrace (prefixWord ++ tailWord_411531) baseStart_411531 baseEnd_411531 := by
    simpa [prefixWord, tailWord_411531, baseEnd_411531] using wordTrace_append hprefix tailTrace_411531
  have hstable : (prefixWord ++ tailWord_411531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411531).length < 2 ^ (prefixWord ++ tailWord_411531).sum := by decide
  have hdescent : baseEnd_411531 < baseStart_411531 := by decide
  rcases family_descends (prefixWord ++ tailWord_411531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411549 : List Nat := [1, 4, 2, 1, 2, 2, 4, 2, 1, 4]
def baseStart_411549 : Nat := 118140960795 + 411549 * 2 ^ 59
def prefixEnd_411549 : Nat := 4983230072969 + 3 ^ 40 * 411549 * 2
def baseEnd_411549 : Nat := 70440816625771848781609

theorem tailTrace_411549 : CollatzResearch.WordTrace tailWord_411549 prefixEnd_411549 70440816625771848781609 := by
  unfold tailWord_411549
  simp only [CollatzResearch.WordTrace]
  refine ⟨15010425186035734818477701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10006950124023823212318467 15010425186035734818477701)
  ·
    refine ⟨2814454722381700278464569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15010425186035734818477701 2814454722381700278464569)
    ·
      refine ⟨2110841041786275208848427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2814454722381700278464569 2110841041786275208848427)
      ·
        refine ⟨3166261562679412813272641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2110841041786275208848427 3166261562679412813272641)
        ·
          refine ⟨2374696172009559609954481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3166261562679412813272641 2374696172009559609954481)
          ·
            refine ⟨1781022129007169707465861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2374696172009559609954481 1781022129007169707465861)
            ·
              refine ⟨333941649188844320149849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1781022129007169707465861 333941649188844320149849)
              ·
                refine ⟨250456236891633240112387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333941649188844320149849 250456236891633240112387)
                ·
                  refine ⟨375684355337449860168581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250456236891633240112387 375684355337449860168581)
                  ·
                    refine ⟨70440816625771848781609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 375684355337449860168581 70440816625771848781609)
                    ·
                      rfl

theorem cell23_411549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_411549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411549 prefixEnd_411549 := by exact prefixLift 411549
  have htrace : WordTrace (prefixWord ++ tailWord_411549) baseStart_411549 baseEnd_411549 := by
    simpa [prefixWord, tailWord_411549, baseEnd_411549] using wordTrace_append hprefix tailTrace_411549
  have hstable : (prefixWord ++ tailWord_411549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411549).length < 2 ^ (prefixWord ++ tailWord_411549).sum := by decide
  have hdescent : baseEnd_411549 < baseStart_411549 := by decide
  rcases family_descends (prefixWord ++ tailWord_411549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411555 : List Nat := [1, 1, 1, 4, 1, 2, 1, 5, 3, 1, 3]
def baseStart_411555 : Nat := 118140960795 + 411555 * 2 ^ 59
def prefixEnd_411555 : Nat := 4983230072969 + 3 ^ 40 * 411555 * 2
def baseEnd_411555 : Nat := 211325530761242522869799

theorem tailTrace_411555 : CollatzResearch.WordTrace tailWord_411555 prefixEnd_411555 211325530761242522869799 := by
  unfold tailWord_411555
  simp only [CollatzResearch.WordTrace]
  refine ⟨15010644024013997843196119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10007096016009331895464079 15010644024013997843196119)
  ·
    refine ⟨22515966036020996764794179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15010644024013997843196119 22515966036020996764794179)
    ·
      refine ⟨33773949054031495147191269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22515966036020996764794179 33773949054031495147191269)
      ·
        refine ⟨6332615447630905340098363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33773949054031495147191269 6332615447630905340098363)
        ·
          refine ⟨9498923171446358010147545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6332615447630905340098363 9498923171446358010147545)
          ·
            refine ⟨7124192378584768507610659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9498923171446358010147545 7124192378584768507610659)
            ·
              refine ⟨10686288567877152761415989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7124192378584768507610659 10686288567877152761415989)
              ·
                refine ⟨1001839553238483071382749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10686288567877152761415989 1001839553238483071382749)
                ·
                  refine ⟨375689832464431151768531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1001839553238483071382749 375689832464431151768531)
                  ·
                    refine ⟨563534748696646727652797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 375689832464431151768531 563534748696646727652797)
                    ·
                      refine ⟨211325530761242522869799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 563534748696646727652797 211325530761242522869799)
                      ·
                        rfl

theorem cell23_411555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_411555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411555 prefixEnd_411555 := by exact prefixLift 411555
  have htrace : WordTrace (prefixWord ++ tailWord_411555) baseStart_411555 baseEnd_411555 := by
    simpa [prefixWord, tailWord_411555, baseEnd_411555] using wordTrace_append hprefix tailTrace_411555
  have hstable : (prefixWord ++ tailWord_411555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411555).length < 2 ^ (prefixWord ++ tailWord_411555).sum := by decide
  have hdescent : baseEnd_411555 < baseStart_411555 := by decide
  rcases family_descends (prefixWord ++ tailWord_411555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411566 : List Nat := [4, 1, 5, 1, 1, 1, 1, 2, 3, 4]
def baseStart_411566 : Nat := 118140960795 + 411566 * 2 ^ 59
def prefixEnd_411566 : Nat := 4983230072969 + 3 ^ 40 * 411566 * 2
def baseEnd_411566 : Nat := 70443726349480659944083

theorem tailTrace_411566 : CollatzResearch.WordTrace tailWord_411566 prefixEnd_411566 70443726349480659944083 := by
  unfold tailWord_411566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1876380653371768340230819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10007363484649431147897701 1876380653371768340230819)
  ·
    refine ⟨2814570980057652510346229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1876380653371768340230819 2814570980057652510346229)
    ·
      refine ⟨263866029380404922844959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2814570980057652510346229 263866029380404922844959)
      ·
        refine ⟨395799044070607384267439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263866029380404922844959 395799044070607384267439)
        ·
          refine ⟨593698566105911076401159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395799044070607384267439 593698566105911076401159)
          ·
            refine ⟨890547849158866614601739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593698566105911076401159 890547849158866614601739)
            ·
              refine ⟨1335821773738299921902609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890547849158866614601739 1335821773738299921902609)
              ·
                refine ⟨1001866330303724941426957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1335821773738299921902609 1001866330303724941426957)
                ·
                  refine ⟨375699873863896853035109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1001866330303724941426957 375699873863896853035109)
                  ·
                    refine ⟨70443726349480659944083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 375699873863896853035109 70443726349480659944083)
                    ·
                      rfl

theorem cell23_411566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_411566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411566 prefixEnd_411566 := by exact prefixLift 411566
  have htrace : WordTrace (prefixWord ++ tailWord_411566) baseStart_411566 baseEnd_411566 := by
    simpa [prefixWord, tailWord_411566, baseEnd_411566] using wordTrace_append hprefix tailTrace_411566
  have hstable : (prefixWord ++ tailWord_411566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411566).length < 2 ^ (prefixWord ++ tailWord_411566).sum := by decide
  have hdescent : baseEnd_411566 < baseStart_411566 := by decide
  rcases family_descends (prefixWord ++ tailWord_411566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411582 : List Nat := [4, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2]
def baseStart_411582 : Nat := 118140960795 + 411582 * 2 ^ 59
def prefixEnd_411582 : Nat := 4983230072969 + 3 ^ 40 * 411582 * 2
def baseEnd_411582 : Nat := 211339394738913917232175

theorem tailTrace_411582 : CollatzResearch.WordTrace tailWord_411582 prefixEnd_411582 211339394738913917232175 := by
  unfold tailWord_411582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1876453599364522681803625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10007752529944120969619333 1876453599364522681803625)
  ·
    refine ⟨1407340199523392011352719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1876453599364522681803625 1407340199523392011352719)
    ·
      refine ⟨2111010299285088017029079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1407340199523392011352719 2111010299285088017029079)
      ·
        refine ⟨3166515448927632025543619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2111010299285088017029079 3166515448927632025543619)
        ·
          refine ⟨4749773173391448038315429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3166515448927632025543619 4749773173391448038315429)
          ·
            refine ⟨890582470010896507184143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4749773173391448038315429 890582470010896507184143)
            ·
              refine ⟨1335873705016344760776215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890582470010896507184143 1335873705016344760776215)
              ·
                refine ⟨2003810557524517141164323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335873705016344760776215 2003810557524517141164323)
                ·
                  refine ⟨3005715836286775711746485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2003810557524517141164323 3005715836286775711746485)
                  ·
                    refine ⟨281785859651885222976233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3005715836286775711746485 281785859651885222976233)
                    ·
                      refine ⟨211339394738913917232175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 281785859651885222976233 211339394738913917232175)
                      ·
                        rfl

theorem cell23_411582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_411582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411582 prefixEnd_411582 := by exact prefixLift 411582
  have htrace : WordTrace (prefixWord ++ tailWord_411582) baseStart_411582 baseEnd_411582 := by
    simpa [prefixWord, tailWord_411582, baseEnd_411582] using wordTrace_append hprefix tailTrace_411582
  have hstable : (prefixWord ++ tailWord_411582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411582).length < 2 ^ (prefixWord ++ tailWord_411582).sum := by decide
  have hdescent : baseEnd_411582 < baseStart_411582 := by decide
  rcases family_descends (prefixWord ++ tailWord_411582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411592 : List Nat := [2, 1, 3, 1, 4, 1, 4, 1, 1, 5]
def baseStart_411592 : Nat := 118140960795 + 411592 * 2 ^ 59
def prefixEnd_411592 : Nat := 4983230072969 + 3 ^ 40 * 411592 * 2
def baseEnd_411592 : Nat := 70448176515152959369043

theorem tailTrace_411592 : CollatzResearch.WordTrace tailWord_411592 prefixEnd_411592 70448176515152959369043 := by
  unfold tailWord_411592
  simp only [CollatzResearch.WordTrace]
  refine ⟨7505996762439976581146515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10007995683253302108195353 7505996762439976581146515)
  ·
    refine ⟨11258995143659964871719773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7505996762439976581146515 11258995143659964871719773)
    ·
      refine ⟨4222123178872486826894915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11258995143659964871719773 4222123178872486826894915)
      ·
        refine ⟨6333184768308730240342373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4222123178872486826894915 6333184768308730240342373)
        ·
          refine ⟨1187472144057886920064195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6333184768308730240342373 1187472144057886920064195)
          ·
            refine ⟨1781208216086830380096293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1187472144057886920064195 1781208216086830380096293)
            ·
              refine ⟨333976540516280696268055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1781208216086830380096293 333976540516280696268055)
              ·
                refine ⟨500964810774421044402083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333976540516280696268055 500964810774421044402083)
                ·
                  refine ⟨751447216161631566603125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 500964810774421044402083 751447216161631566603125)
                  ·
                    refine ⟨70448176515152959369043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 751447216161631566603125 70448176515152959369043)
                    ·
                      rfl

theorem cell23_411592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_411592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411592 prefixEnd_411592 := by exact prefixLift 411592
  have htrace : WordTrace (prefixWord ++ tailWord_411592) baseStart_411592 baseEnd_411592 := by
    simpa [prefixWord, tailWord_411592, baseEnd_411592] using wordTrace_append hprefix tailTrace_411592
  have hstable : (prefixWord ++ tailWord_411592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411592).length < 2 ^ (prefixWord ++ tailWord_411592).sum := by decide
  have hdescent : baseEnd_411592 < baseStart_411592 := by decide
  rcases family_descends (prefixWord ++ tailWord_411592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411595 : List Nat := [1, 1, 1, 1, 3, 4, 3, 3, 1, 1, 4]
def baseStart_411595 : Nat := 118140960795 + 411595 * 2 ^ 59
def prefixEnd_411595 : Nat := 4983230072969 + 3 ^ 40 * 411595 * 2
def baseEnd_411595 : Nat := 211346069987422366369615

theorem tailTrace_411595 : CollatzResearch.WordTrace tailWord_411595 prefixEnd_411595 211346069987422366369615 := by
  unfold tailWord_411595
  simp only [CollatzResearch.WordTrace]
  refine ⟨15012102943869084674652239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10008068629246056449768159 15012102943869084674652239)
  ·
    refine ⟨22518154415803627011978359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15012102943869084674652239 22518154415803627011978359)
    ·
      refine ⟨33777231623705440517967539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22518154415803627011978359 33777231623705440517967539)
      ·
        refine ⟨50665847435558160776951309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33777231623705440517967539 50665847435558160776951309)
        ·
          refine ⟨18999692788334310291356741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50665847435558160776951309 18999692788334310291356741)
          ·
            refine ⟨3562442397812683179629389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18999692788334310291356741 3562442397812683179629389)
            ·
              refine ⟨1335915899179756192361021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3562442397812683179629389 1335915899179756192361021)
              ·
                refine ⟨500968462192408572135383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1335915899179756192361021 500968462192408572135383)
                ·
                  refine ⟨751452693288612858203075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 500968462192408572135383 751452693288612858203075)
                  ·
                    refine ⟨1127179039932919287304613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 751452693288612858203075 1127179039932919287304613)
                    ·
                      refine ⟨211346069987422366369615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1127179039932919287304613 211346069987422366369615)
                      ·
                        rfl

theorem cell23_411595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 1, 4].length) (baseStart_411595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411595 prefixEnd_411595 := by exact prefixLift 411595
  have htrace : WordTrace (prefixWord ++ tailWord_411595) baseStart_411595 baseEnd_411595 := by
    simpa [prefixWord, tailWord_411595, baseEnd_411595] using wordTrace_append hprefix tailTrace_411595
  have hstable : (prefixWord ++ tailWord_411595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411595).length < 2 ^ (prefixWord ++ tailWord_411595).sum := by decide
  have hdescent : baseEnd_411595 < baseStart_411595 := by decide
  rcases family_descends (prefixWord ++ tailWord_411595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411606 : List Nat := [5, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_411606 : Nat := 118140960795 + 411606 * 2 ^ 59
def prefixEnd_411606 : Nat := 4983230072969 + 3 ^ 40 * 411606 * 2
def baseEnd_411606 : Nat := 211351718274621823332065

theorem tailTrace_411606 : CollatzResearch.WordTrace tailWord_411606 prefixEnd_411606 211351718274621823332065 := by
  unfold tailWord_411606
  simp only [CollatzResearch.WordTrace]
  refine ⟨938281509176827097081417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10008336097886155702201781 938281509176827097081417)
  ·
    refine ⟨703711131882620322811063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 938281509176827097081417 703711131882620322811063)
    ·
      refine ⟨1055566697823930484216595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 703711131882620322811063 1055566697823930484216595)
      ·
        refine ⟨1583350046735895726324893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1055566697823930484216595 1583350046735895726324893)
        ·
          refine ⟨593756267525960897371835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1583350046735895726324893 593756267525960897371835)
          ·
            refine ⟨890634401288941346057753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593756267525960897371835 890634401288941346057753)
            ·
              refine ⟨667975800966706009543315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 890634401288941346057753 667975800966706009543315)
              ·
                refine ⟨1001963701450059014314973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667975800966706009543315 1001963701450059014314973)
                ·
                  refine ⟨375736388043772130368115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1001963701450059014314973 375736388043772130368115)
                  ·
                    refine ⟨563604582065658195552173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 375736388043772130368115 563604582065658195552173)
                    ·
                      refine ⟨211351718274621823332065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 563604582065658195552173 211351718274621823332065)
                      ·
                        rfl

theorem cell23_411606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_411606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411606 prefixEnd_411606 := by exact prefixLift 411606
  have htrace : WordTrace (prefixWord ++ tailWord_411606) baseStart_411606 baseEnd_411606 := by
    simpa [prefixWord, tailWord_411606, baseEnd_411606] using wordTrace_append hprefix tailTrace_411606
  have hstable : (prefixWord ++ tailWord_411606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411606).length < 2 ^ (prefixWord ++ tailWord_411606).sum := by decide
  have hdescent : baseEnd_411606 < baseStart_411606 := by decide
  rcases family_descends (prefixWord ++ tailWord_411606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411608 : List Nat := [2, 1, 2, 2, 2, 2, 2, 2, 1, 1, 6]
def baseStart_411608 : Nat := 118140960795 + 411608 * 2 ^ 59
def prefixEnd_411608 : Nat := 4983230072969 + 3 ^ 40 * 411608 * 2
def baseEnd_411608 : Nat := 211352745235930815507055

theorem tailTrace_411608 : CollatzResearch.WordTrace tailWord_411608 prefixEnd_411608 211352745235930815507055 := by
  unfold tailWord_411608
  simp only [CollatzResearch.WordTrace]
  refine ⟨7506288546410993947437739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10008384728547991929916985 7506288546410993947437739)
  ·
    refine ⟨11259432819616490921156609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7506288546410993947437739 11259432819616490921156609)
    ·
      refine ⟨8444574614712368190867457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11259432819616490921156609 8444574614712368190867457)
      ·
        refine ⟨6333430961034276143150593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8444574614712368190867457 6333430961034276143150593)
        ·
          refine ⟨4750073220775707107362945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6333430961034276143150593 4750073220775707107362945)
          ·
            refine ⟨3562554915581780330522209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4750073220775707107362945 3562554915581780330522209)
            ·
              refine ⟨2671916186686335247891657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3562554915581780330522209 2671916186686335247891657)
              ·
                refine ⟨2003937140014751435918743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2671916186686335247891657 2003937140014751435918743)
                ·
                  refine ⟨3005905710022127153878115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2003937140014751435918743 3005905710022127153878115)
                  ·
                    refine ⟨4508858565033190730817173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3005905710022127153878115 4508858565033190730817173)
                    ·
                      refine ⟨211352745235930815507055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4508858565033190730817173 211352745235930815507055)
                      ·
                        rfl

theorem cell23_411608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_411608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411608 prefixEnd_411608 := by exact prefixLift 411608
  have htrace : WordTrace (prefixWord ++ tailWord_411608) baseStart_411608 baseEnd_411608 := by
    simpa [prefixWord, tailWord_411608, baseEnd_411608] using wordTrace_append hprefix tailTrace_411608
  have hstable : (prefixWord ++ tailWord_411608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411608).length < 2 ^ (prefixWord ++ tailWord_411608).sum := by decide
  have hdescent : baseEnd_411608 < baseStart_411608 := by decide
  rcases family_descends (prefixWord ++ tailWord_411608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411615 : List Nat := [1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 5]
def baseStart_411615 : Nat := 118140960795 + 411615 * 2 ^ 59
def prefixEnd_411615 : Nat := 4983230072969 + 3 ^ 40 * 411615 * 2
def baseEnd_411615 : Nat := 211356339600512288119523

theorem tailTrace_411615 : CollatzResearch.WordTrace tailWord_411615 prefixEnd_411615 211356339600512288119523 := by
  unfold tailWord_411615
  simp only [CollatzResearch.WordTrace]
  refine ⟨15012832403796628090380299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10008554935864418726920199 15012832403796628090380299)
  ·
    refine ⟨22519248605694942135570449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15012832403796628090380299 22519248605694942135570449)
    ·
      refine ⟨16889436454271206601677837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22519248605694942135570449 16889436454271206601677837)
      ·
        refine ⟨6333538670351702475629189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16889436454271206601677837 6333538670351702475629189)
        ·
          refine ⟨1187538500690944214180473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6333538670351702475629189 1187538500690944214180473)
          ·
            refine ⟨890653875518208160635355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1187538500690944214180473 890653875518208160635355)
            ·
              refine ⟨1335980813277312240953033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890653875518208160635355 1335980813277312240953033)
              ·
                refine ⟨1001985609957984180714775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1335980813277312240953033 1001985609957984180714775)
                ·
                  refine ⟨1502978414936976271072163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1001985609957984180714775 1502978414936976271072163)
                  ·
                    refine ⟨2254467622405464406608245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1502978414936976271072163 2254467622405464406608245)
                    ·
                      refine ⟨211356339600512288119523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2254467622405464406608245 211356339600512288119523)
                      ·
                        rfl

theorem cell23_411615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_411615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411615 prefixEnd_411615 := by exact prefixLift 411615
  have htrace : WordTrace (prefixWord ++ tailWord_411615) baseStart_411615 baseEnd_411615 := by
    simpa [prefixWord, tailWord_411615, baseEnd_411615] using wordTrace_append hprefix tailTrace_411615
  have hstable : (prefixWord ++ tailWord_411615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411615).length < 2 ^ (prefixWord ++ tailWord_411615).sum := by decide
  have hdescent : baseEnd_411615 < baseStart_411615 := by decide
  rcases family_descends (prefixWord ++ tailWord_411615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411645 : List Nat := [1, 4, 1, 1, 1, 2, 2, 4, 1, 3, 3]
def baseStart_411645 : Nat := 118140960795 + 411645 * 2 ^ 59
def prefixEnd_411645 : Nat := 4983230072969 + 3 ^ 40 * 411645 * 2
def baseEnd_411645 : Nat := 211371744020147170744385

theorem tailTrace_411645 : CollatzResearch.WordTrace tailWord_411645 prefixEnd_411645 211371744020147170744385 := by
  unfold tailWord_411645
  simp only [CollatzResearch.WordTrace]
  refine ⟨15013926593687943213972389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10009284395791962142648259 15013926593687943213972389)
  ·
    refine ⟨2815111236316489352619823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15013926593687943213972389 2815111236316489352619823)
    ·
      refine ⟨4222666854474734028929735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2815111236316489352619823 4222666854474734028929735)
      ·
        refine ⟨6334000281712101043394603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4222666854474734028929735 6334000281712101043394603)
        ·
          refine ⟨9501000422568151565091905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6334000281712101043394603 9501000422568151565091905)
          ·
            refine ⟨7125750316926113673818929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9501000422568151565091905 7125750316926113673818929)
            ·
              refine ⟨5344312737694585255364197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7125750316926113673818929 5344312737694585255364197)
              ·
                refine ⟨1002058638317734735380787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5344312737694585255364197 1002058638317734735380787)
                ·
                  refine ⟨1503087957476602103071181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1002058638317734735380787 1503087957476602103071181)
                  ·
                    refine ⟨563657984053725788651693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1503087957476602103071181 563657984053725788651693)
                    ·
                      refine ⟨211371744020147170744385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 563657984053725788651693 211371744020147170744385)
                      ·
                        rfl

theorem cell23_411645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_411645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411645 prefixEnd_411645 := by exact prefixLift 411645
  have htrace : WordTrace (prefixWord ++ tailWord_411645) baseStart_411645 baseEnd_411645 := by
    simpa [prefixWord, tailWord_411645, baseEnd_411645] using wordTrace_append hprefix tailTrace_411645
  have hstable : (prefixWord ++ tailWord_411645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411645).length < 2 ^ (prefixWord ++ tailWord_411645).sum := by decide
  have hdescent : baseEnd_411645 < baseStart_411645 := by decide
  rcases family_descends (prefixWord ++ tailWord_411645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411652 : List Nat := [2, 3, 2, 4, 1, 2, 9]
def baseStart_411652 : Nat := 118140960795 + 411652 * 2 ^ 59
def prefixEnd_411652 : Nat := 4983230072969 + 3 ^ 40 * 411652 * 2
def baseEnd_411652 : Nat := 2609572078823810411813

theorem tailTrace_411652 : CollatzResearch.WordTrace tailWord_411652 prefixEnd_411652 2609572078823810411813 := by
  unfold tailWord_411652
  simp only [CollatzResearch.WordTrace]
  refine ⟨7507090952331291704738605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10009454603108388939651473 7507090952331291704738605)
  ·
    refine ⟨2815159107124234389276977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7507090952331291704738605 2815159107124234389276977)
    ·
      refine ⟨2111369330343175791957733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2815159107124234389276977 2111369330343175791957733)
      ·
        refine ⟨395881749439345460992075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2111369330343175791957733 395881749439345460992075)
        ·
          refine ⟨593822624159018191488113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395881749439345460992075 593822624159018191488113)
          ·
            refine ⟨445366968119263643616085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 593822624159018191488113 445366968119263643616085)
            ·
              refine ⟨2609572078823810411813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 445366968119263643616085 2609572078823810411813)
              ·
                rfl

theorem cell23_411652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 9].length) (baseStart_411652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411652 prefixEnd_411652 := by exact prefixLift 411652
  have htrace : WordTrace (prefixWord ++ tailWord_411652) baseStart_411652 baseEnd_411652 := by
    simpa [prefixWord, tailWord_411652, baseEnd_411652] using wordTrace_append hprefix tailTrace_411652
  have hstable : (prefixWord ++ tailWord_411652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411652).length < 2 ^ (prefixWord ++ tailWord_411652).sum := by decide
  have hdescent : baseEnd_411652 < baseStart_411652 := by decide
  rcases family_descends (prefixWord ++ tailWord_411652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411662 : List Nat := [4, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3]
def baseStart_411662 : Nat := 118140960795 + 411662 * 2 ^ 59
def prefixEnd_411662 : Nat := 4983230072969 + 3 ^ 40 * 411662 * 2
def baseEnd_411662 : Nat := 211380473191273604231807

theorem tailTrace_411662 : CollatzResearch.WordTrace tailWord_411662 prefixEnd_411662 211380473191273604231807 := by
  unfold tailWord_411662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1876818329328294389667655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10009697756417570078227493 1876818329328294389667655)
  ·
    refine ⟨2815227493992441584501483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1876818329328294389667655 2815227493992441584501483)
    ·
      refine ⟨4222841240988662376752225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2815227493992441584501483 4222841240988662376752225)
      ·
        refine ⟨3167130930741496782564169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4222841240988662376752225 3167130930741496782564169)
        ·
          refine ⟨2375348198056122586923127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3167130930741496782564169 2375348198056122586923127)
          ·
            refine ⟨3563022297084183880384691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2375348198056122586923127 3563022297084183880384691)
            ·
              refine ⟨5344533445626275820577037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3563022297084183880384691 5344533445626275820577037)
              ·
                refine ⟨2004200042109853432716389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5344533445626275820577037 2004200042109853432716389)
                ·
                  refine ⟨375787507895597518634323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2004200042109853432716389 375787507895597518634323)
                  ·
                    refine ⟨563681261843396277951485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 375787507895597518634323 563681261843396277951485)
                    ·
                      refine ⟨211380473191273604231807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 563681261843396277951485 211380473191273604231807)
                      ·
                        rfl

theorem cell23_411662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_411662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411662 prefixEnd_411662 := by exact prefixLift 411662
  have htrace : WordTrace (prefixWord ++ tailWord_411662) baseStart_411662 baseEnd_411662 := by
    simpa [prefixWord, tailWord_411662, baseEnd_411662] using wordTrace_append hprefix tailTrace_411662
  have hstable : (prefixWord ++ tailWord_411662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411662).length < 2 ^ (prefixWord ++ tailWord_411662).sum := by decide
  have hdescent : baseEnd_411662 < baseStart_411662 := by decide
  rcases family_descends (prefixWord ++ tailWord_411662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411672 : List Nat := [2, 1, 2, 3, 2, 1, 2, 2, 3, 3, 2]
def baseStart_411672 : Nat := 118140960795 + 411672 * 2 ^ 59
def prefixEnd_411672 : Nat := 4983230072969 + 3 ^ 40 * 411672 * 2
def baseEnd_411672 : Nat := 211385607997818565106761

theorem tailTrace_411672 : CollatzResearch.WordTrace tailWord_411672 prefixEnd_411672 211385607997818565106761 := by
  unfold tailWord_411672
  simp only [CollatzResearch.WordTrace]
  refine ⟨7507455682295063412602635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10009940909726751216803513 7507455682295063412602635)
  ·
    refine ⟨11261183523442595118903953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7507455682295063412602635 11261183523442595118903953)
    ·
      refine ⟨8445887642581946339177965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11261183523442595118903953 8445887642581946339177965)
      ·
        refine ⟨3167207865968229877191737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8445887642581946339177965 3167207865968229877191737)
        ·
          refine ⟨2375405899476172407893803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3167207865968229877191737 2375405899476172407893803)
          ·
            refine ⟨3563108849214258611840705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2375405899476172407893803 3563108849214258611840705)
            ·
              refine ⟨2672331636910693958880529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3563108849214258611840705 2672331636910693958880529)
              ·
                refine ⟨2004248727683020469160397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2672331636910693958880529 2004248727683020469160397)
                ·
                  refine ⟨751593272881132675935149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2004248727683020469160397 751593272881132675935149)
                  ·
                    refine ⟨281847477330424753475681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 751593272881132675935149 281847477330424753475681)
                    ·
                      refine ⟨211385607997818565106761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 281847477330424753475681 211385607997818565106761)
                      ·
                        rfl

theorem cell23_411672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_411672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411672 prefixEnd_411672 := by exact prefixLift 411672
  have htrace : WordTrace (prefixWord ++ tailWord_411672) baseStart_411672 baseEnd_411672 := by
    simpa [prefixWord, tailWord_411672, baseEnd_411672] using wordTrace_append hprefix tailTrace_411672
  have hstable : (prefixWord ++ tailWord_411672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411672).length < 2 ^ (prefixWord ++ tailWord_411672).sum := by decide
  have hdescent : baseEnd_411672 < baseStart_411672 := by decide
  rcases family_descends (prefixWord ++ tailWord_411672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411728 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 8]
def baseStart_411728 : Nat := 118140960795 + 411728 * 2 ^ 59
def prefixEnd_411728 : Nat := 4983230072969 + 3 ^ 40 * 411728 * 2
def baseEnd_411728 : Nat := 211414362914470346006503

theorem tailTrace_411728 : CollatzResearch.WordTrace tailWord_411728 prefixEnd_411728 211414362914470346006503 := by
  unfold tailWord_411728
  simp only [CollatzResearch.WordTrace]
  refine ⟨7508476926193624194621919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10011302568258165592829225 7508476926193624194621919)
  ·
    refine ⟨11262715389290436291932879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7508476926193624194621919 11262715389290436291932879)
    ·
      refine ⟨16894073083935654437899319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11262715389290436291932879 16894073083935654437899319)
      ·
        refine ⟨25341109625903481656848979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16894073083935654437899319 25341109625903481656848979)
        ·
          refine ⟨38011664438855222485273469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25341109625903481656848979 38011664438855222485273469)
          ·
            refine ⟨14254374164570708431977551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38011664438855222485273469 14254374164570708431977551)
            ·
              refine ⟨21381561246856062647966327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14254374164570708431977551 21381561246856062647966327)
              ·
                refine ⟨32072341870284093971949491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21381561246856062647966327 32072341870284093971949491)
                ·
                  refine ⟨48108512805426140957924237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32072341870284093971949491 48108512805426140957924237)
                  ·
                    refine ⟨18040692302034802859221589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48108512805426140957924237 18040692302034802859221589)
                    ·
                      refine ⟨211414362914470346006503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 18040692302034802859221589 211414362914470346006503)
                      ·
                        rfl

theorem cell23_411728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_411728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411728 prefixEnd_411728 := by exact prefixLift 411728
  have htrace : WordTrace (prefixWord ++ tailWord_411728) baseStart_411728 baseEnd_411728 := by
    simpa [prefixWord, tailWord_411728, baseEnd_411728] using wordTrace_append hprefix tailTrace_411728
  have hstable : (prefixWord ++ tailWord_411728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411728).length < 2 ^ (prefixWord ++ tailWord_411728).sum := by decide
  have hdescent : baseEnd_411728 < baseStart_411728 := by decide
  rcases family_descends (prefixWord ++ tailWord_411728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411735 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 3]
def baseStart_411735 : Nat := 118140960795 + 411735 * 2 ^ 59
def prefixEnd_411735 : Nat := 4983230072969 + 3 ^ 40 * 411735 * 2
def baseEnd_411735 : Nat := 211417957279051818618971

theorem tailTrace_411735 : CollatzResearch.WordTrace tailWord_411735 prefixEnd_411735 211417957279051818618971 := by
  unfold tailWord_411735
  simp only [CollatzResearch.WordTrace]
  refine ⟨15017209163361888584748659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10011472775574592389832439 15017209163361888584748659)
  ·
    refine ⟨22525813745042832877122989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15017209163361888584748659 22525813745042832877122989)
    ·
      refine ⟨8447180154391062328921121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22525813745042832877122989 8447180154391062328921121)
      ·
        refine ⟨6335385115793296746690841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8447180154391062328921121 6335385115793296746690841)
        ·
          refine ⟨4751538836844972560018131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6335385115793296746690841 4751538836844972560018131)
          ·
            refine ⟨7127308255267458840027197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4751538836844972560018131 7127308255267458840027197)
            ·
              refine ⟨2672740595725297065010199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7127308255267458840027197 2672740595725297065010199)
              ·
                refine ⟨4009110893587945597515299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2672740595725297065010199 4009110893587945597515299)
                ·
                  refine ⟨6013666340381918396272949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4009110893587945597515299 6013666340381918396272949)
                  ·
                    refine ⟨563781219410804849650589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6013666340381918396272949 563781219410804849650589)
                    ·
                      refine ⟨211417957279051818618971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 563781219410804849650589 211417957279051818618971)
                      ·
                        rfl

theorem cell23_411735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_411735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411735 prefixEnd_411735 := by exact prefixLift 411735
  have htrace : WordTrace (prefixWord ++ tailWord_411735) baseStart_411735 baseEnd_411735 := by
    simpa [prefixWord, tailWord_411735, baseEnd_411735] using wordTrace_append hprefix tailTrace_411735
  have hstable : (prefixWord ++ tailWord_411735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411735).length < 2 ^ (prefixWord ++ tailWord_411735).sum := by decide
  have hdescent : baseEnd_411735 < baseStart_411735 := by decide
  rcases family_descends (prefixWord ++ tailWord_411735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411792 : List Nat := [2, 1, 1, 1, 1, 1, 5, 3, 2, 4, 2]
def baseStart_411792 : Nat := 118140960795 + 411792 * 2 ^ 59
def prefixEnd_411792 : Nat := 4983230072969 + 3 ^ 40 * 411792 * 2
def baseEnd_411792 : Nat := 211447225676358095606209

theorem tailTrace_411792 : CollatzResearch.WordTrace tailWord_411792 prefixEnd_411792 211447225676358095606209 := by
  unfold tailWord_411792
  simp only [CollatzResearch.WordTrace]
  refine ⟨7509644062077693659786815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10012858749436924879715753 7509644062077693659786815)
  ·
    refine ⟨11264466093116540489680223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7509644062077693659786815 11264466093116540489680223)
    ·
      refine ⟨16896699139674810734520335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11264466093116540489680223 16896699139674810734520335)
      ·
        refine ⟨25345048709512216101780503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16896699139674810734520335 25345048709512216101780503)
        ·
          refine ⟨38017573064268324152670755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25345048709512216101780503 38017573064268324152670755)
          ·
            refine ⟨57026359596402486229006133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38017573064268324152670755 57026359596402486229006133)
            ·
              refine ⟨5346221212162733083969325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57026359596402486229006133 5346221212162733083969325)
              ·
                refine ⟨2004832954561024906488497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5346221212162733083969325 2004832954561024906488497)
                ·
                  refine ⟨1503624715920768679866373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2004832954561024906488497 1503624715920768679866373)
                  ·
                    refine ⟨281929634235144127474945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1503624715920768679866373 281929634235144127474945)
                    ·
                      refine ⟨211447225676358095606209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 281929634235144127474945 211447225676358095606209)
                      ·
                        rfl

theorem cell23_411792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 2, 4, 2].length) (baseStart_411792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411792 prefixEnd_411792 := by exact prefixLift 411792
  have htrace : WordTrace (prefixWord ++ tailWord_411792) baseStart_411792 baseEnd_411792 := by
    simpa [prefixWord, tailWord_411792, baseEnd_411792] using wordTrace_append hprefix tailTrace_411792
  have hstable : (prefixWord ++ tailWord_411792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411792).length < 2 ^ (prefixWord ++ tailWord_411792).sum := by decide
  have hdescent : baseEnd_411792 < baseStart_411792 := by decide
  rcases family_descends (prefixWord ++ tailWord_411792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411836 : List Nat := [2, 2, 2, 3, 3, 2, 1, 1, 3, 4]
def baseStart_411836 : Nat := 118140960795 + 411836 * 2 ^ 59
def prefixEnd_411836 : Nat := 4983230072969 + 3 ^ 40 * 411836 * 2
def baseEnd_411836 : Nat := 70489939608385307818669

theorem tailTrace_411836 : CollatzResearch.WordTrace tailWord_411836 prefixEnd_411836 70489939608385307818669 := by
  unfold tailWord_411836
  simp only [CollatzResearch.WordTrace]
  refine ⟨7510446467997991417087681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10013928623997321889450241 7510446467997991417087681)
  ·
    refine ⟨5632834850998493562815761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7510446467997991417087681 5632834850998493562815761)
    ·
      refine ⟨4224626138248870172111821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5632834850998493562815761 4224626138248870172111821)
      ·
        refine ⟨1584234801843326314541933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4224626138248870172111821 1584234801843326314541933)
        ·
          refine ⟨594088050691247367953225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1584234801843326314541933 594088050691247367953225)
          ·
            refine ⟨445566038018435525964919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 594088050691247367953225 445566038018435525964919)
            ·
              refine ⟨668349057027653288947379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 445566038018435525964919 668349057027653288947379)
              ·
                refine ⟨1002523585541479933421069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668349057027653288947379 1002523585541479933421069)
                ·
                  refine ⟨375946344578054975032901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1002523585541479933421069 375946344578054975032901)
                  ·
                    refine ⟨70489939608385307818669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 375946344578054975032901 70489939608385307818669)
                    ·
                      rfl

theorem cell23_411836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_411836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411836 prefixEnd_411836 := by exact prefixLift 411836
  have htrace : WordTrace (prefixWord ++ tailWord_411836) baseStart_411836 baseEnd_411836 := by
    simpa [prefixWord, tailWord_411836, baseEnd_411836] using wordTrace_append hprefix tailTrace_411836
  have hstable : (prefixWord ++ tailWord_411836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411836).length < 2 ^ (prefixWord ++ tailWord_411836).sum := by decide
  have hdescent : baseEnd_411836 < baseStart_411836 := by decide
  rcases family_descends (prefixWord ++ tailWord_411836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411876 : List Nat := [2, 3, 1, 1, 1, 2, 1, 7, 1, 1, 3]
def baseStart_411876 : Nat := 118140960795 + 411876 * 2 ^ 59
def prefixEnd_411876 : Nat := 4983230072969 + 3 ^ 40 * 411876 * 2
def baseEnd_411876 : Nat := 211490358051335766955823

theorem tailTrace_411876 : CollatzResearch.WordTrace tailWord_411876 prefixEnd_411876 211490358051335766955823 := by
  unfold tailWord_411876
  simp only [CollatzResearch.WordTrace]
  refine ⟨7511175927925534832815741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10014901237234046443754321 7511175927925534832815741)
  ·
    refine ⟨2816690972972075562305903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7511175927925534832815741 2816690972972075562305903)
    ·
      refine ⟨4225036459458113343458855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2816690972972075562305903 4225036459458113343458855)
      ·
        refine ⟨6337554689187170015188283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4225036459458113343458855 6337554689187170015188283)
        ·
          refine ⟨9506332033780755022782425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6337554689187170015188283 9506332033780755022782425)
          ·
            refine ⟨7129749025335566267086819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9506332033780755022782425 7129749025335566267086819)
            ·
              refine ⟨10694623538003349400630229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7129749025335566267086819 10694623538003349400630229)
              ·
                refine ⟨250655239171953501577271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 10694623538003349400630229 250655239171953501577271)
                ·
                  refine ⟨375982858757930252365907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250655239171953501577271 375982858757930252365907)
                  ·
                    refine ⟨563974288136895378548861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 375982858757930252365907 563974288136895378548861)
                    ·
                      refine ⟨211490358051335766955823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 563974288136895378548861 211490358051335766955823)
                      ·
                        rfl

theorem cell23_411876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 1, 1, 3].length) (baseStart_411876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411876 prefixEnd_411876 := by exact prefixLift 411876
  have htrace : WordTrace (prefixWord ++ tailWord_411876) baseStart_411876 baseEnd_411876 := by
    simpa [prefixWord, tailWord_411876, baseEnd_411876] using wordTrace_append hprefix tailTrace_411876
  have hstable : (prefixWord ++ tailWord_411876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411876).length < 2 ^ (prefixWord ++ tailWord_411876).sum := by decide
  have hdescent : baseEnd_411876 < baseStart_411876 := by decide
  rcases family_descends (prefixWord ++ tailWord_411876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411899 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 9, 2, 2]
def baseStart_411899 : Nat := 118140960795 + 411899 * 2 ^ 59
def prefixEnd_411899 : Nat := 4983230072969 + 3 ^ 40 * 411899 * 2
def baseEnd_411899 : Nat := 211502168106389176968217

theorem tailTrace_411899 : CollatzResearch.WordTrace tailWord_411899 prefixEnd_411899 211502168106389176968217 := by
  unfold tailWord_411899
  simp only [CollatzResearch.WordTrace]
  refine ⟨15023190734767744593718751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10015460489845163062479167 15023190734767744593718751)
  ·
    refine ⟨22534786102151616890578127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15023190734767744593718751 22534786102151616890578127)
    ·
      refine ⟨33802179153227425335867191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22534786102151616890578127 33802179153227425335867191)
      ·
        refine ⟨50703268729841138003800787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33802179153227425335867191 50703268729841138003800787)
        ·
          refine ⟨76054903094761707005701181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50703268729841138003800787 76054903094761707005701181)
          ·
            refine ⟨28520588660535640127137943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76054903094761707005701181 28520588660535640127137943)
            ·
              refine ⟨42780882990803460190706915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28520588660535640127137943 42780882990803460190706915)
              ·
                refine ⟨64171324486205190286060373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42780882990803460190706915 64171324486205190286060373)
                ·
                  refine ⟨376003854411358536832385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64171324486205190286060373 376003854411358536832385)
                  ·
                    refine ⟨282002890808518902624289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 376003854411358536832385 282002890808518902624289)
                    ·
                      refine ⟨211502168106389176968217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 282002890808518902624289 211502168106389176968217)
                      ·
                        rfl

theorem cell23_411899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 2, 2].length) (baseStart_411899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411899 prefixEnd_411899 := by exact prefixLift 411899
  have htrace : WordTrace (prefixWord ++ tailWord_411899) baseStart_411899 baseEnd_411899 := by
    simpa [prefixWord, tailWord_411899, baseEnd_411899] using wordTrace_append hprefix tailTrace_411899
  have hstable : (prefixWord ++ tailWord_411899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411899).length < 2 ^ (prefixWord ++ tailWord_411899).sum := by decide
  have hdescent : baseEnd_411899 < baseStart_411899 := by decide
  rcases family_descends (prefixWord ++ tailWord_411899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411916 : List Nat := [2, 2, 1, 2, 2, 2, 3, 2, 3, 2, 2]
def baseStart_411916 : Nat := 118140960795 + 411916 * 2 ^ 59
def prefixEnd_411916 : Nat := 4983230072969 + 3 ^ 40 * 411916 * 2
def baseEnd_411916 : Nat := 211510897277515610455639

theorem tailTrace_411916 : CollatzResearch.WordTrace tailWord_411916 prefixEnd_411916 211510897277515610455639 := by
  unfold tailWord_411916
  simp only [CollatzResearch.WordTrace]
  refine ⟨7511905387853078248543801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10015873850470770998058401 7511905387853078248543801)
  ·
    refine ⟨5633929040889808686407851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7511905387853078248543801 5633929040889808686407851)
    ·
      refine ⟨8450893561334713029611777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5633929040889808686407851 8450893561334713029611777)
      ·
        refine ⟨6338170171001034772208833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8450893561334713029611777 6338170171001034772208833)
        ·
          refine ⟨4753627628250776079156625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6338170171001034772208833 4753627628250776079156625)
          ·
            refine ⟨3565220721188082059367469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4753627628250776079156625 3565220721188082059367469)
            ·
              refine ⟨1336957770445530772262801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3565220721188082059367469 1336957770445530772262801)
              ·
                refine ⟨1002718327834148079197101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1336957770445530772262801 1002718327834148079197101)
                ·
                  refine ⟨376019372937805529698913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1002718327834148079197101 376019372937805529698913)
                  ·
                    refine ⟨282014529703354147274185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 376019372937805529698913 282014529703354147274185)
                    ·
                      refine ⟨211510897277515610455639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 282014529703354147274185 211510897277515610455639)
                      ·
                        rfl

theorem cell23_411916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 3, 2, 2].length) (baseStart_411916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411916 prefixEnd_411916 := by exact prefixLift 411916
  have htrace : WordTrace (prefixWord ++ tailWord_411916) baseStart_411916 baseEnd_411916 := by
    simpa [prefixWord, tailWord_411916, baseEnd_411916] using wordTrace_append hprefix tailTrace_411916
  have hstable : (prefixWord ++ tailWord_411916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411916).length < 2 ^ (prefixWord ++ tailWord_411916).sum := by decide
  have hdescent : baseEnd_411916 < baseStart_411916 := by decide
  rcases family_descends (prefixWord ++ tailWord_411916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411936 : List Nat := [2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 3]
def baseStart_411936 : Nat := 118140960795 + 411936 * 2 ^ 59
def prefixEnd_411936 : Nat := 4983230072969 + 3 ^ 40 * 411936 * 2
def baseEnd_411936 : Nat := 211521166890605532205547

theorem tailTrace_411936 : CollatzResearch.WordTrace tailWord_411936 prefixEnd_411936 211521166890605532205547 := by
  unfold tailWord_411936
  simp only [CollatzResearch.WordTrace]
  refine ⟨7512270117816849956407831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10016360157089133275210441 7512270117816849956407831)
  ·
    refine ⟨11268405176725274934611747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7512270117816849956407831 11268405176725274934611747)
    ·
      refine ⟨16902607765087912401917621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11268405176725274934611747 16902607765087912401917621)
      ·
        refine ⟨1584619477976991787679777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16902607765087912401917621 1584619477976991787679777)
        ·
          refine ⟨1188464608482743840759833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1584619477976991787679777 1188464608482743840759833)
          ·
            refine ⟨891348456362057880569875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1188464608482743840759833 891348456362057880569875)
            ·
              refine ⟨1337022684543086820854813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 891348456362057880569875 1337022684543086820854813)
              ·
                refine ⟨501383506703657557820555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1337022684543086820854813 501383506703657557820555)
                ·
                  refine ⟨752075260055486336730833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 501383506703657557820555 752075260055486336730833)
                  ·
                    refine ⟨564056445041614752548125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 752075260055486336730833 564056445041614752548125)
                    ·
                      refine ⟨211521166890605532205547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 564056445041614752548125 211521166890605532205547)
                      ·
                        rfl

theorem cell23_411936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_411936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411936 prefixEnd_411936 := by exact prefixLift 411936
  have htrace : WordTrace (prefixWord ++ tailWord_411936) baseStart_411936 baseEnd_411936 := by
    simpa [prefixWord, tailWord_411936, baseEnd_411936] using wordTrace_append hprefix tailTrace_411936
  have hstable : (prefixWord ++ tailWord_411936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411936).length < 2 ^ (prefixWord ++ tailWord_411936).sum := by decide
  have hdescent : baseEnd_411936 < baseStart_411936 := by decide
  rcases family_descends (prefixWord ++ tailWord_411936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411959 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 5, 3, 2]
def baseStart_411959 : Nat := 118140960795 + 411959 * 2 ^ 59
def prefixEnd_411959 : Nat := 4983230072969 + 3 ^ 40 * 411959 * 2
def baseEnd_411959 : Nat := 211532976945658942217941

theorem tailTrace_411959 : CollatzResearch.WordTrace tailWord_411959 prefixEnd_411959 211532976945658942217941 := by
  unfold tailWord_411959
  simp only [CollatzResearch.WordTrace]
  refine ⟨15025379114550374840902931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10016919409700249893935287 15025379114550374840902931)
  ·
    refine ⟨22538068671825562261354397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15025379114550374840902931 22538068671825562261354397)
    ·
      refine ⟨8451775751934585848007899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22538068671825562261354397 8451775751934585848007899)
      ·
        refine ⟨12677663627901878772011849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8451775751934585848007899 12677663627901878772011849)
        ·
          refine ⟨9508247720926409079008887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12677663627901878772011849 9508247720926409079008887)
          ·
            refine ⟨14262371581389613618513331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9508247720926409079008887 14262371581389613618513331)
            ·
              refine ⟨21393557372084420427769997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14262371581389613618513331 21393557372084420427769997)
              ·
                refine ⟨8022584014531657660413749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21393557372084420427769997 8022584014531657660413749)
                ·
                  refine ⟨752117251362342905663789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8022584014531657660413749 752117251362342905663789)
                  ·
                    refine ⟨282043969260878589623921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 752117251362342905663789 282043969260878589623921)
                    ·
                      refine ⟨211532976945658942217941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 282043969260878589623921 211532976945658942217941)
                      ·
                        rfl

theorem cell23_411959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 3, 2].length) (baseStart_411959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411959 prefixEnd_411959 := by exact prefixLift 411959
  have htrace : WordTrace (prefixWord ++ tailWord_411959) baseStart_411959 baseEnd_411959 := by
    simpa [prefixWord, tailWord_411959, baseEnd_411959] using wordTrace_append hprefix tailTrace_411959
  have hstable : (prefixWord ++ tailWord_411959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411959).length < 2 ^ (prefixWord ++ tailWord_411959).sum := by decide
  have hdescent : baseEnd_411959 < baseStart_411959 := by decide
  rcases family_descends (prefixWord ++ tailWord_411959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411966 : List Nat := [4, 2, 1, 2, 1, 2, 3, 1, 1, 3, 3]
def baseStart_411966 : Nat := 118140960795 + 411966 * 2 ^ 59
def prefixEnd_411966 : Nat := 4983230072969 + 3 ^ 40 * 411966 * 2
def baseEnd_411966 : Nat := 211536571310240414830409

theorem tailTrace_411966 : CollatzResearch.WordTrace tailWord_411966 prefixEnd_411966 211536571310240414830409 := by
  unfold tailWord_411966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1878204303190626879550969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10017089617016676690938501 1878204303190626879550969)
  ·
    refine ⟨1408653227392970159663227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1878204303190626879550969 1408653227392970159663227)
    ·
      refine ⟨2112979841089455239494841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1408653227392970159663227 2112979841089455239494841)
      ·
        refine ⟨1584734880817091429621131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2112979841089455239494841 1584734880817091429621131)
        ·
          refine ⟨2377102321225637144431697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1584734880817091429621131 2377102321225637144431697)
          ·
            refine ⟨1782826740919227858323773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2377102321225637144431697 1782826740919227858323773)
            ·
              refine ⟨668560027844710446871415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1782826740919227858323773 668560027844710446871415)
              ·
                refine ⟨1002840041767065670307123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668560027844710446871415 1002840041767065670307123)
                ·
                  refine ⟨1504260062650598505460685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1002840041767065670307123 1504260062650598505460685)
                  ·
                    refine ⟨564097523493974439547757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1504260062650598505460685 564097523493974439547757)
                    ·
                      refine ⟨211536571310240414830409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 564097523493974439547757 211536571310240414830409)
                      ·
                        rfl

theorem cell23_411966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_411966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411966 prefixEnd_411966 := by exact prefixLift 411966
  have htrace : WordTrace (prefixWord ++ tailWord_411966) baseStart_411966 baseEnd_411966 := by
    simpa [prefixWord, tailWord_411966, baseEnd_411966] using wordTrace_append hprefix tailTrace_411966
  have hstable : (prefixWord ++ tailWord_411966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411966).length < 2 ^ (prefixWord ++ tailWord_411966).sum := by decide
  have hdescent : baseEnd_411966 < baseStart_411966 := by decide
  rcases family_descends (prefixWord ++ tailWord_411966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411976 : List Nat := [2, 1, 3, 1, 1, 2, 3, 4, 1, 3, 2]
def baseStart_411976 : Nat := 118140960795 + 411976 * 2 ^ 59
def prefixEnd_411976 : Nat := 4983230072969 + 3 ^ 40 * 411976 * 2
def baseEnd_411976 : Nat := 211541706116785375705363

theorem tailTrace_411976 : CollatzResearch.WordTrace tailWord_411976 prefixEnd_411976 211541706116785375705363 := by
  unfold tailWord_411976
  simp only [CollatzResearch.WordTrace]
  refine ⟨7512999577744393372135891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10017332770325857829514521 7512999577744393372135891)
  ·
    refine ⟨11269499366616590058203837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7512999577744393372135891 11269499366616590058203837)
    ·
      refine ⟨4226062262481221271826439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11269499366616590058203837 4226062262481221271826439)
      ·
        refine ⟨6339093393721831907739659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4226062262481221271826439 6339093393721831907739659)
        ·
          refine ⟨9508640090582747861609489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6339093393721831907739659 9508640090582747861609489)
          ·
            refine ⟨7131480067937060896207117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9508640090582747861609489 7131480067937060896207117)
            ·
              refine ⟨2674305025476397836077669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7131480067937060896207117 2674305025476397836077669)
              ·
                refine ⟨501432192276824594264563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2674305025476397836077669 501432192276824594264563)
                ·
                  refine ⟨752148288415236891396845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 501432192276824594264563 752148288415236891396845)
                  ·
                    refine ⟨282055608155713834273817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 752148288415236891396845 282055608155713834273817)
                    ·
                      refine ⟨211541706116785375705363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 282055608155713834273817 211541706116785375705363)
                      ·
                        rfl

theorem cell23_411976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 1, 3, 2].length) (baseStart_411976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411976 prefixEnd_411976 := by exact prefixLift 411976
  have htrace : WordTrace (prefixWord ++ tailWord_411976) baseStart_411976 baseEnd_411976 := by
    simpa [prefixWord, tailWord_411976, baseEnd_411976] using wordTrace_append hprefix tailTrace_411976
  have hstable : (prefixWord ++ tailWord_411976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411976).length < 2 ^ (prefixWord ++ tailWord_411976).sum := by decide
  have hdescent : baseEnd_411976 < baseStart_411976 := by decide
  rcases family_descends (prefixWord ++ tailWord_411976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411982 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 4, 6]
def baseStart_411982 : Nat := 118140960795 + 411982 * 2 ^ 59
def prefixEnd_411982 : Nat := 4983230072969 + 3 ^ 40 * 411982 * 2
def baseEnd_411982 : Nat := 70514929000237450743445

theorem tailTrace_411982 : CollatzResearch.WordTrace tailWord_411982 prefixEnd_411982 70514929000237450743445 := by
  unfold tailWord_411982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1878277249183381221123775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10017478662311366512660133 1878277249183381221123775)
  ·
    refine ⟨2817415873775071831685663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1878277249183381221123775 2817415873775071831685663)
    ·
      refine ⟨4226123810662607747528495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2817415873775071831685663 4226123810662607747528495)
      ·
        refine ⟨6339185715993911621292743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4226123810662607747528495 6339185715993911621292743)
        ·
          refine ⟨9508778573990867431939115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6339185715993911621292743 9508778573990867431939115)
          ·
            refine ⟨14263167860986301147908673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9508778573990867431939115 14263167860986301147908673)
            ·
              refine ⟨10697375895739725860931505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14263167860986301147908673 10697375895739725860931505)
              ·
                refine ⟨8023031921804794395698629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10697375895739725860931505 8023031921804794395698629)
                ·
                  refine ⟨1504318485338398949193493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8023031921804794395698629 1504318485338398949193493)
                  ·
                    refine ⟨70514929000237450743445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1504318485338398949193493 70514929000237450743445)
                    ·
                      rfl

theorem cell23_411982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_411982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_411982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_411982 prefixEnd_411982 := by exact prefixLift 411982
  have htrace : WordTrace (prefixWord ++ tailWord_411982) baseStart_411982 baseEnd_411982 := by
    simpa [prefixWord, tailWord_411982, baseEnd_411982] using wordTrace_append hprefix tailTrace_411982
  have hstable : (prefixWord ++ tailWord_411982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411982).length < 2 ^ (prefixWord ++ tailWord_411982).sum := by decide
  have hdescent : baseEnd_411982 < baseStart_411982 := by decide
  rcases family_descends (prefixWord ++ tailWord_411982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412049 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 3, 7, 2]
def baseStart_412049 : Nat := 118140960795 + 412049 * 2 ^ 59
def prefixEnd_412049 : Nat := 4983230072969 + 3 ^ 40 * 412049 * 2
def baseEnd_412049 : Nat := 211579190204563590092527

theorem tailTrace_412049 : CollatzResearch.WordTrace tailWord_412049 prefixEnd_412049 211579190204563590092527 := by
  unfold tailWord_412049
  simp only [CollatzResearch.WordTrace]
  refine ⟨15028661684224320211679201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10019107789482880141119467 15028661684224320211679201)
  ·
    refine ⟨11271496263168240158759401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15028661684224320211679201 11271496263168240158759401)
    ·
      refine ⟨8453622197376180119069551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11271496263168240158759401 8453622197376180119069551)
      ·
        refine ⟨12680433296064270178604327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8453622197376180119069551 12680433296064270178604327)
        ·
          refine ⟨19020649944096405267906491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12680433296064270178604327 19020649944096405267906491)
          ·
            refine ⟨28530974916144607901859737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19020649944096405267906491 28530974916144607901859737)
            ·
              refine ⟨21398231187108455926394803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28530974916144607901859737 21398231187108455926394803)
              ·
                refine ⟨32097346780662683889592205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21398231187108455926394803 32097346780662683889592205)
                ·
                  refine ⟨12036505042748506458597077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32097346780662683889592205 12036505042748506458597077)
                  ·
                    refine ⟨282105586939418120123369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12036505042748506458597077 282105586939418120123369)
                    ·
                      refine ⟨211579190204563590092527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 282105586939418120123369 211579190204563590092527)
                      ·
                        rfl

theorem cell23_412049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 7, 2].length) (baseStart_412049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412049 prefixEnd_412049 := by exact prefixLift 412049
  have htrace : WordTrace (prefixWord ++ tailWord_412049) baseStart_412049 baseEnd_412049 := by
    simpa [prefixWord, tailWord_412049, baseEnd_412049] using wordTrace_append hprefix tailTrace_412049
  have hstable : (prefixWord ++ tailWord_412049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412049).length < 2 ^ (prefixWord ++ tailWord_412049).sum := by decide
  have hdescent : baseEnd_412049 < baseStart_412049 := by decide
  rcases family_descends (prefixWord ++ tailWord_412049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412066 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 1, 7, 2]
def baseStart_412066 : Nat := 118140960795 + 412066 * 2 ^ 59
def prefixEnd_412066 : Nat := 4983230072969 + 3 ^ 40 * 412066 * 2
def baseEnd_412066 : Nat := 211587919375690023579949

theorem tailTrace_412066 : CollatzResearch.WordTrace tailWord_412066 prefixEnd_412066 211587919375690023579949 := by
  unfold tailWord_412066
  simp only [CollatzResearch.WordTrace]
  refine ⟨3757320431290683028762013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10019521150108488076698701 3757320431290683028762013)
  ·
    refine ⟨1408995161734006135785755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3757320431290683028762013 1408995161734006135785755)
    ·
      refine ⟨2113492742601009203678633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1408995161734006135785755 2113492742601009203678633)
      ·
        refine ⟨1585119556950756902758975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2113492742601009203678633 1585119556950756902758975)
        ·
          refine ⟨2377679335426135354138463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1585119556950756902758975 2377679335426135354138463)
          ·
            refine ⟨3566519003139203031207695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2377679335426135354138463 3566519003139203031207695)
            ·
              refine ⟨5349778504708804546811543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3566519003139203031207695 5349778504708804546811543)
              ·
                refine ⟨8024667757063206820217315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5349778504708804546811543 8024667757063206820217315)
                ·
                  refine ⟨12037001635594810230325973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8024667757063206820217315 12037001635594810230325973)
                  ·
                    refine ⟨282117225834253364773265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12037001635594810230325973 282117225834253364773265)
                    ·
                      refine ⟨211587919375690023579949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 282117225834253364773265 211587919375690023579949)
                      ·
                        rfl

theorem cell23_412066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_412066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412066 prefixEnd_412066 := by exact prefixLift 412066
  have htrace : WordTrace (prefixWord ++ tailWord_412066) baseStart_412066 baseEnd_412066 := by
    simpa [prefixWord, tailWord_412066, baseEnd_412066] using wordTrace_append hprefix tailTrace_412066
  have hstable : (prefixWord ++ tailWord_412066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412066).length < 2 ^ (prefixWord ++ tailWord_412066).sum := by decide
  have hdescent : baseEnd_412066 < baseStart_412066 := by decide
  rcases family_descends (prefixWord ++ tailWord_412066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412097 : List Nat := [1, 2, 7, 1, 1, 1, 2, 3, 5]
def baseStart_412097 : Nat := 118140960795 + 412097 * 2 ^ 59
def prefixEnd_412097 : Nat := 4983230072969 + 3 ^ 40 * 412097 * 2
def baseEnd_412097 : Nat := 23511537475108822476923

theorem tailTrace_412097 : CollatzResearch.WordTrace tailWord_412097 prefixEnd_412097 23511537475108822476923 := by
  unfold tailWord_412097
  simp only [CollatzResearch.WordTrace]
  refine ⟨15030412388050424409426545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10020274925366949606284363 15030412388050424409426545)
  ·
    refine ⟨11272809291037818307069909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15030412388050424409426545 11272809291037818307069909)
    ·
      refine ⟨264206467758698866571951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 11272809291037818307069909 264206467758698866571951)
      ·
        refine ⟨396309701638048299857927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264206467758698866571951 396309701638048299857927)
        ·
          refine ⟨594464552457072449786891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396309701638048299857927 594464552457072449786891)
          ·
            refine ⟨891696828685608674680337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594464552457072449786891 891696828685608674680337)
            ·
              refine ⟨668772621514206506010253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 891696828685608674680337 668772621514206506010253)
              ·
                refine ⟨250789733067827439753845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 668772621514206506010253 250789733067827439753845)
                ·
                  refine ⟨23511537475108822476923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 250789733067827439753845 23511537475108822476923)
                  ·
                    rfl

theorem cell23_412097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 5].length) (baseStart_412097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412097 prefixEnd_412097 := by exact prefixLift 412097
  have htrace : WordTrace (prefixWord ++ tailWord_412097) baseStart_412097 baseEnd_412097 := by
    simpa [prefixWord, tailWord_412097, baseEnd_412097] using wordTrace_append hprefix tailTrace_412097
  have hstable : (prefixWord ++ tailWord_412097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412097).length < 2 ^ (prefixWord ++ tailWord_412097).sum := by decide
  have hdescent : baseEnd_412097 < baseStart_412097 := by decide
  rcases family_descends (prefixWord ++ tailWord_412097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412200 : List Nat := [2, 1, 5, 2, 1, 3, 1, 2, 1, 5]
def baseStart_412200 : Nat := 118140960795 + 412200 * 2 ^ 59
def prefixEnd_412200 : Nat := 4983230072969 + 3 ^ 40 * 412200 * 2
def baseEnd_412200 : Nat := 70552241927797499768111

theorem tailTrace_412200 : CollatzResearch.WordTrace tailWord_412200 prefixEnd_412200 70552241927797499768111 := by
  unfold tailWord_412200
  simp only [CollatzResearch.WordTrace]
  refine ⟨7517084553338636500213027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10022779404451515333617369 7517084553338636500213027)
  ·
    refine ⟨11275626830007954750319541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7517084553338636500213027 11275626830007954750319541)
    ·
      refine ⟨1057090015313245757842457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11275626830007954750319541 1057090015313245757842457)
      ·
        refine ⟨792817511484934318381843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1057090015313245757842457 792817511484934318381843)
        ·
          refine ⟨1189226267227401477572765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 792817511484934318381843 1189226267227401477572765)
          ·
            refine ⟨445959850210275554089787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1189226267227401477572765 445959850210275554089787)
            ·
              refine ⟨668939775315413331134681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 445959850210275554089787 668939775315413331134681)
              ·
                refine ⟨501704831486559998351011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 668939775315413331134681 501704831486559998351011)
                ·
                  refine ⟨752557247229839997526517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 501704831486559998351011 752557247229839997526517)
                  ·
                    refine ⟨70552241927797499768111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 752557247229839997526517 70552241927797499768111)
                    ·
                      rfl

theorem cell23_412200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_412200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412200 prefixEnd_412200 := by exact prefixLift 412200
  have htrace : WordTrace (prefixWord ++ tailWord_412200) baseStart_412200 baseEnd_412200 := by
    simpa [prefixWord, tailWord_412200, baseEnd_412200] using wordTrace_append hprefix tailTrace_412200
  have hstable : (prefixWord ++ tailWord_412200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412200).length < 2 ^ (prefixWord ++ tailWord_412200).sum := by decide
  have hdescent : baseEnd_412200 < baseStart_412200 := by decide
  rcases family_descends (prefixWord ++ tailWord_412200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412203 : List Nat := [1, 1, 1, 1, 2, 1, 3, 6, 3, 2, 2]
def baseStart_412203 : Nat := 118140960795 + 412203 * 2 ^ 59
def prefixEnd_412203 : Nat := 4983230072969 + 3 ^ 40 * 412203 * 2
def baseEnd_412203 : Nat := 211658266225355987566819

theorem tailTrace_412203 : CollatzResearch.WordTrace tailWord_412203 prefixEnd_412203 211658266225355987566819 := by
  unfold tailWord_412203
  simp only [CollatzResearch.WordTrace]
  refine ⟨15034278525666404512785263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10022852350444269675190175 15034278525666404512785263)
  ·
    refine ⟨22551417788499606769177895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15034278525666404512785263 22551417788499606769177895)
    ·
      refine ⟨33827126682749410153766843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22551417788499606769177895 33827126682749410153766843)
      ·
        refine ⟨50740690024124115230650265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33827126682749410153766843 50740690024124115230650265)
        ·
          refine ⟨38055517518093086422987699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50740690024124115230650265 38055517518093086422987699)
          ·
            refine ⟨57083276277139629634481549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38055517518093086422987699 57083276277139629634481549)
            ·
              refine ⟨21406228603927361112930581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57083276277139629634481549 21406228603927361112930581)
              ·
                refine ⟨1003416965809095052168621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21406228603927361112930581 1003416965809095052168621)
                ·
                  refine ⟨376281362178410644563233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1003416965809095052168621 376281362178410644563233)
                  ·
                    refine ⟨282211021633807983422425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 376281362178410644563233 282211021633807983422425)
                    ·
                      refine ⟨211658266225355987566819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 282211021633807983422425 211658266225355987566819)
                      ·
                        rfl

theorem cell23_412203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 2, 2].length) (baseStart_412203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412203 prefixEnd_412203 := by exact prefixLift 412203
  have htrace : WordTrace (prefixWord ++ tailWord_412203) baseStart_412203 baseEnd_412203 := by
    simpa [prefixWord, tailWord_412203, baseEnd_412203] using wordTrace_append hprefix tailTrace_412203
  have hstable : (prefixWord ++ tailWord_412203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412203).length < 2 ^ (prefixWord ++ tailWord_412203).sum := by decide
  have hdescent : baseEnd_412203 < baseStart_412203 := by decide
  rcases family_descends (prefixWord ++ tailWord_412203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412209 : List Nat := [1, 2, 2, 3, 1, 1, 4, 9]
def baseStart_412209 : Nat := 118140960795 + 412209 * 2 ^ 59
def prefixEnd_412209 : Nat := 4983230072969 + 3 ^ 40 * 412209 * 2
def baseEnd_412209 : Nat := 7839309152195665336733

theorem tailTrace_412209 : CollatzResearch.WordTrace tailWord_412209 prefixEnd_412209 7839309152195665336733 := by
  unfold tailWord_412209
  simp only [CollatzResearch.WordTrace]
  refine ⟨15034497363644667537503681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10022998242429778358335787 15034497363644667537503681)
  ·
    refine ⟨11275873022733500653127761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15034497363644667537503681 11275873022733500653127761)
    ·
      refine ⟨8456904767050125489845821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11275873022733500653127761 8456904767050125489845821)
      ·
        refine ⟨3171339287643797058692183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8456904767050125489845821 3171339287643797058692183)
        ·
          refine ⟨4757008931465695588038275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3171339287643797058692183 4757008931465695588038275)
          ·
            refine ⟨7135513397198543382057413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4757008931465695588038275 7135513397198543382057413)
            ·
              refine ⟨1337908761974726884135765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7135513397198543382057413 1337908761974726884135765)
              ·
                refine ⟨7839309152195665336733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1337908761974726884135765 7839309152195665336733)
                ·
                  rfl

theorem cell23_412209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 9].length) (baseStart_412209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412209 prefixEnd_412209 := by exact prefixLift 412209
  have htrace : WordTrace (prefixWord ++ tailWord_412209) baseStart_412209 baseEnd_412209 := by
    simpa [prefixWord, tailWord_412209, baseEnd_412209] using wordTrace_append hprefix tailTrace_412209
  have hstable : (prefixWord ++ tailWord_412209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412209).length < 2 ^ (prefixWord ++ tailWord_412209).sum := by decide
  have hdescent : baseEnd_412209 < baseStart_412209 := by decide
  rcases family_descends (prefixWord ++ tailWord_412209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412216 : List Nat := [2, 1, 2, 1, 4, 1, 3, 2, 1, 2, 4]
def baseStart_412216 : Nat := 118140960795 + 412216 * 2 ^ 59
def prefixEnd_412216 : Nat := 4983230072969 + 3 ^ 40 * 412216 * 2
def baseEnd_412216 : Nat := 211664941473864436704259

theorem tailTrace_412216 : CollatzResearch.WordTrace tailWord_412216 prefixEnd_412216 211664941473864436704259 := by
  unfold tailWord_412216
  simp only [CollatzResearch.WordTrace]
  refine ⟨7517376337309653866504251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10023168449746205155339001 7517376337309653866504251)
  ·
    refine ⟨11276064505964480799756377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7517376337309653866504251 11276064505964480799756377)
    ·
      refine ⟨8457048379473360599817283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11276064505964480799756377 8457048379473360599817283)
      ·
        refine ⟨12685572569210040899725925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8457048379473360599817283 12685572569210040899725925)
        ·
          refine ⟨2378544856726882668698611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12685572569210040899725925 2378544856726882668698611)
          ·
            refine ⟨3567817285090324003047917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2378544856726882668698611 3567817285090324003047917)
            ·
              refine ⟨1337931481908871501142969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3567817285090324003047917 1337931481908871501142969)
              ·
                refine ⟨1003448611431653625857227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1337931481908871501142969 1003448611431653625857227)
                ·
                  refine ⟨1505172917147480438785841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1003448611431653625857227 1505172917147480438785841)
                  ·
                    refine ⟨1128879687860610329089381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1505172917147480438785841 1128879687860610329089381)
                    ·
                      refine ⟨211664941473864436704259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1128879687860610329089381 211664941473864436704259)
                      ·
                        rfl

theorem cell23_412216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_412216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412216 prefixEnd_412216 := by exact prefixLift 412216
  have htrace : WordTrace (prefixWord ++ tailWord_412216) baseStart_412216 baseEnd_412216 := by
    simpa [prefixWord, tailWord_412216, baseEnd_412216] using wordTrace_append hprefix tailTrace_412216
  have hstable : (prefixWord ++ tailWord_412216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412216).length < 2 ^ (prefixWord ++ tailWord_412216).sum := by decide
  have hdescent : baseEnd_412216 < baseStart_412216 := by decide
  rcases family_descends (prefixWord ++ tailWord_412216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412220 : List Nat := [2, 2, 2, 2, 3, 2, 3, 1, 1, 1, 4]
def baseStart_412220 : Nat := 118140960795 + 412220 * 2 ^ 59
def prefixEnd_412220 : Nat := 4983230072969 + 3 ^ 40 * 412220 * 2
def baseEnd_412220 : Nat := 211666995396482421054241

theorem tailTrace_412220 : CollatzResearch.WordTrace tailWord_412220 prefixEnd_412220 211666995396482421054241 := by
  unfold tailWord_412220
  simp only [CollatzResearch.WordTrace]
  refine ⟨7517449283302408208077057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10023265711069877610769409 7517449283302408208077057)
  ·
    refine ⟨5638086962476806156057793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7517449283302408208077057 5638086962476806156057793)
    ·
      refine ⟨4228565221857604617043345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5638086962476806156057793 4228565221857604617043345)
      ·
        refine ⟨3171423916393203462782509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4228565221857604617043345 3171423916393203462782509)
        ·
          refine ⟨1189283968647451298543441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3171423916393203462782509 1189283968647451298543441)
          ·
            refine ⟨891962976485588473907581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1189283968647451298543441 891962976485588473907581)
            ·
              refine ⟨334486116182095677715343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 891962976485588473907581 334486116182095677715343)
              ·
                refine ⟨501729174273143516573015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 334486116182095677715343 501729174273143516573015)
                ·
                  refine ⟨752593761409715274859523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 501729174273143516573015 752593761409715274859523)
                  ·
                    refine ⟨1128890642114572912289285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 752593761409715274859523 1128890642114572912289285)
                    ·
                      refine ⟨211666995396482421054241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1128890642114572912289285 211666995396482421054241)
                      ·
                        rfl

theorem cell23_412220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_412220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412220 prefixEnd_412220 := by exact prefixLift 412220
  have htrace : WordTrace (prefixWord ++ tailWord_412220) baseStart_412220 baseEnd_412220 := by
    simpa [prefixWord, tailWord_412220, baseEnd_412220] using wordTrace_append hprefix tailTrace_412220
  have hstable : (prefixWord ++ tailWord_412220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412220).length < 2 ^ (prefixWord ++ tailWord_412220).sum := by decide
  have hdescent : baseEnd_412220 < baseStart_412220 := by decide
  rcases family_descends (prefixWord ++ tailWord_412220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412236 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 3, 3, 3]
def baseStart_412236 : Nat := 118140960795 + 412236 * 2 ^ 59
def prefixEnd_412236 : Nat := 4983230072969 + 3 ^ 40 * 412236 * 2
def baseEnd_412236 : Nat := 211675211086954358454167

theorem tailTrace_412236 : CollatzResearch.WordTrace tailWord_412236 prefixEnd_412236 211675211086954358454167 := by
  unfold tailWord_412236
  simp only [CollatzResearch.WordTrace]
  refine ⟨7517741067273425574368281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10023654756364567432491041 7517741067273425574368281)
  ·
    refine ⟨5638305800455069180776211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7517741067273425574368281 5638305800455069180776211)
    ·
      refine ⟨8457458700682603771164317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5638305800455069180776211 8457458700682603771164317)
      ·
        refine ⟨3171547012755976414186619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8457458700682603771164317 3171547012755976414186619)
        ·
          refine ⟨4757320519133964621279929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3171547012755976414186619 4757320519133964621279929)
          ·
            refine ⟨3567990389350473465959947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4757320519133964621279929 3567990389350473465959947)
            ·
              refine ⟨5351985584025710198939921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3567990389350473465959947 5351985584025710198939921)
              ·
                refine ⟨4013989188019282649204941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5351985584025710198939921 4013989188019282649204941)
                ·
                  refine ⟨1505245945507230993451853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4013989188019282649204941 1505245945507230993451853)
                  ·
                    refine ⟨564467229565211622544445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1505245945507230993451853 564467229565211622544445)
                    ·
                      refine ⟨211675211086954358454167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 564467229565211622544445 211675211086954358454167)
                      ·
                        rfl

theorem cell23_412236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_412236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412236 prefixEnd_412236 := by exact prefixLift 412236
  have htrace : WordTrace (prefixWord ++ tailWord_412236) baseStart_412236 baseEnd_412236 := by
    simpa [prefixWord, tailWord_412236, baseEnd_412236] using wordTrace_append hprefix tailTrace_412236
  have hstable : (prefixWord ++ tailWord_412236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412236).length < 2 ^ (prefixWord ++ tailWord_412236).sum := by decide
  have hdescent : baseEnd_412236 < baseStart_412236 := by decide
  rcases family_descends (prefixWord ++ tailWord_412236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412239 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 2, 7]
def baseStart_412239 : Nat := 118140960795 + 412239 * 2 ^ 59
def prefixEnd_412239 : Nat := 4983230072969 + 3 ^ 40 * 412239 * 2
def baseEnd_412239 : Nat := 70558917176305948905551

theorem tailTrace_412239 : CollatzResearch.WordTrace tailWord_412239 prefixEnd_412239 70558917176305948905551 := by
  unfold tailWord_412239
  simp only [CollatzResearch.WordTrace]
  refine ⟨15035591553535982661095771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10023727702357321774063847 15035591553535982661095771)
  ·
    refine ⟨22553387330303973991643657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15035591553535982661095771 22553387330303973991643657)
    ·
      refine ⟨16915040497727980493732743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22553387330303973991643657 16915040497727980493732743)
      ·
        refine ⟨25372560746591970740599115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16915040497727980493732743 25372560746591970740599115)
        ·
          refine ⟨38058841119887956110898673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25372560746591970740599115 38058841119887956110898673)
          ·
            refine ⟨28544130839915967083174005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38058841119887956110898673 28544130839915967083174005)
            ·
              refine ⟨2676012266242121914047563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28544130839915967083174005 2676012266242121914047563)
              ·
                refine ⟨4014018399363182871071345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2676012266242121914047563 4014018399363182871071345)
                ·
                  refine ⟨3010513799522387153303509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4014018399363182871071345 3010513799522387153303509)
                  ·
                    refine ⟨70558917176305948905551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3010513799522387153303509 70558917176305948905551)
                    ·
                      rfl

theorem cell23_412239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 7].length) (baseStart_412239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412239 prefixEnd_412239 := by exact prefixLift 412239
  have htrace : WordTrace (prefixWord ++ tailWord_412239) baseStart_412239 baseEnd_412239 := by
    simpa [prefixWord, tailWord_412239, baseEnd_412239] using wordTrace_append hprefix tailTrace_412239
  have hstable : (prefixWord ++ tailWord_412239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412239).length < 2 ^ (prefixWord ++ tailWord_412239).sum := by decide
  have hdescent : baseEnd_412239 < baseStart_412239 := by decide
  rcases family_descends (prefixWord ++ tailWord_412239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412249 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 3, 4, 5]
def baseStart_412249 : Nat := 118140960795 + 412249 * 2 ^ 59
def prefixEnd_412249 : Nat := 4983230072969 + 3 ^ 40 * 412249 * 2
def baseEnd_412249 : Nat := 211681886335462807591607

theorem tailTrace_412249 : CollatzResearch.WordTrace tailWord_412249 prefixEnd_412249 211681886335462807591607 := by
  unfold tailWord_412249
  simp only [CollatzResearch.WordTrace]
  refine ⟨15035956283499754368959801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10023970855666502912639867 15035956283499754368959801)
  ·
    refine ⟨11276967212624815776719851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15035956283499754368959801 11276967212624815776719851)
    ·
      refine ⟨16915450818937223665079777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11276967212624815776719851 16915450818937223665079777)
      ·
        refine ⟨12686588114202917748809833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16915450818937223665079777 12686588114202917748809833)
        ·
          refine ⟨9514941085652188311607375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12686588114202917748809833 9514941085652188311607375)
          ·
            refine ⟨14272411628478282467411063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9514941085652188311607375 14272411628478282467411063)
            ·
              refine ⟨21408617442717423701116595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14272411628478282467411063 21408617442717423701116595)
              ·
                refine ⟨32112926164076135551674893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21408617442717423701116595 32112926164076135551674893)
                ·
                  refine ⟨12042347311528550831878085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32112926164076135551674893 12042347311528550831878085)
                  ·
                    refine ⟨2257940120911603280977141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12042347311528550831878085 2257940120911603280977141)
                    ·
                      refine ⟨211681886335462807591607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2257940120911603280977141 211681886335462807591607)
                      ·
                        rfl

theorem cell23_412249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_412249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412249 prefixEnd_412249 := by exact prefixLift 412249
  have htrace : WordTrace (prefixWord ++ tailWord_412249) baseStart_412249 baseEnd_412249 := by
    simpa [prefixWord, tailWord_412249, baseEnd_412249] using wordTrace_append hprefix tailTrace_412249
  have hstable : (prefixWord ++ tailWord_412249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412249).length < 2 ^ (prefixWord ++ tailWord_412249).sum := by decide
  have hdescent : baseEnd_412249 < baseStart_412249 := by decide
  rcases family_descends (prefixWord ++ tailWord_412249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412266 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_412266 : Nat := 118140960795 + 412266 * 2 ^ 59
def prefixEnd_412266 : Nat := 4983230072969 + 3 ^ 40 * 412266 * 2
def baseEnd_412266 : Nat := 211690615506589241079029

theorem tailTrace_412266 : CollatzResearch.WordTrace tailWord_412266 prefixEnd_412266 211690615506589241079029 := by
  unfold tailWord_412266
  simp only [CollatzResearch.WordTrace]
  refine ⟨3759144081109541568082163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10024384216292110848219101 3759144081109541568082163)
  ·
    refine ⟨5638716121664312352123245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3759144081109541568082163 5638716121664312352123245)
    ·
      refine ⟨2114518545624117132046217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5638716121664312352123245 2114518545624117132046217)
      ·
        refine ⟨1585888909218087849034663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2114518545624117132046217 1585888909218087849034663)
        ·
          refine ⟨2378833363827131773551995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1585888909218087849034663 2378833363827131773551995)
          ·
            refine ⟨3568250045740697660327993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2378833363827131773551995 3568250045740697660327993)
            ·
              refine ⟨2676187534305523245245995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3568250045740697660327993 2676187534305523245245995)
              ·
                refine ⟨4014281301458284867868993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2676187534305523245245995 4014281301458284867868993)
                ·
                  refine ⟨3010710976093713650901745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4014281301458284867868993 3010710976093713650901745)
                  ·
                    refine ⟨2258033232070285238176309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3010710976093713650901745 2258033232070285238176309)
                    ·
                      refine ⟨211690615506589241079029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2258033232070285238176309 211690615506589241079029)
                      ·
                        rfl

theorem cell23_412266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_412266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412266 prefixEnd_412266 := by exact prefixLift 412266
  have htrace : WordTrace (prefixWord ++ tailWord_412266) baseStart_412266 baseEnd_412266 := by
    simpa [prefixWord, tailWord_412266, baseEnd_412266] using wordTrace_append hprefix tailTrace_412266
  have hstable : (prefixWord ++ tailWord_412266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412266).length < 2 ^ (prefixWord ++ tailWord_412266).sum := by decide
  have hdescent : baseEnd_412266 < baseStart_412266 := by decide
  rcases family_descends (prefixWord ++ tailWord_412266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412274 : List Nat := [3, 2, 1, 2, 5, 1, 2, 1, 1, 2, 3]
def baseStart_412274 : Nat := 118140960795 + 412274 * 2 ^ 59
def prefixEnd_412274 : Nat := 4983230072969 + 3 ^ 40 * 412274 * 2
def baseEnd_412274 : Nat := 211694723351825209778993

theorem tailTrace_412274 : CollatzResearch.WordTrace tailWord_412274 prefixEnd_412274 211694723351825209778993 := by
  unfold tailWord_412274
  simp only [CollatzResearch.WordTrace]
  refine ⟨3759217027102295909654969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10024578738939455759079917 3759217027102295909654969)
  ·
    refine ⟨2819412770326721932241227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3759217027102295909654969 2819412770326721932241227)
    ·
      refine ⟨4229119155490082898361841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2819412770326721932241227 4229119155490082898361841)
      ·
        refine ⟨3171839366617562173771381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4229119155490082898361841 3171839366617562173771381)
        ·
          refine ⟨297359940620396453791067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3171839366617562173771381 297359940620396453791067)
          ·
            refine ⟨446039910930594680686601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297359940620396453791067 446039910930594680686601)
            ·
              refine ⟨334529933197946010514951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446039910930594680686601 334529933197946010514951)
              ·
                refine ⟨501794899796919015772427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 334529933197946010514951 501794899796919015772427)
                ·
                  refine ⟨752692349695378523658641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 501794899796919015772427 752692349695378523658641)
                  ·
                    refine ⟨564519262271533892743981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 752692349695378523658641 564519262271533892743981)
                    ·
                      refine ⟨211694723351825209778993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 564519262271533892743981 211694723351825209778993)
                      ·
                        rfl

theorem cell23_412274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_412274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412274 prefixEnd_412274 := by exact prefixLift 412274
  have htrace : WordTrace (prefixWord ++ tailWord_412274) baseStart_412274 baseEnd_412274 := by
    simpa [prefixWord, tailWord_412274, baseEnd_412274] using wordTrace_append hprefix tailTrace_412274
  have hstable : (prefixWord ++ tailWord_412274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412274).length < 2 ^ (prefixWord ++ tailWord_412274).sum := by decide
  have hdescent : baseEnd_412274 < baseStart_412274 := by decide
  rcases family_descends (prefixWord ++ tailWord_412274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412314 : List Nat := [3, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2]
def baseStart_412314 : Nat := 118140960795 + 412314 * 2 ^ 59
def prefixEnd_412314 : Nat := 4983230072969 + 3 ^ 40 * 412314 * 2
def baseEnd_412314 : Nat := 211715262578005053278809

theorem tailTrace_412314 : CollatzResearch.WordTrace tailWord_412314 prefixEnd_412314 211715262578005053278809 := by
  unfold tailWord_412314
  simp only [CollatzResearch.WordTrace]
  refine ⟨3759581757066067617518999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10025551352176180313383997 3759581757066067617518999)
  ·
    refine ⟨5639372635599101426278499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3759581757066067617518999 5639372635599101426278499)
    ·
      refine ⟨8459058953398652139417749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5639372635599101426278499 8459058953398652139417749)
      ·
        refine ⟨396518388440561819035207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8459058953398652139417749 396518388440561819035207)
        ·
          refine ⟨594777582660842728552811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396518388440561819035207 594777582660842728552811)
          ·
            refine ⟨892166373991264092829217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594777582660842728552811 892166373991264092829217)
            ·
              refine ⟨669124780493448069621913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892166373991264092829217 669124780493448069621913)
              ·
                refine ⟨501843585370086052216435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 669124780493448069621913 501843585370086052216435)
                ·
                  refine ⟨752765378055129078324653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 501843585370086052216435 752765378055129078324653)
                  ·
                    refine ⟨282287016770673404371745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 752765378055129078324653 282287016770673404371745)
                    ·
                      refine ⟨211715262578005053278809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 282287016770673404371745 211715262578005053278809)
                      ·
                        rfl

theorem cell23_412314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_412314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412314 prefixEnd_412314 := by exact prefixLift 412314
  have htrace : WordTrace (prefixWord ++ tailWord_412314) baseStart_412314 baseEnd_412314 := by
    simpa [prefixWord, tailWord_412314, baseEnd_412314] using wordTrace_append hprefix tailTrace_412314
  have hstable : (prefixWord ++ tailWord_412314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412314).length < 2 ^ (prefixWord ++ tailWord_412314).sum := by decide
  have hdescent : baseEnd_412314 < baseStart_412314 := by decide
  rcases family_descends (prefixWord ++ tailWord_412314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412380 : List Nat := [2, 2, 5, 1, 1, 1, 1, 3, 2, 5]
def baseStart_412380 : Nat := 118140960795 + 412380 * 2 ^ 59
def prefixEnd_412380 : Nat := 4983230072969 + 3 ^ 40 * 412380 * 2
def baseEnd_412380 : Nat := 70583050767067265017835

theorem tailTrace_412380 : CollatzResearch.WordTrace tailWord_412380 prefixEnd_412380 70583050767067265017835 := by
  unfold tailWord_412380
  simp only [CollatzResearch.WordTrace]
  refine ⟨7520367123012581870989297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10027156164016775827985729 7520367123012581870989297)
  ·
    refine ⟨5640275342259436403241973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7520367123012581870989297 5640275342259436403241973)
    ·
      refine ⟨528775813336822162803935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5640275342259436403241973 528775813336822162803935)
      ·
        refine ⟨793163720005233244205903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528775813336822162803935 793163720005233244205903)
        ·
          refine ⟨1189745580007849866308855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793163720005233244205903 1189745580007849866308855)
          ·
            refine ⟨1784618370011774799463283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189745580007849866308855 1784618370011774799463283)
            ·
              refine ⟨2676927555017662199194925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1784618370011774799463283 2676927555017662199194925)
              ·
                refine ⟨1003847833131623324698097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2676927555017662199194925 1003847833131623324698097)
                ·
                  refine ⟨752885874848717493523573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1003847833131623324698097 752885874848717493523573)
                  ·
                    refine ⟨70583050767067265017835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 752885874848717493523573 70583050767067265017835)
                    ·
                      rfl

theorem cell23_412380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_412380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412380 prefixEnd_412380 := by exact prefixLift 412380
  have htrace : WordTrace (prefixWord ++ tailWord_412380) baseStart_412380 baseEnd_412380 := by
    simpa [prefixWord, tailWord_412380, baseEnd_412380] using wordTrace_append hprefix tailTrace_412380
  have hstable : (prefixWord ++ tailWord_412380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412380).length < 2 ^ (prefixWord ++ tailWord_412380).sum := by decide
  have hdescent : baseEnd_412380 < baseStart_412380 := by decide
  rcases family_descends (prefixWord ++ tailWord_412380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412383 : List Nat := [1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 4]
def baseStart_412383 : Nat := 118140960795 + 412383 * 2 ^ 59
def prefixEnd_412383 : Nat := 4983230072969 + 3 ^ 40 * 412383 * 2
def baseEnd_412383 : Nat := 211750692743165283315991

theorem tailTrace_412383 : CollatzResearch.WordTrace tailWord_412383 prefixEnd_412383 211750692743165283315991 := by
  unfold tailWord_412383
  simp only [CollatzResearch.WordTrace]
  refine ⟨15040843665014295254337803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10027229110009530169558535 15040843665014295254337803)
  ·
    refine ⟨22561265497521442881506705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15040843665014295254337803 22561265497521442881506705)
    ·
      refine ⟨16920949123141082161130029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22561265497521442881506705 16920949123141082161130029)
      ·
        refine ⟨6345355921177905810423761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16920949123141082161130029 6345355921177905810423761)
        ·
          refine ⟨4759016940883429357817821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6345355921177905810423761 4759016940883429357817821)
          ·
            refine ⟨1784631352831286009181683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4759016940883429357817821 1784631352831286009181683)
            ·
              refine ⟨2676947029246929013772525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1784631352831286009181683 2676947029246929013772525)
              ·
                refine ⟨1003855135967598380164697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2676947029246929013772525 1003855135967598380164697)
                ·
                  refine ⟨752891351975698785123523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1003855135967598380164697 752891351975698785123523)
                  ·
                    refine ⟨1129337027963548177685285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 752891351975698785123523 1129337027963548177685285)
                    ·
                      refine ⟨211750692743165283315991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1129337027963548177685285 211750692743165283315991)
                      ·
                        rfl

theorem cell23_412383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_412383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412383 prefixEnd_412383 := by exact prefixLift 412383
  have htrace : WordTrace (prefixWord ++ tailWord_412383) baseStart_412383 baseEnd_412383 := by
    simpa [prefixWord, tailWord_412383, baseEnd_412383] using wordTrace_append hprefix tailTrace_412383
  have hstable : (prefixWord ++ tailWord_412383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412383).length < 2 ^ (prefixWord ++ tailWord_412383).sum := by decide
  have hdescent : baseEnd_412383 < baseStart_412383 := by decide
  rcases family_descends (prefixWord ++ tailWord_412383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412396 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 6]
def baseStart_412396 : Nat := 118140960795 + 412396 * 2 ^ 59
def prefixEnd_412396 : Nat := 4983230072969 + 3 ^ 40 * 412396 * 2
def baseEnd_412396 : Nat := 211757367991673732453431

theorem tailTrace_412396 : CollatzResearch.WordTrace tailWord_412396 prefixEnd_412396 211757367991673732453431 := by
  unfold tailWord_412396
  simp only [CollatzResearch.WordTrace]
  refine ⟨7520658906983599237280521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10027545209311465649707361 7520658906983599237280521)
  ·
    refine ⟨5640494180237699427960391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7520658906983599237280521 5640494180237699427960391)
    ·
      refine ⟨8460741270356549141940587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5640494180237699427960391 8460741270356549141940587)
      ·
        refine ⟨12691111905534823712910881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8460741270356549141940587 12691111905534823712910881)
        ·
          refine ⟨9518333929151117784683161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12691111905534823712910881 9518333929151117784683161)
          ·
            refine ⟨7138750446863338338512371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9518333929151117784683161 7138750446863338338512371)
            ·
              refine ⟨10708125670295007507768557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7138750446863338338512371 10708125670295007507768557)
              ·
                refine ⟨4015547126360627815413209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10708125670295007507768557 4015547126360627815413209)
                ·
                  refine ⟨3011660344770470861559907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4015547126360627815413209 3011660344770470861559907)
                  ·
                    refine ⟨4517490517155706292339861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3011660344770470861559907 4517490517155706292339861)
                    ·
                      refine ⟨211757367991673732453431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4517490517155706292339861 211757367991673732453431)
                      ·
                        rfl

theorem cell23_412396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_412396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412396 prefixEnd_412396 := by exact prefixLift 412396
  have htrace : WordTrace (prefixWord ++ tailWord_412396) baseStart_412396 baseEnd_412396 := by
    simpa [prefixWord, tailWord_412396, baseEnd_412396] using wordTrace_append hprefix tailTrace_412396
  have hstable : (prefixWord ++ tailWord_412396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412396).length < 2 ^ (prefixWord ++ tailWord_412396).sum := by decide
  have hdescent : baseEnd_412396 < baseStart_412396 := by decide
  rcases family_descends (prefixWord ++ tailWord_412396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412434 : List Nat := [3, 2, 4, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_412434 : Nat := 118140960795 + 412434 * 2 ^ 59
def prefixEnd_412434 : Nat := 4983230072969 + 3 ^ 40 * 412434 * 2
def baseEnd_412434 : Nat := 211776880256544583778257

theorem tailTrace_412434 : CollatzResearch.WordTrace tailWord_412434 prefixEnd_412434 211776880256544583778257 := by
  unfold tailWord_412434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3760675946957382741111089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10028469191886353976296237 3760675946957382741111089)
  ·
    refine ⟨2820506960218037055833317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3760675946957382741111089 2820506960218037055833317)
    ·
      refine ⟨528845055040881947968747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2820506960218037055833317 528845055040881947968747)
      ·
        refine ⟨793267582561322921953121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528845055040881947968747 793267582561322921953121)
        ·
          refine ⟨594950686920992191464841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 793267582561322921953121 594950686920992191464841)
          ·
            refine ⟨446213015190744143598631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 594950686920992191464841 446213015190744143598631)
            ·
              refine ⟨669319522786116215397947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446213015190744143598631 669319522786116215397947)
              ·
                refine ⟨1003979284179174323096921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669319522786116215397947 1003979284179174323096921)
                ·
                  refine ⟨752984463134380742322691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1003979284179174323096921 752984463134380742322691)
                  ·
                    refine ⟨1129476694701571113484037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 752984463134380742322691 1129476694701571113484037)
                    ·
                      refine ⟨211776880256544583778257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1129476694701571113484037 211776880256544583778257)
                      ·
                        rfl

theorem cell23_412434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_412434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412434 prefixEnd_412434 := by exact prefixLift 412434
  have htrace : WordTrace (prefixWord ++ tailWord_412434) baseStart_412434 baseEnd_412434 := by
    simpa [prefixWord, tailWord_412434, baseEnd_412434] using wordTrace_append hprefix tailTrace_412434
  have hstable : (prefixWord ++ tailWord_412434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412434).length < 2 ^ (prefixWord ++ tailWord_412434).sum := by decide
  have hdescent : baseEnd_412434 < baseStart_412434 := by decide
  rcases family_descends (prefixWord ++ tailWord_412434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412460 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 4, 3, 2]
def baseStart_412460 : Nat := 118140960795 + 412460 * 2 ^ 59
def prefixEnd_412460 : Nat := 4983230072969 + 3 ^ 40 * 412460 * 2
def baseEnd_412460 : Nat := 211790230753561482053137

theorem tailTrace_412460 : CollatzResearch.WordTrace tailWord_412460 prefixEnd_412460 211790230753561482053137 := by
  unfold tailWord_412460
  simp only [CollatzResearch.WordTrace]
  refine ⟨7521826042867668702445417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10029101390490224936593889 7521826042867668702445417)
  ·
    refine ⟨5641369532150751526834063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7521826042867668702445417 5641369532150751526834063)
    ·
      refine ⟨8462054298226127290251095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5641369532150751526834063 8462054298226127290251095)
      ·
        refine ⟨12693081447339190935376643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8462054298226127290251095 12693081447339190935376643)
        ·
          refine ⟨19039622171008786403064965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12693081447339190935376643 19039622171008786403064965)
          ·
            refine ⟨3569929157064147450574681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19039622171008786403064965 3569929157064147450574681)
            ·
              refine ⟨2677446867798110587931011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3569929157064147450574681 2677446867798110587931011)
              ·
                refine ⟨4016170301697165881896517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2677446867798110587931011 4016170301697165881896517)
                ·
                  refine ⟨753031931568218602855597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4016170301697165881896517 753031931568218602855597)
                  ·
                    refine ⟨282386974338081976070849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 753031931568218602855597 282386974338081976070849)
                    ·
                      refine ⟨211790230753561482053137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 282386974338081976070849 211790230753561482053137)
                      ·
                        rfl

theorem cell23_412460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 3, 2].length) (baseStart_412460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412460 prefixEnd_412460 := by exact prefixLift 412460
  have htrace : WordTrace (prefixWord ++ tailWord_412460) baseStart_412460 baseEnd_412460 := by
    simpa [prefixWord, tailWord_412460, baseEnd_412460] using wordTrace_append hprefix tailTrace_412460
  have hstable : (prefixWord ++ tailWord_412460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412460).length < 2 ^ (prefixWord ++ tailWord_412460).sum := by decide
  have hdescent : baseEnd_412460 < baseStart_412460 := by decide
  rcases family_descends (prefixWord ++ tailWord_412460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412467 : List Nat := [1, 1, 1, 2, 6, 2, 2, 1, 3, 1, 3]
def baseStart_412467 : Nat := 118140960795 + 412467 * 2 ^ 59
def prefixEnd_412467 : Nat := 4983230072969 + 3 ^ 40 * 412467 * 2
def baseEnd_412467 : Nat := 211793825118142954665605

theorem tailTrace_412467 : CollatzResearch.WordTrace tailWord_412467 prefixEnd_412467 211793825118142954665605 := by
  unfold tailWord_412467
  simp only [CollatzResearch.WordTrace]
  refine ⟨15043907396709977600395655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10029271597806651733597103 15043907396709977600395655)
  ·
    refine ⟨22565861095064966400593483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15043907396709977600395655 22565861095064966400593483)
    ·
      refine ⟨33848791642597449600890225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22565861095064966400593483 33848791642597449600890225)
      ·
        refine ⟨25386593731948087200667669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33848791642597449600890225 25386593731948087200667669)
        ·
          refine ⟨1189996581185066587531297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25386593731948087200667669 1189996581185066587531297)
          ·
            refine ⟨892497435888799940648473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1189996581185066587531297 892497435888799940648473)
            ·
              refine ⟨669373076916599955486355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892497435888799940648473 669373076916599955486355)
              ·
                refine ⟨1004059615374899933229533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669373076916599955486355 1004059615374899933229533)
                ·
                  refine ⟨376522355765587474961075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1004059615374899933229533 376522355765587474961075)
                  ·
                    refine ⟨564783533648381212441613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 376522355765587474961075 564783533648381212441613)
                    ·
                      refine ⟨211793825118142954665605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 564783533648381212441613 211793825118142954665605)
                      ·
                        rfl

theorem cell23_412467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 1, 3].length) (baseStart_412467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412467 prefixEnd_412467 := by exact prefixLift 412467
  have htrace : WordTrace (prefixWord ++ tailWord_412467) baseStart_412467 baseEnd_412467 := by
    simpa [prefixWord, tailWord_412467, baseEnd_412467] using wordTrace_append hprefix tailTrace_412467
  have hstable : (prefixWord ++ tailWord_412467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412467).length < 2 ^ (prefixWord ++ tailWord_412467).sum := by decide
  have hdescent : baseEnd_412467 < baseStart_412467 := by decide
  rcases family_descends (prefixWord ++ tailWord_412467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412534 : List Nat := [5, 1, 1, 3, 1, 2, 1, 3, 2, 4]
def baseStart_412534 : Nat := 118140960795 + 412534 * 2 ^ 59
def prefixEnd_412534 : Nat := 4983230072969 + 3 ^ 40 * 412534 * 2
def baseEnd_412534 : Nat := 70609409440664730842599

theorem tailTrace_412534 : CollatzResearch.WordTrace tailWord_412534 prefixEnd_412534 70609409440664730842599 := by
  unfold tailWord_412534
  simp only [CollatzResearch.WordTrace]
  refine ⟨940396942966703002692791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10030900724978165362056437 940396942966703002692791)
  ·
    refine ⟨1410595414450054504039187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 940396942966703002692791 1410595414450054504039187)
    ·
      refine ⟨2115893121675081756058781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1410595414450054504039187 2115893121675081756058781)
      ·
        refine ⟨793459920628155658522043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2115893121675081756058781 793459920628155658522043)
        ·
          refine ⟨1190189880942233487783065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793459920628155658522043 1190189880942233487783065)
          ·
            refine ⟨892642410706675115837299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1190189880942233487783065 892642410706675115837299)
            ·
              refine ⟨1338963616060012673755949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892642410706675115837299 1338963616060012673755949)
              ·
                refine ⟨502111356022504752658481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1338963616060012673755949 502111356022504752658481)
                ·
                  refine ⟨376583517016878564493861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 502111356022504752658481 376583517016878564493861)
                  ·
                    refine ⟨70609409440664730842599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 376583517016878564493861 70609409440664730842599)
                    ·
                      rfl

theorem cell23_412534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_412534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412534 prefixEnd_412534 := by exact prefixLift 412534
  have htrace : WordTrace (prefixWord ++ tailWord_412534) baseStart_412534 baseEnd_412534 := by
    simpa [prefixWord, tailWord_412534, baseEnd_412534] using wordTrace_append hprefix tailTrace_412534
  have hstable : (prefixWord ++ tailWord_412534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412534).length < 2 ^ (prefixWord ++ tailWord_412534).sum := by decide
  have hdescent : baseEnd_412534 < baseStart_412534 := by decide
  rcases family_descends (prefixWord ++ tailWord_412534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412637 : List Nat := [1, 4, 3, 1, 2, 2, 2, 1, 7]
def baseStart_412637 : Nat := 118140960795 + 412637 * 2 ^ 59
def prefixEnd_412637 : Nat := 4983230072969 + 3 ^ 40 * 412637 * 2
def baseEnd_412637 : Nat := 23542346314378587726647

theorem tailTrace_412637 : CollatzResearch.WordTrace tailWord_412637 prefixEnd_412637 23542346314378587726647 := by
  unfold tailWord_412637
  simp only [CollatzResearch.WordTrace]
  refine ⟨15050107806094096634084165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10033405204062731089389443 15050107806094096634084165)
  ·
    refine ⟨2821895213642643118890781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15050107806094096634084165 2821895213642643118890781)
    ·
      refine ⟨1058210705115991169584043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2821895213642643118890781 1058210705115991169584043)
      ·
        refine ⟨1587316057673986754376065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1058210705115991169584043 1587316057673986754376065)
        ·
          refine ⟨1190487043255490065782049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1587316057673986754376065 1190487043255490065782049)
          ·
            refine ⟨892865282441617549336537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1190487043255490065782049 892865282441617549336537)
            ·
              refine ⟨669648961831213162002403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892865282441617549336537 669648961831213162002403)
              ·
                refine ⟨1004473442746819743003605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669648961831213162002403 1004473442746819743003605)
                ·
                  refine ⟨23542346314378587726647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1004473442746819743003605 23542346314378587726647)
                  ·
                    rfl

theorem cell23_412637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_412637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412637 prefixEnd_412637 := by exact prefixLift 412637
  have htrace : WordTrace (prefixWord ++ tailWord_412637) baseStart_412637 baseEnd_412637 := by
    simpa [prefixWord, tailWord_412637, baseEnd_412637] using wordTrace_append hprefix tailTrace_412637
  have hstable : (prefixWord ++ tailWord_412637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412637).length < 2 ^ (prefixWord ++ tailWord_412637).sum := by decide
  have hdescent : baseEnd_412637 < baseStart_412637 := by decide
  rcases family_descends (prefixWord ++ tailWord_412637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412647 : List Nat := [1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 3]
def baseStart_412647 : Nat := 118140960795 + 412647 * 2 ^ 59
def prefixEnd_412647 : Nat := 4983230072969 + 3 ^ 40 * 412647 * 2
def baseEnd_412647 : Nat := 211886251635952250414777

theorem tailTrace_412647 : CollatzResearch.WordTrace tailWord_412647 prefixEnd_412647 211886251635952250414777 := by
  unfold tailWord_412647
  simp only [CollatzResearch.WordTrace]
  refine ⟨15050472536057868341948195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10033648357371912227965463 15050472536057868341948195)
  ·
    refine ⟨22575708804086802512922293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15050472536057868341948195 22575708804086802512922293)
    ·
      refine ⟨2116472700383137735586465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22575708804086802512922293 2116472700383137735586465)
      ·
        refine ⟨1587354525287353301689849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2116472700383137735586465 1587354525287353301689849)
        ·
          refine ⟨1190515893965514976267387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1587354525287353301689849 1190515893965514976267387)
          ·
            refine ⟨1785773840948272464401081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190515893965514976267387 1785773840948272464401081)
            ·
              refine ⟨1339330380711204348300811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1785773840948272464401081 1339330380711204348300811)
              ·
                refine ⟨2008995571066806522451217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339330380711204348300811 2008995571066806522451217)
                ·
                  refine ⟨1506746678300104891838413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2008995571066806522451217 1506746678300104891838413)
                  ·
                    refine ⟨565030004362539334439405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1506746678300104891838413 565030004362539334439405)
                    ·
                      refine ⟨211886251635952250414777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 565030004362539334439405 211886251635952250414777)
                      ·
                        rfl

theorem cell23_412647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_412647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412647 prefixEnd_412647 := by exact prefixLift 412647
  have htrace : WordTrace (prefixWord ++ tailWord_412647) baseStart_412647 baseEnd_412647 := by
    simpa [prefixWord, tailWord_412647, baseEnd_412647] using wordTrace_append hprefix tailTrace_412647
  have hstable : (prefixWord ++ tailWord_412647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412647).length < 2 ^ (prefixWord ++ tailWord_412647).sum := by decide
  have hdescent : baseEnd_412647 < baseStart_412647 := by decide
  rcases family_descends (prefixWord ++ tailWord_412647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412650 : List Nat := [3, 1, 3, 1, 2, 2, 1, 2, 1, 7]
def baseStart_412650 : Nat := 118140960795 + 412650 * 2 ^ 59
def prefixEnd_412650 : Nat := 4983230072969 + 3 ^ 40 * 412650 * 2
def baseEnd_412650 : Nat := 70629264025971912892421

theorem tailTrace_412650 : CollatzResearch.WordTrace tailWord_412650 prefixEnd_412650 70629264025971912892421 := by
  unfold tailWord_412650
  simp only [CollatzResearch.WordTrace]
  refine ⟨3762645488761749963576851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10033721303364666569538269 3762645488761749963576851)
  ·
    refine ⟨5643968233142624945365277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3762645488761749963576851 5643968233142624945365277)
    ·
      refine ⟨2116488087428484354511979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5643968233142624945365277 2116488087428484354511979)
      ·
        refine ⟨3174732131142726531767969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2116488087428484354511979 3174732131142726531767969)
        ·
          refine ⟨2381049098357044898825977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3174732131142726531767969 2381049098357044898825977)
          ·
            refine ⟨1785786823767783674119483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2381049098357044898825977 1785786823767783674119483)
            ·
              refine ⟨2678680235651675511179225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1785786823767783674119483 2678680235651675511179225)
              ·
                refine ⟨2009010176738756633384419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2678680235651675511179225 2009010176738756633384419)
                ·
                  refine ⟨3013515265108134950076629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009010176738756633384419 3013515265108134950076629)
                  ·
                    refine ⟨70629264025971912892421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3013515265108134950076629 70629264025971912892421)
                    ·
                      rfl

theorem cell23_412650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_412650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412650 prefixEnd_412650 := by exact prefixLift 412650
  have htrace : WordTrace (prefixWord ++ tailWord_412650) baseStart_412650 baseEnd_412650 := by
    simpa [prefixWord, tailWord_412650, baseEnd_412650] using wordTrace_append hprefix tailTrace_412650
  have hstable : (prefixWord ++ tailWord_412650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412650).length < 2 ^ (prefixWord ++ tailWord_412650).sum := by decide
  have hdescent : baseEnd_412650 < baseStart_412650 := by decide
  rcases family_descends (prefixWord ++ tailWord_412650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412697 : List Nat := [1, 2, 1, 2, 1, 1, 7, 1, 3, 4]
def baseStart_412697 : Nat := 118140960795 + 412697 * 2 ^ 59
def prefixEnd_412697 : Nat := 4983230072969 + 3 ^ 40 * 412697 * 2
def baseEnd_412697 : Nat := 70637308556225684929849

theorem tailTrace_412697 : CollatzResearch.WordTrace tailWord_412697 prefixEnd_412697 70637308556225684929849 := by
  unfold tailWord_412697
  simp only [CollatzResearch.WordTrace]
  refine ⟨15052296185876726881268345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10034864123917817920845563 15052296185876726881268345)
  ·
    refine ⟨11289222139407545160951259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15052296185876726881268345 11289222139407545160951259)
    ·
      refine ⟨16933833209111317741426889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11289222139407545160951259 16933833209111317741426889)
      ·
        refine ⟨12700374906833488306070167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16933833209111317741426889 12700374906833488306070167)
        ·
          refine ⟨19050562360250232459105251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12700374906833488306070167 19050562360250232459105251)
          ·
            refine ⟨28575843540375348688657877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19050562360250232459105251 28575843540375348688657877)
            ·
              refine ⟨669746332977547234890419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 28575843540375348688657877 669746332977547234890419)
              ·
                refine ⟨1004619499466320852335629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669746332977547234890419 1004619499466320852335629)
                ·
                  refine ⟨376732312299870319625861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1004619499466320852335629 376732312299870319625861)
                  ·
                    refine ⟨70637308556225684929849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 376732312299870319625861 70637308556225684929849)
                    ·
                      rfl

theorem cell23_412697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 4].length) (baseStart_412697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412697 prefixEnd_412697 := by exact prefixLift 412697
  have htrace : WordTrace (prefixWord ++ tailWord_412697) baseStart_412697 baseEnd_412697 := by
    simpa [prefixWord, tailWord_412697, baseEnd_412697] using wordTrace_append hprefix tailTrace_412697
  have hstable : (prefixWord ++ tailWord_412697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412697).length < 2 ^ (prefixWord ++ tailWord_412697).sum := by decide
  have hdescent : baseEnd_412697 < baseStart_412697 := by decide
  rcases family_descends (prefixWord ++ tailWord_412697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412764 : List Nat := [2, 2, 4, 1, 1, 1, 2, 2, 1, 5, 2]
def baseStart_412764 : Nat := 118140960795 + 412764 * 2 ^ 59
def prefixEnd_412764 : Nat := 4983230072969 + 3 ^ 40 * 412764 * 2
def baseEnd_412764 : Nat := 211946328872528292651739

theorem tailTrace_412764 : CollatzResearch.WordTrace tailWord_412764 prefixEnd_412764 211946328872528292651739 := by
  unfold tailWord_412764
  simp only [CollatzResearch.WordTrace]
  refine ⟨7527369938316998661978673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10036493251089331549304897 7527369938316998661978673)
  ·
    refine ⟨5645527453737748996484005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7527369938316998661978673 5645527453737748996484005)
    ·
      refine ⟨1058536397575827936840751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5645527453737748996484005 1058536397575827936840751)
      ·
        refine ⟨1587804596363741905261127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1058536397575827936840751 1587804596363741905261127)
        ·
          refine ⟨2381706894545612857891691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1587804596363741905261127 2381706894545612857891691)
          ·
            refine ⟨3572560341818419286837537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2381706894545612857891691 3572560341818419286837537)
            ·
              refine ⟨2679420256363814465128153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3572560341818419286837537 2679420256363814465128153)
              ·
                refine ⟨2009565192272860848846115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2679420256363814465128153 2009565192272860848846115)
                ·
                  refine ⟨3014347788409291273269173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009565192272860848846115 3014347788409291273269173)
                  ·
                    refine ⟨282595105163371056868985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3014347788409291273269173 282595105163371056868985)
                    ·
                      refine ⟨211946328872528292651739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 282595105163371056868985 211946328872528292651739)
                      ·
                        rfl

theorem cell23_412764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_412764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412764 prefixEnd_412764 := by exact prefixLift 412764
  have htrace : WordTrace (prefixWord ++ tailWord_412764) baseStart_412764 baseEnd_412764 := by
    simpa [prefixWord, tailWord_412764, baseEnd_412764] using wordTrace_append hprefix tailTrace_412764
  have hstable : (prefixWord ++ tailWord_412764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412764).length < 2 ^ (prefixWord ++ tailWord_412764).sum := by decide
  have hdescent : baseEnd_412764 < baseStart_412764 := by decide
  rcases family_descends (prefixWord ++ tailWord_412764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412777 : List Nat := [1, 2, 1, 1, 1, 6, 2, 1, 3, 1, 4]
def baseStart_412777 : Nat := 118140960795 + 412777 * 2 ^ 59
def prefixEnd_412777 : Nat := 4983230072969 + 3 ^ 40 * 412777 * 2
def baseEnd_412777 : Nat := 211953004121036741789179

theorem tailTrace_412777 : CollatzResearch.WordTrace tailWord_412777 prefixEnd_412777 211953004121036741789179 := by
  unfold tailWord_412777
  simp only [CollatzResearch.WordTrace]
  refine ⟨15055214025586900544180585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10036809350391267029453723 15055214025586900544180585)
  ·
    refine ⟨11291410519190175408135439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15055214025586900544180585 11291410519190175408135439)
    ·
      refine ⟨16937115778785263112203159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11291410519190175408135439 16937115778785263112203159)
      ·
        refine ⟨25405673668177894668304739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16937115778785263112203159 25405673668177894668304739)
        ·
          refine ⟨38108510502266842002457109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25405673668177894668304739 38108510502266842002457109)
          ·
            refine ⟨1786336429793758218865177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38108510502266842002457109 1786336429793758218865177)
            ·
              refine ⟨1339752322345318664148883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1786336429793758218865177 1339752322345318664148883)
              ·
                refine ⟨2009628483517977996223325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339752322345318664148883 2009628483517977996223325)
                ·
                  refine ⟨753610681319241748583747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2009628483517977996223325 753610681319241748583747)
                  ·
                    refine ⟨1130416021978862622875621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 753610681319241748583747 1130416021978862622875621)
                    ·
                      refine ⟨211953004121036741789179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1130416021978862622875621 211953004121036741789179)
                      ·
                        rfl

theorem cell23_412777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 1, 4].length) (baseStart_412777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412777 prefixEnd_412777 := by exact prefixLift 412777
  have htrace : WordTrace (prefixWord ++ tailWord_412777) baseStart_412777 baseEnd_412777 := by
    simpa [prefixWord, tailWord_412777, baseEnd_412777] using wordTrace_append hprefix tailTrace_412777
  have hstable : (prefixWord ++ tailWord_412777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412777).length < 2 ^ (prefixWord ++ tailWord_412777).sum := by decide
  have hdescent : baseEnd_412777 < baseStart_412777 := by decide
  rcases family_descends (prefixWord ++ tailWord_412777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412781 : List Nat := [1, 5, 1, 1, 2, 2, 3, 1, 2, 3, 2]
def baseStart_412781 : Nat := 118140960795 + 412781 * 2 ^ 59
def prefixEnd_412781 : Nat := 4983230072969 + 3 ^ 40 * 412781 * 2
def baseEnd_412781 : Nat := 211955058043654726139161

theorem tailTrace_412781 : CollatzResearch.WordTrace tailWord_412781 prefixEnd_412781 211955058043654726139161 := by
  unfold tailWord_412781
  simp only [CollatzResearch.WordTrace]
  refine ⟨15055359917572409227326197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10036906611714939484884131 15055359917572409227326197)
  ·
    refine ⟨1411439992272413365061831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15055359917572409227326197 1411439992272413365061831)
    ·
      refine ⟨2117159988408620047592747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1411439992272413365061831 2117159988408620047592747)
      ·
        refine ⟨3175739982612930071389121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2117159988408620047592747 3175739982612930071389121)
        ·
          refine ⟨2381804986959697553541841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3175739982612930071389121 2381804986959697553541841)
          ·
            refine ⟨1786353740219773165156381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2381804986959697553541841 1786353740219773165156381)
            ·
              refine ⟨669882652582414936933643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1786353740219773165156381 669882652582414936933643)
              ·
                refine ⟨1004823978873622405400465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669882652582414936933643 1004823978873622405400465)
                ·
                  refine ⟨753617984155216804050349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1004823978873622405400465 753617984155216804050349)
                  ·
                    refine ⟨282606744058206301518881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 753617984155216804050349 282606744058206301518881)
                    ·
                      refine ⟨211955058043654726139161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 282606744058206301518881 211955058043654726139161)
                      ·
                        rfl

theorem cell23_412781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_412781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412781 prefixEnd_412781 := by exact prefixLift 412781
  have htrace : WordTrace (prefixWord ++ tailWord_412781) baseStart_412781 baseEnd_412781 := by
    simpa [prefixWord, tailWord_412781, baseEnd_412781] using wordTrace_append hprefix tailTrace_412781
  have hstable : (prefixWord ++ tailWord_412781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412781).length < 2 ^ (prefixWord ++ tailWord_412781).sum := by decide
  have hdescent : baseEnd_412781 < baseStart_412781 := by decide
  rcases family_descends (prefixWord ++ tailWord_412781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412797 : List Nat := [1, 4, 1, 1, 3, 1, 2, 3, 1, 1, 5]
def baseStart_412797 : Nat := 118140960795 + 412797 * 2 ^ 59
def prefixEnd_412797 : Nat := 4983230072969 + 3 ^ 40 * 412797 * 2
def baseEnd_412797 : Nat := 211963273734126663539087

theorem tailTrace_412797 : CollatzResearch.WordTrace tailWord_412797 prefixEnd_412797 211963273734126663539087 := by
  unfold tailWord_412797
  simp only [CollatzResearch.WordTrace]
  refine ⟨15055943485514443959908645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10037295657009629306605763 15055943485514443959908645)
  ·
    refine ⟨2822989403533958242482871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15055943485514443959908645 2822989403533958242482871)
    ·
      refine ⟨4234484105300937363724307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2822989403533958242482871 4234484105300937363724307)
      ·
        refine ⟨6351726157951406045586461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4234484105300937363724307 6351726157951406045586461)
        ·
          refine ⟨2381897309231777267094923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6351726157951406045586461 2381897309231777267094923)
          ·
            refine ⟨3572845963847665900642385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2381897309231777267094923 3572845963847665900642385)
            ·
              refine ⟨2679634472885749425481789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3572845963847665900642385 2679634472885749425481789)
              ·
                refine ⟨1004862927332156034555671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2679634472885749425481789 1004862927332156034555671)
                ·
                  refine ⟨1507294390998234051833507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1004862927332156034555671 1507294390998234051833507)
                  ·
                    refine ⟨2260941586497351077750261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1507294390998234051833507 2260941586497351077750261)
                    ·
                      refine ⟨211963273734126663539087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2260941586497351077750261 211963273734126663539087)
                      ·
                        rfl

theorem cell23_412797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_412797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412797 prefixEnd_412797 := by exact prefixLift 412797
  have htrace : WordTrace (prefixWord ++ tailWord_412797) baseStart_412797 baseEnd_412797 := by
    simpa [prefixWord, tailWord_412797, baseEnd_412797] using wordTrace_append hprefix tailTrace_412797
  have hstable : (prefixWord ++ tailWord_412797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412797).length < 2 ^ (prefixWord ++ tailWord_412797).sum := by decide
  have hdescent : baseEnd_412797 < baseStart_412797 := by decide
  rcases family_descends (prefixWord ++ tailWord_412797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412804 : List Nat := [2, 3, 2, 1, 2, 3, 1, 1, 4, 4]
def baseStart_412804 : Nat := 118140960795 + 412804 * 2 ^ 59
def prefixEnd_412804 : Nat := 4983230072969 + 3 ^ 40 * 412804 * 2
def baseEnd_412804 : Nat := 70655622699569378717185

theorem tailTrace_412804 : CollatzResearch.WordTrace tailWord_412804 prefixEnd_412804 70655622699569378717185 := by
  unfold tailWord_412804
  simp only [CollatzResearch.WordTrace]
  refine ⟨7528099398244542077706733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10037465864326056103608977 7528099398244542077706733)
  ·
    refine ⟨2823037274341703279140025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7528099398244542077706733 2823037274341703279140025)
    ·
      refine ⟨2117277955756277459355019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2823037274341703279140025 2117277955756277459355019)
      ·
        refine ⟨3175916933634416189032529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2117277955756277459355019 3175916933634416189032529)
        ·
          refine ⟨2381937700225812141774397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3175916933634416189032529 2381937700225812141774397)
          ·
            refine ⟨893226637584679553165399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2381937700225812141774397 893226637584679553165399)
            ·
              refine ⟨1339839956377019329748099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893226637584679553165399 1339839956377019329748099)
              ·
                refine ⟨2009759934565528994622149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339839956377019329748099 2009759934565528994622149)
                ·
                  refine ⟨376829987731036686491653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2009759934565528994622149 376829987731036686491653)
                  ·
                    refine ⟨70655622699569378717185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 376829987731036686491653 70655622699569378717185)
                    ·
                      rfl

theorem cell23_412804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_412804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412804 prefixEnd_412804 := by exact prefixLift 412804
  have htrace : WordTrace (prefixWord ++ tailWord_412804) baseStart_412804 baseEnd_412804 := by
    simpa [prefixWord, tailWord_412804, baseEnd_412804] using wordTrace_append hprefix tailTrace_412804
  have hstable : (prefixWord ++ tailWord_412804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412804).length < 2 ^ (prefixWord ++ tailWord_412804).sum := by decide
  have hdescent : baseEnd_412804 < baseStart_412804 := by decide
  rcases family_descends (prefixWord ++ tailWord_412804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412814 : List Nat := [4, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5]
def baseStart_412814 : Nat := 118140960795 + 412814 * 2 ^ 59
def prefixEnd_412814 : Nat := 4983230072969 + 3 ^ 40 * 412814 * 2
def baseEnd_412814 : Nat := 211972002905253097026509

theorem tailTrace_412814 : CollatzResearch.WordTrace tailWord_412814 prefixEnd_412814 211972002905253097026509 := by
  unfold tailWord_412814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1882070440806606982909687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10037709017635237242184997 1882070440806606982909687)
  ·
    refine ⟨2823105661209910474364531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1882070440806606982909687 2823105661209910474364531)
    ·
      refine ⟨4234658491814865711546797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2823105661209910474364531 4234658491814865711546797)
      ·
        refine ⟨1587996934430574641830049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4234658491814865711546797 1587996934430574641830049)
        ·
          refine ⟨1190997700822930981372537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1587996934430574641830049 1190997700822930981372537)
          ·
            refine ⟨893248275617198236029403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1190997700822930981372537 893248275617198236029403)
            ·
              refine ⟨1339872413425797354044105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893248275617198236029403 1339872413425797354044105)
              ·
                refine ⟨1004904310069348015533079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1339872413425797354044105 1004904310069348015533079)
                ·
                  refine ⟨1507356465104022023299619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1004904310069348015533079 1507356465104022023299619)
                  ·
                    refine ⟨2261034697656033034949429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1507356465104022023299619 2261034697656033034949429)
                    ·
                      refine ⟨211972002905253097026509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2261034697656033034949429 211972002905253097026509)
                      ·
                        rfl

theorem cell23_412814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_412814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412814 prefixEnd_412814 := by exact prefixLift 412814
  have htrace : WordTrace (prefixWord ++ tailWord_412814) baseStart_412814 baseEnd_412814 := by
    simpa [prefixWord, tailWord_412814, baseEnd_412814] using wordTrace_append hprefix tailTrace_412814
  have hstable : (prefixWord ++ tailWord_412814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412814).length < 2 ^ (prefixWord ++ tailWord_412814).sum := by decide
  have hdescent : baseEnd_412814 < baseStart_412814 := by decide
  rcases family_descends (prefixWord ++ tailWord_412814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412824 : List Nat := [2, 1, 2, 4, 2, 1, 3, 1, 1, 2, 4]
def baseStart_412824 : Nat := 118140960795 + 412824 * 2 ^ 59
def prefixEnd_412824 : Nat := 4983230072969 + 3 ^ 40 * 412824 * 2
def baseEnd_412824 : Nat := 211977137711798057901463

theorem tailTrace_412824 : CollatzResearch.WordTrace tailWord_412824 prefixEnd_412824 211977137711798057901463 := by
  unfold tailWord_412824
  simp only [CollatzResearch.WordTrace]
  refine ⟨7528464128208313785570763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10037952170944418380761017 7528464128208313785570763)
  ·
    refine ⟨11292696192312470678356145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7528464128208313785570763 11292696192312470678356145)
    ·
      refine ⟨8469522144234353008767109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11292696192312470678356145 8469522144234353008767109)
      ·
        refine ⟨1588035402043941189143833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8469522144234353008767109 1588035402043941189143833)
        ·
          refine ⟨1191026551532955891857875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1588035402043941189143833 1191026551532955891857875)
          ·
            refine ⟨1786539827299433837786813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1191026551532955891857875 1786539827299433837786813)
            ·
              refine ⟨669952435237287689170055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1786539827299433837786813 669952435237287689170055)
              ·
                refine ⟨1004928652855931533755083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669952435237287689170055 1004928652855931533755083)
                ·
                  refine ⟨1507392979283897300632625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1004928652855931533755083 1507392979283897300632625)
                  ·
                    refine ⟨1130544734462922975474469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1507392979283897300632625 1130544734462922975474469)
                    ·
                      refine ⟨211977137711798057901463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1130544734462922975474469 211977137711798057901463)
                      ·
                        rfl

theorem cell23_412824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_412824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412824 prefixEnd_412824 := by exact prefixLift 412824
  have htrace : WordTrace (prefixWord ++ tailWord_412824) baseStart_412824 baseEnd_412824 := by
    simpa [prefixWord, tailWord_412824, baseEnd_412824] using wordTrace_append hprefix tailTrace_412824
  have hstable : (prefixWord ++ tailWord_412824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412824).length < 2 ^ (prefixWord ++ tailWord_412824).sum := by decide
  have hdescent : baseEnd_412824 < baseStart_412824 := by decide
  rcases family_descends (prefixWord ++ tailWord_412824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412834 : List Nat := [3, 3, 1, 3, 2, 1, 1, 9]
def baseStart_412834 : Nat := 118140960795 + 412834 * 2 ^ 59
def prefixEnd_412834 : Nat := 4983230072969 + 3 ^ 40 * 412834 * 2
def baseEnd_412834 : Nat := 7851195278457148843571

theorem tailTrace_412834 : CollatzResearch.WordTrace tailWord_412834 prefixEnd_412834 7851195278457148843571 := by
  unfold tailWord_412834
  simp only [CollatzResearch.WordTrace]
  refine ⟨3764323246595099819751389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10038195324253599519337037 3764323246595099819751389)
  ·
    refine ⟨1411621217473162432406771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3764323246595099819751389 1411621217473162432406771)
    ·
      refine ⟨2117431826209743648610157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1411621217473162432406771 2117431826209743648610157)
      ·
        refine ⟨794036934828653868228809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2117431826209743648610157 794036934828653868228809)
        ·
          refine ⟨595527701121490401171607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 794036934828653868228809 595527701121490401171607)
          ·
            refine ⟨893291551682235601757411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595527701121490401171607 893291551682235601757411)
            ·
              refine ⟨1339937327523353402636117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893291551682235601757411 1339937327523353402636117)
              ·
                refine ⟨7851195278457148843571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1339937327523353402636117 7851195278457148843571)
                ·
                  rfl

theorem cell23_412834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 9].length) (baseStart_412834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412834 prefixEnd_412834 := by exact prefixLift 412834
  have htrace : WordTrace (prefixWord ++ tailWord_412834) baseStart_412834 baseEnd_412834 := by
    simpa [prefixWord, tailWord_412834, baseEnd_412834] using wordTrace_append hprefix tailTrace_412834
  have hstable : (prefixWord ++ tailWord_412834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412834).length < 2 ^ (prefixWord ++ tailWord_412834).sum := by decide
  have hdescent : baseEnd_412834 < baseStart_412834 := by decide
  rcases family_descends (prefixWord ++ tailWord_412834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412862 : List Nat := [4, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2]
def baseStart_412862 : Nat := 118140960795 + 412862 * 2 ^ 59
def prefixEnd_412862 : Nat := 4983230072969 + 3 ^ 40 * 412862 * 2
def baseEnd_412862 : Nat := 211996649976668909226289

theorem tailTrace_412862 : CollatzResearch.WordTrace tailWord_412862 prefixEnd_412862 211996649976668909226289 := by
  unfold tailWord_412862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1882289278784870007628105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10038876153519306707349893 1882289278784870007628105)
  ·
    refine ⟨1411716959088652505721079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1882289278784870007628105 1411716959088652505721079)
    ·
      refine ⟨2117575438632978758581619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1411716959088652505721079 2117575438632978758581619)
      ·
        refine ⟨3176363157949468137872429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2117575438632978758581619 3176363157949468137872429)
        ·
          refine ⟨1191136184231050551702161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3176363157949468137872429 1191136184231050551702161)
          ·
            refine ⟨893352138173287913776621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1191136184231050551702161 893352138173287913776621)
            ·
              refine ⟨335007051814982967666233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 893352138173287913776621 335007051814982967666233)
              ·
                refine ⟨251255288861237225749675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335007051814982967666233 251255288861237225749675)
                ·
                  refine ⟨376882933291855838624513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251255288861237225749675 376882933291855838624513)
                  ·
                    refine ⟨282662199968891878968385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 376882933291855838624513 282662199968891878968385)
                    ·
                      refine ⟨211996649976668909226289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 282662199968891878968385 211996649976668909226289)
                      ·
                        rfl

theorem cell23_412862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_412862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412862 prefixEnd_412862 := by exact prefixLift 412862
  have htrace : WordTrace (prefixWord ++ tailWord_412862) baseStart_412862 baseEnd_412862 := by
    simpa [prefixWord, tailWord_412862, baseEnd_412862] using wordTrace_append hprefix tailTrace_412862
  have hstable : (prefixWord ++ tailWord_412862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412862).length < 2 ^ (prefixWord ++ tailWord_412862).sum := by decide
  have hdescent : baseEnd_412862 < baseStart_412862 := by decide
  rcases family_descends (prefixWord ++ tailWord_412862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412878 : List Nat := [4, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3]
def baseStart_412878 : Nat := 118140960795 + 412878 * 2 ^ 59
def prefixEnd_412878 : Nat := 4983230072969 + 3 ^ 40 * 412878 * 2
def baseEnd_412878 : Nat := 212004865667140846626215

theorem tailTrace_412878 : CollatzResearch.WordTrace tailWord_412878 prefixEnd_412878 212004865667140846626215 := by
  unfold tailWord_412878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1882362224777624349200911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10039265198813996529071525 1882362224777624349200911)
  ·
    refine ⟨2823543337166436523801367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1882362224777624349200911 2823543337166436523801367)
    ·
      refine ⟨4235315005749654785702051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2823543337166436523801367 4235315005749654785702051)
      ·
        refine ⟨6352972508624482178553077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4235315005749654785702051 6352972508624482178553077)
        ·
          refine ⟨595591172683545204239351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6352972508624482178553077 595591172683545204239351)
          ·
            refine ⟨893386759025317806359027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595591172683545204239351 893386759025317806359027)
            ·
              refine ⟨1340080138537976709538541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893386759025317806359027 1340080138537976709538541)
              ·
                refine ⟨502530051951741266076953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1340080138537976709538541 502530051951741266076953)
                ·
                  refine ⟨376897538963805949557715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 502530051951741266076953 376897538963805949557715)
                  ·
                    refine ⟨565346308445708924336573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 376897538963805949557715 565346308445708924336573)
                    ·
                      refine ⟨212004865667140846626215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 565346308445708924336573 212004865667140846626215)
                      ·
                        rfl

theorem cell23_412878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_412878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412878 prefixEnd_412878 := by exact prefixLift 412878
  have htrace : WordTrace (prefixWord ++ tailWord_412878) baseStart_412878 baseEnd_412878 := by
    simpa [prefixWord, tailWord_412878, baseEnd_412878] using wordTrace_append hprefix tailTrace_412878
  have hstable : (prefixWord ++ tailWord_412878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412878).length < 2 ^ (prefixWord ++ tailWord_412878).sum := by decide
  have hdescent : baseEnd_412878 < baseStart_412878 := by decide
  rcases family_descends (prefixWord ++ tailWord_412878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412887 : List Nat := [1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 5]
def baseStart_412887 : Nat := 118140960795 + 412887 * 2 ^ 59
def prefixEnd_412887 : Nat := 4983230072969 + 3 ^ 40 * 412887 * 2
def baseEnd_412887 : Nat := 212009486993031311413673

theorem tailTrace_412887 : CollatzResearch.WordTrace tailWord_412887 prefixEnd_412887 212009486993031311413673 := by
  unfold tailWord_412887
  simp only [CollatzResearch.WordTrace]
  refine ⟨15059226055188389330684915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10039484036792259553789943 15059226055188389330684915)
  ·
    refine ⟨22588839082782583996027373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15059226055188389330684915 22588839082782583996027373)
    ·
      refine ⟨8470814656043468998510265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22588839082782583996027373 8470814656043468998510265)
      ·
        refine ⟨6353110992032601748882699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8470814656043468998510265 6353110992032601748882699)
        ·
          refine ⟨9529666488048902623324049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6353110992032601748882699 9529666488048902623324049)
          ·
            refine ⟨7147249866036676967493037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9529666488048902623324049 7147249866036676967493037)
            ·
              refine ⟨2680218699763753862809889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7147249866036676967493037 2680218699763753862809889)
              ·
                refine ⟨2010164024822815397107417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2680218699763753862809889 2010164024822815397107417)
                ·
                  refine ⟨1507623018617111547830563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2010164024822815397107417 1507623018617111547830563)
                  ·
                    refine ⟨2261434527925667321745845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1507623018617111547830563 2261434527925667321745845)
                    ·
                      refine ⟨212009486993031311413673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2261434527925667321745845 212009486993031311413673)
                      ·
                        rfl

theorem cell23_412887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_412887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412887 prefixEnd_412887 := by exact prefixLift 412887
  have htrace : WordTrace (prefixWord ++ tailWord_412887) baseStart_412887 baseEnd_412887 := by
    simpa [prefixWord, tailWord_412887, baseEnd_412887] using wordTrace_append hprefix tailTrace_412887
  have hstable : (prefixWord ++ tailWord_412887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412887).length < 2 ^ (prefixWord ++ tailWord_412887).sum := by decide
  have hdescent : baseEnd_412887 < baseStart_412887 := by decide
  rcases family_descends (prefixWord ++ tailWord_412887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412937 : List Nat := [1, 2, 1, 1, 3, 3, 2, 2, 1, 7]
def baseStart_412937 : Nat := 118140960795 + 412937 * 2 ^ 59
def prefixEnd_412937 : Nat := 4983230072969 + 3 ^ 40 * 412937 * 2
def baseEnd_412937 : Nat := 70678387008585371929481

theorem tailTrace_412937 : CollatzResearch.WordTrace tailWord_412937 prefixEnd_412937 70678387008585371929481 := by
  unfold tailWord_412937
  simp only [CollatzResearch.WordTrace]
  refine ⟨15061049705007247870005065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10040699803338165246670043 15061049705007247870005065)
  ·
    refine ⟨11295787278755435902503799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15061049705007247870005065 11295787278755435902503799)
    ·
      refine ⟨16943680918133153853755699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11295787278755435902503799 16943680918133153853755699)
      ·
        refine ⟨25415521377199730780633549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16943680918133153853755699 25415521377199730780633549)
        ·
          refine ⟨9530820516449899042737581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25415521377199730780633549 9530820516449899042737581)
          ·
            refine ⟨3574057693668712141026593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9530820516449899042737581 3574057693668712141026593)
            ·
              refine ⟨2680543270251534105769945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3574057693668712141026593 2680543270251534105769945)
              ·
                refine ⟨2010407452688650579327459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2680543270251534105769945 2010407452688650579327459)
                ·
                  refine ⟨3015611179032975868991189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2010407452688650579327459 3015611179032975868991189)
                  ·
                    refine ⟨70678387008585371929481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3015611179032975868991189 70678387008585371929481)
                    ·
                      rfl

theorem cell23_412937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 7].length) (baseStart_412937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412937 prefixEnd_412937 := by exact prefixLift 412937
  have htrace : WordTrace (prefixWord ++ tailWord_412937) baseStart_412937 baseEnd_412937 := by
    simpa [prefixWord, tailWord_412937, baseEnd_412937] using wordTrace_append hprefix tailTrace_412937
  have hstable : (prefixWord ++ tailWord_412937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412937).length < 2 ^ (prefixWord ++ tailWord_412937).sum := by decide
  have hdescent : baseEnd_412937 < baseStart_412937 := by decide
  rcases family_descends (prefixWord ++ tailWord_412937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412954 : List Nat := [3, 1, 1, 3, 3, 2, 1, 1, 1, 7]
def baseStart_412954 : Nat := 118140960795 + 412954 * 2 ^ 59
def prefixEnd_412954 : Nat := 4983230072969 + 3 ^ 40 * 412954 * 2
def baseEnd_412954 : Nat := 70681296732294183091955

theorem tailTrace_412954 : CollatzResearch.WordTrace tailWord_412954 prefixEnd_412954 70681296732294183091955 := by
  unfold tailWord_412954
  simp only [CollatzResearch.WordTrace]
  refine ⟨3765417436486414943343479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10041113163963773182249277 3765417436486414943343479)
  ·
    refine ⟨5648126154729622415015219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3765417436486414943343479 5648126154729622415015219)
    ·
      refine ⟨8472189232094433622522829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5648126154729622415015219 8472189232094433622522829)
      ·
        refine ⟨3177070962035412608446061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8472189232094433622522829 3177070962035412608446061)
        ·
          refine ⟨1191401610763279728167273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3177070962035412608446061 1191401610763279728167273)
          ·
            refine ⟨893551208072459796125455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1191401610763279728167273 893551208072459796125455)
            ·
              refine ⟨1340326812108689694188183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893551208072459796125455 1340326812108689694188183)
              ·
                refine ⟨2010490218163034541282275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1340326812108689694188183 2010490218163034541282275)
                ·
                  refine ⟨3015735327244551811923413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2010490218163034541282275 3015735327244551811923413)
                  ·
                    refine ⟨70681296732294183091955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3015735327244551811923413 70681296732294183091955)
                    ·
                      rfl

theorem cell23_412954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 1, 7].length) (baseStart_412954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412954 prefixEnd_412954 := by exact prefixLift 412954
  have htrace : WordTrace (prefixWord ++ tailWord_412954) baseStart_412954 baseEnd_412954 := by
    simpa [prefixWord, tailWord_412954, baseEnd_412954] using wordTrace_append hprefix tailTrace_412954
  have hstable : (prefixWord ++ tailWord_412954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412954).length < 2 ^ (prefixWord ++ tailWord_412954).sum := by decide
  have hdescent : baseEnd_412954 < baseStart_412954 := by decide
  rcases family_descends (prefixWord ++ tailWord_412954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412991 : List Nat := [1, 1, 2, 2, 4, 2, 2, 1, 2, 4, 2]
def baseStart_412991 : Nat := 118140960795 + 412991 * 2 ^ 59
def prefixEnd_412991 : Nat := 4983230072969 + 3 ^ 40 * 412991 * 2
def baseEnd_412991 : Nat := 212062888981098904513195

theorem tailTrace_412991 : CollatzResearch.WordTrace tailWord_412991 prefixEnd_412991 212062888981098904513195 := by
  unfold tailWord_412991
  simp only [CollatzResearch.WordTrace]
  refine ⟨15063019246811615092470827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10042012831207743394980551 15063019246811615092470827)
  ·
    refine ⟨22594528870217422638706241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15063019246811615092470827 22594528870217422638706241)
    ·
      refine ⟨16945896652663066979029681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22594528870217422638706241 16945896652663066979029681)
      ·
        refine ⟨12709422489497300234272261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16945896652663066979029681 12709422489497300234272261)
        ·
          refine ⟨2383016716780743793926049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12709422489497300234272261 2383016716780743793926049)
          ·
            refine ⟨1787262537585557845444537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2383016716780743793926049 1787262537585557845444537)
            ·
              refine ⟨1340446903189168384083403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1787262537585557845444537 1340446903189168384083403)
              ·
                refine ⟨2010670354783752576125105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1340446903189168384083403 2010670354783752576125105)
                ·
                  refine ⟨1508002766087814432093829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2010670354783752576125105 1508002766087814432093829)
                  ·
                    refine ⟨282750518641465206017593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1508002766087814432093829 282750518641465206017593)
                    ·
                      refine ⟨212062888981098904513195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 282750518641465206017593 212062888981098904513195)
                      ·
                        rfl

theorem cell23_412991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 4, 2].length) (baseStart_412991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_412991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_412991 prefixEnd_412991 := by exact prefixLift 412991
  have htrace : WordTrace (prefixWord ++ tailWord_412991) baseStart_412991 baseEnd_412991 := by
    simpa [prefixWord, tailWord_412991, baseEnd_412991] using wordTrace_append hprefix tailTrace_412991
  have hstable : (prefixWord ++ tailWord_412991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412991).length < 2 ^ (prefixWord ++ tailWord_412991).sum := by decide
  have hdescent : baseEnd_412991 < baseStart_412991 := by decide
  rcases family_descends (prefixWord ++ tailWord_412991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413018 : List Nat := [3, 1, 1, 2, 1, 2, 5, 3, 1, 4]
def baseStart_413018 : Nat := 118140960795 + 413018 * 2 ^ 59
def prefixEnd_413018 : Nat := 4983230072969 + 3 ^ 40 * 413018 * 2
def baseEnd_413018 : Nat := 70692250986256766291857

theorem tailTrace_413018 : CollatzResearch.WordTrace tailWord_413018 prefixEnd_413018 70692250986256766291857 := by
  unfold tailWord_413018
  simp only [CollatzResearch.WordTrace]
  refine ⟨3766001004428449675925927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10042669345142532469135805 3766001004428449675925927)
  ·
    refine ⟨5649001506642674513888891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3766001004428449675925927 5649001506642674513888891)
    ·
      refine ⟨8473502259964011770833337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5649001506642674513888891 8473502259964011770833337)
      ·
        refine ⟨6355126694973008828125003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8473502259964011770833337 6355126694973008828125003)
        ·
          refine ⟨9532690042459513242187505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6355126694973008828125003 9532690042459513242187505)
          ·
            refine ⟨7149517531844634931640629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9532690042459513242187505 7149517531844634931640629)
            ·
              refine ⟨670267268610434524841309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7149517531844634931640629 670267268610434524841309)
              ·
                refine ⟨251350225728912946815491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 670267268610434524841309 251350225728912946815491)
                ·
                  refine ⟨377025338593369420223237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251350225728912946815491 377025338593369420223237)
                  ·
                    refine ⟨70692250986256766291857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 377025338593369420223237 70692250986256766291857)
                    ·
                      rfl

theorem cell23_413018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 1, 4].length) (baseStart_413018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413018 prefixEnd_413018 := by exact prefixLift 413018
  have htrace : WordTrace (prefixWord ++ tailWord_413018) baseStart_413018 baseEnd_413018 := by
    simpa [prefixWord, tailWord_413018, baseEnd_413018] using wordTrace_append hprefix tailTrace_413018
  have hstable : (prefixWord ++ tailWord_413018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413018).length < 2 ^ (prefixWord ++ tailWord_413018).sum := by decide
  have hdescent : baseEnd_413018 < baseStart_413018 := by decide
  rcases family_descends (prefixWord ++ tailWord_413018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413051 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 4, 3, 2]
def baseStart_413051 : Nat := 118140960795 + 413051 * 2 ^ 59
def prefixEnd_413051 : Nat := 4983230072969 + 3 ^ 40 * 413051 * 2
def baseEnd_413051 : Nat := 212093697820368669762919

theorem tailTrace_413051 : CollatzResearch.WordTrace tailWord_413051 prefixEnd_413051 212093697820368669762919 := by
  unfold tailWord_413051
  simp only [CollatzResearch.WordTrace]
  refine ⟨15065207626594245339655007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10043471751062830226436671 15065207626594245339655007)
  ·
    refine ⟨22597811439891368009482511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15065207626594245339655007 22597811439891368009482511)
    ·
      refine ⟨33896717159837052014223767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22597811439891368009482511 33896717159837052014223767)
      ·
        refine ⟨50845075739755578021335651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33896717159837052014223767 50845075739755578021335651)
        ·
          refine ⟨76267613609633367032003477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50845075739755578021335651 76267613609633367032003477)
          ·
            refine ⟨3575044387951564079625163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 76267613609633367032003477 3575044387951564079625163)
            ·
              refine ⟨5362566581927346119437745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3575044387951564079625163 5362566581927346119437745)
              ·
                refine ⟨4021924936445509589578309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5362566581927346119437745 4021924936445509589578309)
                ·
                  refine ⟨754110925583533048045933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4021924936445509589578309 754110925583533048045933)
                  ·
                    refine ⟨282791597093824893017225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 754110925583533048045933 282791597093824893017225)
                    ·
                      refine ⟨212093697820368669762919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 282791597093824893017225 212093697820368669762919)
                      ·
                        rfl

theorem cell23_413051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 3, 2].length) (baseStart_413051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413051 prefixEnd_413051 := by exact prefixLift 413051
  have htrace : WordTrace (prefixWord ++ tailWord_413051) baseStart_413051 baseEnd_413051 := by
    simpa [prefixWord, tailWord_413051, baseEnd_413051] using wordTrace_append hprefix tailTrace_413051
  have hstable : (prefixWord ++ tailWord_413051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413051).length < 2 ^ (prefixWord ++ tailWord_413051).sum := by decide
  have hdescent : baseEnd_413051 < baseStart_413051 := by decide
  rcases family_descends (prefixWord ++ tailWord_413051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413061 : List Nat := [1, 3, 1, 1, 3, 1, 5, 2, 1, 5]
def baseStart_413061 : Nat := 118140960795 + 413061 * 2 ^ 59
def prefixEnd_413061 : Nat := 4983230072969 + 3 ^ 40 * 413061 * 2
def baseEnd_413061 : Nat := 70699610875637876879291

theorem tailTrace_413061 : CollatzResearch.WordTrace tailWord_413061 prefixEnd_413061 70699610875637876879291 := by
  unfold tailWord_413061
  simp only [CollatzResearch.WordTrace]
  refine ⟨15065572356558017047519037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10043714904372011365012691 15065572356558017047519037)
  ·
    refine ⟨5649589633709256392819639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15065572356558017047519037 5649589633709256392819639)
    ·
      refine ⟨8474384450563884589229459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5649589633709256392819639 8474384450563884589229459)
      ·
        refine ⟨12711576675845826883844189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8474384450563884589229459 12711576675845826883844189)
        ·
          refine ⟨4766841253442185081441571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12711576675845826883844189 4766841253442185081441571)
          ·
            refine ⟨7150261880163277622162357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4766841253442185081441571 7150261880163277622162357)
            ·
              refine ⟨670337051265307277077721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7150261880163277622162357 670337051265307277077721)
              ·
                refine ⟨502752788448980457808291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 670337051265307277077721 502752788448980457808291)
                ·
                  refine ⟨754129182673470686712437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 502752788448980457808291 754129182673470686712437)
                  ·
                    refine ⟨70699610875637876879291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 754129182673470686712437 70699610875637876879291)
                    ·
                      rfl

theorem cell23_413061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 5].length) (baseStart_413061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413061 prefixEnd_413061 := by exact prefixLift 413061
  have htrace : WordTrace (prefixWord ++ tailWord_413061) baseStart_413061 baseEnd_413061 := by
    simpa [prefixWord, tailWord_413061, baseEnd_413061] using wordTrace_append hprefix tailTrace_413061
  have hstable : (prefixWord ++ tailWord_413061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413061).length < 2 ^ (prefixWord ++ tailWord_413061).sum := by decide
  have hdescent : baseEnd_413061 < baseStart_413061 := by decide
  rcases family_descends (prefixWord ++ tailWord_413061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413068 : List Nat := [2, 2, 1, 2, 1, 3, 4, 1, 2, 3, 2]
def baseStart_413068 : Nat := 118140960795 + 413068 * 2 ^ 59
def prefixEnd_413068 : Nat := 4983230072969 + 3 ^ 40 * 413068 * 2
def baseEnd_413068 : Nat := 212102426991495103250341

theorem tailTrace_413068 : CollatzResearch.WordTrace tailWord_413068 prefixEnd_413068 212102426991495103250341 := by
  unfold tailWord_413068
  simp only [CollatzResearch.WordTrace]
  refine ⟨7532913833766328621511929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10043885111688438162015905 7532913833766328621511929)
  ·
    refine ⟨5649685375324746466133947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7532913833766328621511929 5649685375324746466133947)
    ·
      refine ⟨8474528062987119699200921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5649685375324746466133947 8474528062987119699200921)
      ·
        refine ⟨6355896047240339774400691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8474528062987119699200921 6355896047240339774400691)
        ·
          refine ⟨9533844070860509661601037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6355896047240339774400691 9533844070860509661601037)
          ·
            refine ⟨3575191526572691123100389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9533844070860509661601037 3575191526572691123100389)
            ·
              refine ⟨670348411232379585581323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3575191526572691123100389 670348411232379585581323)
              ·
                refine ⟨1005522616848569378371985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 670348411232379585581323 1005522616848569378371985)
                ·
                  refine ⟨754141962636427033778989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1005522616848569378371985 754141962636427033778989)
                  ·
                    refine ⟨282803235988660137667121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 754141962636427033778989 282803235988660137667121)
                    ·
                      refine ⟨212102426991495103250341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 282803235988660137667121 212102426991495103250341)
                      ·
                        rfl

theorem cell23_413068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 2, 3, 2].length) (baseStart_413068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413068 prefixEnd_413068 := by exact prefixLift 413068
  have htrace : WordTrace (prefixWord ++ tailWord_413068) baseStart_413068 baseEnd_413068 := by
    simpa [prefixWord, tailWord_413068, baseEnd_413068] using wordTrace_append hprefix tailTrace_413068
  have hstable : (prefixWord ++ tailWord_413068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413068).length < 2 ^ (prefixWord ++ tailWord_413068).sum := by decide
  have hdescent : baseEnd_413068 < baseStart_413068 := by decide
  rcases family_descends (prefixWord ++ tailWord_413068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413086 : List Nat := [4, 3, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_413086 : Nat := 118140960795 + 413086 * 2 ^ 59
def prefixEnd_413086 : Nat := 4983230072969 + 3 ^ 40 * 413086 * 2
def baseEnd_413086 : Nat := 70703889881092010941753

theorem tailTrace_413086 : CollatzResearch.WordTrace tailWord_413086 prefixEnd_413086 70703889881092010941753 := by
  unfold tailWord_413086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1883310522683430789647389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10044322787644964211452741 1883310522683430789647389)
  ·
    refine ⟨706241446006286546117771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1883310522683430789647389 706241446006286546117771)
    ·
      refine ⟨1059362169009429819176657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 706241446006286546117771 1059362169009429819176657)
      ·
        refine ⟨794521626757072364382493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1059362169009429819176657 794521626757072364382493)
        ·
          refine ⟨297945610033902136643435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 794521626757072364382493 297945610033902136643435)
          ·
            refine ⟨446918415050853204965153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297945610033902136643435 446918415050853204965153)
            ·
              refine ⟨335188811288139903723865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446918415050853204965153 335188811288139903723865)
              ·
                refine ⟨251391608466104927792899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335188811288139903723865 251391608466104927792899)
                ·
                  refine ⟨377087412699157391689349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251391608466104927792899 377087412699157391689349)
                  ·
                    refine ⟨70703889881092010941753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 377087412699157391689349 70703889881092010941753)
                    ·
                      rfl

theorem cell23_413086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_413086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413086 prefixEnd_413086 := by exact prefixLift 413086
  have htrace : WordTrace (prefixWord ++ tailWord_413086) baseStart_413086 baseEnd_413086 := by
    simpa [prefixWord, tailWord_413086, baseEnd_413086] using wordTrace_append hprefix tailTrace_413086
  have hstable : (prefixWord ++ tailWord_413086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413086).length < 2 ^ (prefixWord ++ tailWord_413086).sum := by decide
  have hdescent : baseEnd_413086 < baseStart_413086 := by decide
  rcases family_descends (prefixWord ++ tailWord_413086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413111 : List Nat := [1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 4]
def baseStart_413111 : Nat := 118140960795 + 413111 * 2 ^ 59
def prefixEnd_413111 : Nat := 4983230072969 + 3 ^ 40 * 413111 * 2
def baseEnd_413111 : Nat := 212124506659638435012643

theorem tailTrace_413111 : CollatzResearch.WordTrace tailWord_413111 prefixEnd_413111 212124506659638435012643 := by
  unfold tailWord_413111
  simp only [CollatzResearch.WordTrace]
  refine ⟨15067396006376875586839187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10044930670917917057892791 15067396006376875586839187)
  ·
    refine ⟨22601094009565313380258781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15067396006376875586839187 22601094009565313380258781)
    ·
      refine ⟨8475410253586992517597043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22601094009565313380258781 8475410253586992517597043)
      ·
        refine ⟨12713115380380488776395565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8475410253586992517597043 12713115380380488776395565)
        ·
          refine ⟨4767418267642683291148337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12713115380380488776395565 4767418267642683291148337)
          ·
            refine ⟨3575563700732012468361253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4767418267642683291148337 3575563700732012468361253)
            ·
              refine ⟨670418193887252337817735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3575563700732012468361253 670418193887252337817735)
              ·
                refine ⟨1005627290830878506726603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 670418193887252337817735 1005627290830878506726603)
                ·
                  refine ⟨1508440936246317760089905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1005627290830878506726603 1508440936246317760089905)
                  ·
                    refine ⟨1131330702184738320067429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1508440936246317760089905 1131330702184738320067429)
                    ·
                      refine ⟨212124506659638435012643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1131330702184738320067429 212124506659638435012643)
                      ·
                        rfl

theorem cell23_413111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 4].length) (baseStart_413111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413111 prefixEnd_413111 := by exact prefixLift 413111
  have htrace : WordTrace (prefixWord ++ tailWord_413111) baseStart_413111 baseEnd_413111 := by
    simpa [prefixWord, tailWord_413111, baseEnd_413111] using wordTrace_append hprefix tailTrace_413111
  have hstable : (prefixWord ++ tailWord_413111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413111).length < 2 ^ (prefixWord ++ tailWord_413111).sum := by decide
  have hdescent : baseEnd_413111 < baseStart_413111 := by decide
  rcases family_descends (prefixWord ++ tailWord_413111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413118 : List Nat := [4, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3]
def baseStart_413118 : Nat := 118140960795 + 413118 * 2 ^ 59
def prefixEnd_413118 : Nat := 4983230072969 + 3 ^ 40 * 413118 * 2
def baseEnd_413118 : Nat := 212128101024219907625111

theorem tailTrace_413118 : CollatzResearch.WordTrace tailWord_413118 prefixEnd_413118 212128101024219907625111 := by
  unfold tailWord_413118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1883456414668939472793001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10045100878234343854896005 1883456414668939472793001)
  ·
    refine ⟨1412592311001704604594751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1883456414668939472793001 1412592311001704604594751)
    ·
      refine ⟨2118888466502556906892127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1412592311001704604594751 2118888466502556906892127)
      ·
        refine ⟨3178332699753835360338191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2118888466502556906892127 3178332699753835360338191)
        ·
          refine ⟨4767499049630753040507287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3178332699753835360338191 4767499049630753040507287)
          ·
            refine ⟨7151248574446129560760931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4767499049630753040507287 7151248574446129560760931)
            ·
              refine ⟨10726872861669194341141397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7151248574446129560760931 10726872861669194341141397)
              ·
                refine ⟨502822165390743484741003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10726872861669194341141397 502822165390743484741003)
                ·
                  refine ⟨754233248086115227111505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 502822165390743484741003 754233248086115227111505)
                  ·
                    refine ⟨565674936064586420333629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 754233248086115227111505 565674936064586420333629)
                    ·
                      refine ⟨212128101024219907625111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 565674936064586420333629 212128101024219907625111)
                      ·
                        rfl

theorem cell23_413118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_413118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413118 prefixEnd_413118 := by exact prefixLift 413118
  have htrace : WordTrace (prefixWord ++ tailWord_413118) baseStart_413118 baseEnd_413118 := by
    simpa [prefixWord, tailWord_413118, baseEnd_413118] using wordTrace_append hprefix tailTrace_413118
  have hstable : (prefixWord ++ tailWord_413118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413118).length < 2 ^ (prefixWord ++ tailWord_413118).sum := by decide
  have hdescent : baseEnd_413118 < baseStart_413118 := by decide
  rcases family_descends (prefixWord ++ tailWord_413118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413131 : List Nat := [1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 3]
def baseStart_413131 : Nat := 118140960795 + 413131 * 2 ^ 59
def prefixEnd_413131 : Nat := 4983230072969 + 3 ^ 40 * 413131 * 2
def baseEnd_413131 : Nat := 212134776272728356762551

theorem tailTrace_413131 : CollatzResearch.WordTrace tailWord_413131 prefixEnd_413131 212134776272728356762551 := by
  unfold tailWord_413131
  simp only [CollatzResearch.WordTrace]
  refine ⟨15068125466304419002567247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10045416977536279335044831 15068125466304419002567247)
  ·
    refine ⟨22602188199456628503850871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15068125466304419002567247 22602188199456628503850871)
    ·
      refine ⟨33903282299184942755776307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22602188199456628503850871 33903282299184942755776307)
      ·
        refine ⟨50854923448777414133664461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33903282299184942755776307 50854923448777414133664461)
        ·
          refine ⟨19070596293291530300124173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50854923448777414133664461 19070596293291530300124173)
          ·
            refine ⟨7151473609984323862546565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19070596293291530300124173 7151473609984323862546565)
            ·
              refine ⟨1340901301872060724227481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7151473609984323862546565 1340901301872060724227481)
              ·
                refine ⟨1005675976404045543170611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1340901301872060724227481 1005675976404045543170611)
                ·
                  refine ⟨1508513964606068314755917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1005675976404045543170611 1508513964606068314755917)
                  ·
                    refine ⟨565692736727275618033469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1508513964606068314755917 565692736727275618033469)
                    ·
                      refine ⟨212134776272728356762551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 565692736727275618033469 212134776272728356762551)
                      ·
                        rfl

theorem cell23_413131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 3].length) (baseStart_413131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413131 prefixEnd_413131 := by exact prefixLift 413131
  have htrace : WordTrace (prefixWord ++ tailWord_413131) baseStart_413131 baseEnd_413131 := by
    simpa [prefixWord, tailWord_413131, baseEnd_413131] using wordTrace_append hprefix tailTrace_413131
  have hstable : (prefixWord ++ tailWord_413131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413131).length < 2 ^ (prefixWord ++ tailWord_413131).sum := by decide
  have hdescent : baseEnd_413131 < baseStart_413131 := by decide
  rcases family_descends (prefixWord ++ tailWord_413131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413132 : List Nat := [2, 2, 1, 4, 2, 1, 1, 5, 1, 2, 2]
def baseStart_413132 : Nat := 118140960795 + 413132 * 2 ^ 59
def prefixEnd_413132 : Nat := 4983230072969 + 3 ^ 40 * 413132 * 2
def baseEnd_413132 : Nat := 212135289753382852850047

theorem tailTrace_413132 : CollatzResearch.WordTrace tailWord_413132 prefixEnd_413132 212135289753382852850047 := by
  unfold tailWord_413132
  simp only [CollatzResearch.WordTrace]
  refine ⟨7534080969650398086676825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10045441292867197448902433 7534080969650398086676825)
  ·
    refine ⟨5650560727237798565007619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7534080969650398086676825 5650560727237798565007619)
    ·
      refine ⟨8475841090856697847511429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5650560727237798565007619 8475841090856697847511429)
      ·
        refine ⟨1589220204535630846408393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8475841090856697847511429 1589220204535630846408393)
        ·
          refine ⟨1191915153401723134806295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1589220204535630846408393 1191915153401723134806295)
          ·
            refine ⟨1787872730102584702209443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1191915153401723134806295 1787872730102584702209443)
            ·
              refine ⟨2681809095153877053314165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1787872730102584702209443 2681809095153877053314165)
              ·
                refine ⟨251419602670675973748203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2681809095153877053314165 251419602670675973748203)
                ·
                  refine ⟨377129404006013960622305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251419602670675973748203 377129404006013960622305)
                  ·
                    refine ⟨282847053004510470466729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 377129404006013960622305 282847053004510470466729)
                    ·
                      refine ⟨212135289753382852850047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 282847053004510470466729 212135289753382852850047)
                      ·
                        rfl

theorem cell23_413132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_413132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413132 prefixEnd_413132 := by exact prefixLift 413132
  have htrace : WordTrace (prefixWord ++ tailWord_413132) baseStart_413132 baseEnd_413132 := by
    simpa [prefixWord, tailWord_413132, baseEnd_413132] using wordTrace_append hprefix tailTrace_413132
  have hstable : (prefixWord ++ tailWord_413132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413132).length < 2 ^ (prefixWord ++ tailWord_413132).sum := by decide
  have hdescent : baseEnd_413132 < baseStart_413132 := by decide
  rcases family_descends (prefixWord ++ tailWord_413132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413142 : List Nat := [5, 2, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_413142 : Nat := 118140960795 + 413142 * 2 ^ 59
def prefixEnd_413142 : Nat := 4983230072969 + 3 ^ 40 * 413142 * 2
def baseEnd_413142 : Nat := 70713474853309271241667

theorem tailTrace_413142 : CollatzResearch.WordTrace tailWord_413142 prefixEnd_413142 70713474853309271241667 := by
  unfold tailWord_413142
  simp only [CollatzResearch.WordTrace]
  refine ⟨941782916829035492576105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10045684446176378587478453 941782916829035492576105)
  ·
    refine ⟨706337187621776619432079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 941782916829035492576105 706337187621776619432079)
    ·
      refine ⟨1059505781432664929148119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 706337187621776619432079 1059505781432664929148119)
      ·
        refine ⟨1589258672148997393722179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1059505781432664929148119 1589258672148997393722179)
        ·
          refine ⟨2383888008223496090583269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1589258672148997393722179 2383888008223496090583269)
          ·
            refine ⟨446979001541905516984363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2383888008223496090583269 446979001541905516984363)
            ·
              refine ⟨670468502312858275476545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446979001541905516984363 670468502312858275476545)
              ·
                refine ⟨502851376734643706607409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 670468502312858275476545 502851376734643706607409)
                ·
                  refine ⟨377138532550982779955557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 502851376734643706607409 377138532550982779955557)
                  ·
                    refine ⟨70713474853309271241667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 377138532550982779955557 70713474853309271241667)
                    ·
                      rfl

theorem cell23_413142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_413142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413142 prefixEnd_413142 := by exact prefixLift 413142
  have htrace : WordTrace (prefixWord ++ tailWord_413142) baseStart_413142 baseEnd_413142 := by
    simpa [prefixWord, tailWord_413142, baseEnd_413142] using wordTrace_append hprefix tailTrace_413142
  have hstable : (prefixWord ++ tailWord_413142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413142).length < 2 ^ (prefixWord ++ tailWord_413142).sum := by decide
  have hdescent : baseEnd_413142 < baseStart_413142 := by decide
  rcases family_descends (prefixWord ++ tailWord_413142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413164 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 1, 8]
def baseStart_413164 : Nat := 118140960795 + 413164 * 2 ^ 59
def prefixEnd_413164 : Nat := 4983230072969 + 3 ^ 40 * 413164 * 2
def baseEnd_413164 : Nat := 70717240378108909216633

theorem tailTrace_413164 : CollatzResearch.WordTrace tailWord_413164 prefixEnd_413164 70717240378108909216633 := by
  unfold tailWord_413164
  simp only [CollatzResearch.WordTrace]
  refine ⟨7534664537592432819259273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10046219383456577092345697 7534664537592432819259273)
  ·
    refine ⟨5650998403194324614444455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7534664537592432819259273 5650998403194324614444455)
    ·
      refine ⟨8476497604791486921666683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5650998403194324614444455 8476497604791486921666683)
      ·
        refine ⟨12714746407187230382500025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8476497604791486921666683 12714746407187230382500025)
        ·
          refine ⟨9536059805390422786875019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12714746407187230382500025 9536059805390422786875019)
          ·
            refine ⟨14304089708085634180312529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9536059805390422786875019 14304089708085634180312529)
            ·
              refine ⟨10728067281064225635234397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14304089708085634180312529 10728067281064225635234397)
              ·
                refine ⟨4023025230399084613212899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10728067281064225635234397 4023025230399084613212899)
                ·
                  refine ⟨6034537845598626919819349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4023025230399084613212899 6034537845598626919819349)
                  ·
                    refine ⟨70717240378108909216633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6034537845598626919819349 70717240378108909216633)
                    ·
                      rfl

theorem cell23_413164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_413164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413164 prefixEnd_413164 := by exact prefixLift 413164
  have htrace : WordTrace (prefixWord ++ tailWord_413164) baseStart_413164 baseEnd_413164 := by
    simpa [prefixWord, tailWord_413164, baseEnd_413164] using wordTrace_append hprefix tailTrace_413164
  have hstable : (prefixWord ++ tailWord_413164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413164).length < 2 ^ (prefixWord ++ tailWord_413164).sum := by decide
  have hdescent : baseEnd_413164 < baseStart_413164 := by decide
  rcases family_descends (prefixWord ++ tailWord_413164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413191 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 5]
def baseStart_413191 : Nat := 118140960795 + 413191 * 2 ^ 59
def prefixEnd_413191 : Nat := 4983230072969 + 3 ^ 40 * 413191 * 2
def baseEnd_413191 : Nat := 212165585111998122012275

theorem tailTrace_413191 : CollatzResearch.WordTrace tailWord_413191 prefixEnd_413191 212165585111998122012275 := by
  unfold tailWord_413191
  simp only [CollatzResearch.WordTrace]
  refine ⟨15070313846087049249751427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10046875897391366166500951 15070313846087049249751427)
  ·
    refine ⟨22605470769130573874627141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15070313846087049249751427 22605470769130573874627141)
    ·
      refine ⟨4238525769211982601492589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22605470769130573874627141 4238525769211982601492589)
      ·
        refine ⟨1589447163454493475559721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4238525769211982601492589 1589447163454493475559721)
        ·
          refine ⟨1192085372590870106669791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1589447163454493475559721 1192085372590870106669791)
          ·
            refine ⟨1788128058886305160004687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192085372590870106669791 1788128058886305160004687)
            ·
              refine ⟨2682192088329457740007031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1788128058886305160004687 2682192088329457740007031)
              ·
                refine ⟨4023288132494186610010547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2682192088329457740007031 4023288132494186610010547)
                ·
                  refine ⟨6034932198741279915015821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4023288132494186610010547 6034932198741279915015821)
                  ·
                    refine ⟨2263099574527979968130933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6034932198741279915015821 2263099574527979968130933)
                    ·
                      refine ⟨212165585111998122012275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2263099574527979968130933 212165585111998122012275)
                      ·
                        rfl

theorem cell23_413191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_413191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413191 prefixEnd_413191 := by exact prefixLift 413191
  have htrace : WordTrace (prefixWord ++ tailWord_413191) baseStart_413191 baseEnd_413191 := by
    simpa [prefixWord, tailWord_413191, baseEnd_413191] using wordTrace_append hprefix tailTrace_413191
  have hstable : (prefixWord ++ tailWord_413191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413191).length < 2 ^ (prefixWord ++ tailWord_413191).sum := by decide
  have hdescent : baseEnd_413191 < baseStart_413191 := by decide
  rcases family_descends (prefixWord ++ tailWord_413191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413205 : List Nat := [1, 3, 2, 1, 3, 2, 2, 1, 4, 2, 2]
def baseStart_413205 : Nat := 118140960795 + 413205 * 2 ^ 59
def prefixEnd_413205 : Nat := 4983230072969 + 3 ^ 40 * 413205 * 2
def baseEnd_413205 : Nat := 212172773841161067237211

theorem tailTrace_413205 : CollatzResearch.WordTrace tailWord_413205 prefixEnd_413205 212172773841161067237211 := by
  unfold tailWord_413205
  simp only [CollatzResearch.WordTrace]
  refine ⟨15070824468036329640761069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10047216312024219760507379 15070824468036329640761069)
  ·
    refine ⟨5651559175513623615285401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15070824468036329640761069 5651559175513623615285401)
    ·
      refine ⟨4238669381635217711464051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5651559175513623615285401 4238669381635217711464051)
      ·
        refine ⟨6358004072452826567196077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4238669381635217711464051 6358004072452826567196077)
        ·
          refine ⟨2384251527169809962698529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6358004072452826567196077 2384251527169809962698529)
          ·
            refine ⟨1788188645377357472023897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2384251527169809962698529 1788188645377357472023897)
            ·
              refine ⟨1341141484033018104017923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1788188645377357472023897 1341141484033018104017923)
              ·
                refine ⟨2011712226049527156026885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1341141484033018104017923 2011712226049527156026885)
                ·
                  refine ⟨377196042384286341755041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2011712226049527156026885 377196042384286341755041)
                  ·
                    refine ⟨282897031788214756316281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 377196042384286341755041 282897031788214756316281)
                    ·
                      refine ⟨212172773841161067237211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 282897031788214756316281 212172773841161067237211)
                      ·
                        rfl

theorem cell23_413205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 2, 2].length) (baseStart_413205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413205 prefixEnd_413205 := by exact prefixLift 413205
  have htrace : WordTrace (prefixWord ++ tailWord_413205) baseStart_413205 baseEnd_413205 := by
    simpa [prefixWord, tailWord_413205, baseEnd_413205] using wordTrace_append hprefix tailTrace_413205
  have hstable : (prefixWord ++ tailWord_413205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413205).length < 2 ^ (prefixWord ++ tailWord_413205).sum := by decide
  have hdescent : baseEnd_413205 < baseStart_413205 := by decide
  rcases family_descends (prefixWord ++ tailWord_413205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413221 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 1, 5, 3]
def baseStart_413221 : Nat := 118140960795 + 413221 * 2 ^ 59
def prefixEnd_413221 : Nat := 4983230072969 + 3 ^ 40 * 413221 * 2
def baseEnd_413221 : Nat := 212180989531633004637137

theorem tailTrace_413221 : CollatzResearch.WordTrace tailWord_413221 prefixEnd_413221 212180989531633004637137 := by
  unfold tailWord_413221
  simp only [CollatzResearch.WordTrace]
  refine ⟨15071408035978364373343517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10047605357318909582229011 15071408035978364373343517)
  ·
    refine ⟨5651778013491886640003819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15071408035978364373343517 5651778013491886640003819)
    ·
      refine ⟨8477667020237829960005729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5651778013491886640003819 8477667020237829960005729)
      ·
        refine ⟨6358250265178372470004297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8477667020237829960005729 6358250265178372470004297)
        ·
          refine ⟨4768687698883779352503223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6358250265178372470004297 4768687698883779352503223)
          ·
            refine ⟨7153031548325669028754835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4768687698883779352503223 7153031548325669028754835)
            ·
              refine ⟨10729547322488503543132253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7153031548325669028754835 10729547322488503543132253)
              ·
                refine ⟨4023580245933188828674595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10729547322488503543132253 4023580245933188828674595)
                ·
                  refine ⟨6035370368899783243011893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4023580245933188828674595 6035370368899783243011893)
                  ·
                    refine ⟨565815972084354679032365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6035370368899783243011893 565815972084354679032365)
                    ·
                      refine ⟨212180989531633004637137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 565815972084354679032365 212180989531633004637137)
                      ·
                        rfl

theorem cell23_413221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_413221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413221 prefixEnd_413221 := by exact prefixLift 413221
  have htrace : WordTrace (prefixWord ++ tailWord_413221) baseStart_413221 baseEnd_413221 := by
    simpa [prefixWord, tailWord_413221, baseEnd_413221] using wordTrace_append hprefix tailTrace_413221
  have hstable : (prefixWord ++ tailWord_413221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413221).length < 2 ^ (prefixWord ++ tailWord_413221).sum := by decide
  have hdescent : baseEnd_413221 < baseStart_413221 := by decide
  rcases family_descends (prefixWord ++ tailWord_413221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413321 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 1, 2, 6]
def baseStart_413321 : Nat := 118140960795 + 413321 * 2 ^ 59
def prefixEnd_413321 : Nat := 4983230072969 + 3 ^ 40 * 413321 * 2
def baseEnd_413321 : Nat := 212232337597082613386677

theorem tailTrace_413321 : CollatzResearch.WordTrace tailWord_413321 prefixEnd_413321 212232337597082613386677 := by
  unfold tailWord_413321
  simp only [CollatzResearch.WordTrace]
  refine ⟨15075055335616081451983817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10050036890410720967989211 15075055335616081451983817)
  ·
    refine ⟨11306291501712061088987863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15075055335616081451983817 11306291501712061088987863)
    ·
      refine ⟨16959437252568091633481795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11306291501712061088987863 16959437252568091633481795)
      ·
        refine ⟨25439155878852137450222693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16959437252568091633481795 25439155878852137450222693)
        ·
          refine ⟨4769841727284775771916755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25439155878852137450222693 4769841727284775771916755)
          ·
            refine ⟨7154762590927163657875133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4769841727284775771916755 7154762590927163657875133)
            ·
              refine ⟨2683035971597686371703175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7154762590927163657875133 2683035971597686371703175)
              ·
                refine ⟨4024553957396529557554763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2683035971597686371703175 4024553957396529557554763)
                ·
                  refine ⟨6036830936094794336332145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4024553957396529557554763 6036830936094794336332145)
                  ·
                    refine ⟨4527623202071095752249109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6036830936094794336332145 4527623202071095752249109)
                    ·
                      refine ⟨212232337597082613386677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4527623202071095752249109 212232337597082613386677)
                      ·
                        rfl

theorem cell23_413321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 2, 6].length) (baseStart_413321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413321 prefixEnd_413321 := by exact prefixLift 413321
  have htrace : WordTrace (prefixWord ++ tailWord_413321) baseStart_413321 baseEnd_413321 := by
    simpa [prefixWord, tailWord_413321, baseEnd_413321] using wordTrace_append hprefix tailTrace_413321
  have hstable : (prefixWord ++ tailWord_413321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413321).length < 2 ^ (prefixWord ++ tailWord_413321).sum := by decide
  have hdescent : baseEnd_413321 < baseStart_413321 := by decide
  rcases family_descends (prefixWord ++ tailWord_413321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413322 : List Nat := [3, 1, 2, 3, 2, 1, 2, 4, 1, 4]
def baseStart_413322 : Nat := 118140960795 + 413322 * 2 ^ 59
def prefixEnd_413322 : Nat := 4983230072969 + 3 ^ 40 * 413322 * 2
def baseEnd_413322 : Nat := 70744283692579036491391

theorem tailTrace_413322 : CollatzResearch.WordTrace tailWord_413322 prefixEnd_413322 70744283692579036491391 := by
  unfold tailWord_413322
  simp only [CollatzResearch.WordTrace]
  refine ⟨3768772952153114655692555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10050061205741639081846813 3768772952153114655692555)
  ·
    refine ⟨5653159428229671983538833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3768772952153114655692555 5653159428229671983538833)
    ·
      refine ⟨4239869571172253987654125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5653159428229671983538833 4239869571172253987654125)
      ·
        refine ⟨1589951089189595245370297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4239869571172253987654125 1589951089189595245370297)
        ·
          refine ⟨1192463316892196434027723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1589951089189595245370297 1192463316892196434027723)
          ·
            refine ⟨1788694975338294651041585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192463316892196434027723 1788694975338294651041585)
            ·
              refine ⟨1341521231503720988281189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1788694975338294651041585 1341521231503720988281189)
              ·
                refine ⟨251535230906947685302723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1341521231503720988281189 251535230906947685302723)
                ·
                  refine ⟨377302846360421527954085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251535230906947685302723 377302846360421527954085)
                  ·
                    refine ⟨70744283692579036491391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 377302846360421527954085 70744283692579036491391)
                    ·
                      rfl

theorem cell23_413322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_413322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413322 prefixEnd_413322 := by exact prefixLift 413322
  have htrace : WordTrace (prefixWord ++ tailWord_413322) baseStart_413322 baseEnd_413322 := by
    simpa [prefixWord, tailWord_413322, baseEnd_413322] using wordTrace_append hprefix tailTrace_413322
  have hstable : (prefixWord ++ tailWord_413322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413322).length < 2 ^ (prefixWord ++ tailWord_413322).sum := by decide
  have hdescent : baseEnd_413322 < baseStart_413322 := by decide
  rcases family_descends (prefixWord ++ tailWord_413322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413335 : List Nat := [1, 1, 3, 3, 2, 3, 3, 1, 6]
def baseStart_413335 : Nat := 118140960795 + 413335 * 2 ^ 59
def prefixEnd_413335 : Nat := 4983230072969 + 3 ^ 40 * 413335 * 2
def baseEnd_413335 : Nat := 23582169591805062067957

theorem tailTrace_413335 : CollatzResearch.WordTrace tailWord_413335 prefixEnd_413335 23582169591805062067957 := by
  unfold tailWord_413335
  simp only [CollatzResearch.WordTrace]
  refine ⟨15075565957565361842993459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10050377305043574561995639 15075565957565361842993459)
  ·
    refine ⟨22613348936348042764490189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15075565957565361842993459 22613348936348042764490189)
    ·
      refine ⟨8480005851130516036683821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22613348936348042764490189 8480005851130516036683821)
      ·
        refine ⟨3180002194173943513756433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8480005851130516036683821 3180002194173943513756433)
        ·
          refine ⟨2385001645630457635317325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3180002194173943513756433 2385001645630457635317325)
          ·
            refine ⟨894375617111421613243997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2385001645630457635317325 894375617111421613243997)
            ·
              refine ⟨335390856416783104966499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 894375617111421613243997 335390856416783104966499)
              ·
                refine ⟨503086284625174657449749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335390856416783104966499 503086284625174657449749)
                ·
                  refine ⟨23582169591805062067957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 503086284625174657449749 23582169591805062067957)
                  ·
                    rfl

theorem cell23_413335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 6].length) (baseStart_413335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413335 prefixEnd_413335 := by exact prefixLift 413335
  have htrace : WordTrace (prefixWord ++ tailWord_413335) baseStart_413335 baseEnd_413335 := by
    simpa [prefixWord, tailWord_413335, baseEnd_413335] using wordTrace_append hprefix tailTrace_413335
  have hstable : (prefixWord ++ tailWord_413335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413335).length < 2 ^ (prefixWord ++ tailWord_413335).sum := by decide
  have hdescent : baseEnd_413335 < baseStart_413335 := by decide
  rcases family_descends (prefixWord ++ tailWord_413335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413372 : List Nat := [2, 2, 2, 3, 1, 3, 1, 2, 2, 3, 2]
def baseStart_413372 : Nat := 118140960795 + 413372 * 2 ^ 59
def prefixEnd_413372 : Nat := 4983230072969 + 3 ^ 40 * 413372 * 2
def baseEnd_413372 : Nat := 212258525110461913848943

theorem tailTrace_413372 : CollatzResearch.WordTrace tailWord_413372 prefixEnd_413372 212258525110461913848943 := by
  unfold tailWord_413372
  simp only [CollatzResearch.WordTrace]
  refine ⟨7538457729215658581045185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10051276972287544774726913 7538457729215658581045185)
  ·
    refine ⟨5653843296911743935783889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7538457729215658581045185 5653843296911743935783889)
    ·
      refine ⟨4240382472683807951837917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5653843296911743935783889 4240382472683807951837917)
      ·
        refine ⟨1590143427256427981939219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4240382472683807951837917 1590143427256427981939219)
        ·
          refine ⟨2385215140884641972908829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1590143427256427981939219 2385215140884641972908829)
          ·
            refine ⟨894455677831740739840811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2385215140884641972908829 894455677831740739840811)
            ·
              refine ⟨1341683516747611109761217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894455677831740739840811 1341683516747611109761217)
              ·
                refine ⟨1006262637560708332320913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1341683516747611109761217 1006262637560708332320913)
                ·
                  refine ⟨754696978170531249240685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1006262637560708332320913 754696978170531249240685)
                  ·
                    refine ⟨283011366813949218465257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 754696978170531249240685 283011366813949218465257)
                    ·
                      refine ⟨212258525110461913848943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 283011366813949218465257 212258525110461913848943)
                      ·
                        rfl

theorem cell23_413372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_413372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413372 prefixEnd_413372 := by exact prefixLift 413372
  have htrace : WordTrace (prefixWord ++ tailWord_413372) baseStart_413372 baseEnd_413372 := by
    simpa [prefixWord, tailWord_413372, baseEnd_413372] using wordTrace_append hprefix tailTrace_413372
  have hstable : (prefixWord ++ tailWord_413372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413372).length < 2 ^ (prefixWord ++ tailWord_413372).sum := by decide
  have hdescent : baseEnd_413372 < baseStart_413372 := by decide
  rcases family_descends (prefixWord ++ tailWord_413372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413402 : List Nat := [3, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4]
def baseStart_413402 : Nat := 118140960795 + 413402 * 2 ^ 59
def prefixEnd_413402 : Nat := 4983230072969 + 3 ^ 40 * 413402 * 2
def baseEnd_413402 : Nat := 212273929530096796473805

theorem tailTrace_413402 : CollatzResearch.WordTrace tailWord_413402 prefixEnd_413402 212273929530096796473805 := by
  unfold tailWord_413402
  simp only [CollatzResearch.WordTrace]
  refine ⟨3769502412080658071420615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10052006432215088190454973 3769502412080658071420615)
  ·
    refine ⟨5654253618120987107130923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3769502412080658071420615 5654253618120987107130923)
    ·
      refine ⟨8481380427181480660696385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5654253618120987107130923 8481380427181480660696385)
      ·
        refine ⟨6361035320386110495522289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8481380427181480660696385 6361035320386110495522289)
        ·
          refine ⟨4770776490289582871641717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6361035320386110495522289 4770776490289582871641717)
          ·
            refine ⟨447260295964648394216411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4770776490289582871641717 447260295964648394216411)
            ·
              refine ⟨670890443946972591324617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447260295964648394216411 670890443946972591324617)
              ·
                refine ⟨503167832960229443493463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 670890443946972591324617 503167832960229443493463)
                ·
                  refine ⟨754751749440344165240195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 503167832960229443493463 754751749440344165240195)
                  ·
                    refine ⟨1132127624160516247860293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 754751749440344165240195 1132127624160516247860293)
                    ·
                      refine ⟨212273929530096796473805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1132127624160516247860293 212273929530096796473805)
                      ·
                        rfl

theorem cell23_413402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_413402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413402 prefixEnd_413402 := by exact prefixLift 413402
  have htrace : WordTrace (prefixWord ++ tailWord_413402) baseStart_413402 baseEnd_413402 := by
    simpa [prefixWord, tailWord_413402, baseEnd_413402] using wordTrace_append hprefix tailTrace_413402
  have hstable : (prefixWord ++ tailWord_413402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413402).length < 2 ^ (prefixWord ++ tailWord_413402).sum := by decide
  have hdescent : baseEnd_413402 < baseStart_413402 := by decide
  rcases family_descends (prefixWord ++ tailWord_413402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413452 : List Nat := [2, 2, 1, 2, 2, 1, 4, 3, 2, 1, 3]
def baseStart_413452 : Nat := 118140960795 + 413452 * 2 ^ 59
def prefixEnd_413452 : Nat := 4983230072969 + 3 ^ 40 * 413452 * 2
def baseEnd_413452 : Nat := 212299603562821600848575

theorem tailTrace_413452 : CollatzResearch.WordTrace tailWord_413452 prefixEnd_413452 212299603562821600848575 := by
  unfold tailWord_413452
  simp only [CollatzResearch.WordTrace]
  refine ⟨7539916649070745412501305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10053222198760993883335073 7539916649070745412501305)
  ·
    refine ⟨5654937486803059059375979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7539916649070745412501305 5654937486803059059375979)
    ·
      refine ⟨8482406230204588589063969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5654937486803059059375979 8482406230204588589063969)
      ·
        refine ⟨6361804672653441441797977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8482406230204588589063969 6361804672653441441797977)
        ·
          refine ⟨4771353504490081081348483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6361804672653441441797977 4771353504490081081348483)
          ·
            refine ⟨7157030256735121622022725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4771353504490081081348483 7157030256735121622022725)
            ·
              refine ⟨1341943173137835304129261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7157030256735121622022725 1341943173137835304129261)
              ·
                refine ⟨503228689926688239048473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1341943173137835304129261 503228689926688239048473)
                ·
                  refine ⟨377421517445016179286355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503228689926688239048473 377421517445016179286355)
                  ·
                    refine ⟨566132276167524268929533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 377421517445016179286355 566132276167524268929533)
                    ·
                      refine ⟨212299603562821600848575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 566132276167524268929533 212299603562821600848575)
                      ·
                        rfl

theorem cell23_413452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_413452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413452 prefixEnd_413452 := by exact prefixLift 413452
  have htrace : WordTrace (prefixWord ++ tailWord_413452) baseStart_413452 baseEnd_413452 := by
    simpa [prefixWord, tailWord_413452, baseEnd_413452] using wordTrace_append hprefix tailTrace_413452
  have hstable : (prefixWord ++ tailWord_413452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413452).length < 2 ^ (prefixWord ++ tailWord_413452).sum := by decide
  have hdescent : baseEnd_413452 < baseStart_413452 := by decide
  rcases family_descends (prefixWord ++ tailWord_413452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413468 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 1, 8]
def baseStart_413468 : Nat := 118140960795 + 413468 * 2 ^ 59
def prefixEnd_413468 : Nat := 4983230072969 + 3 ^ 40 * 413468 * 2
def baseEnd_413468 : Nat := 70769273084431179416167

theorem tailTrace_413468 : CollatzResearch.WordTrace tailWord_413468 prefixEnd_413468 70769273084431179416167 := by
  unfold tailWord_413468
  simp only [CollatzResearch.WordTrace]
  refine ⟨7540208433041762778792529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10053611244055683705056705 7540208433041762778792529)
  ·
    refine ⟨5655156324781322084094397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7540208433041762778792529 5655156324781322084094397)
    ·
      refine ⟨2120683621792995781535399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5655156324781322084094397 2120683621792995781535399)
      ·
        refine ⟨3181025432689493672303099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2120683621792995781535399 3181025432689493672303099)
        ·
          refine ⟨4771538149034240508454649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3181025432689493672303099 4771538149034240508454649)
          ·
            refine ⟨3578653611775680381340987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4771538149034240508454649 3578653611775680381340987)
            ·
              refine ⟨5367980417663520572011481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3578653611775680381340987 5367980417663520572011481)
              ·
                refine ⟨4025985313247640429008611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5367980417663520572011481 4025985313247640429008611)
                ·
                  refine ⟨6038977969871460643512917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4025985313247640429008611 6038977969871460643512917)
                  ·
                    refine ⟨70769273084431179416167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6038977969871460643512917 70769273084431179416167)
                    ·
                      rfl

theorem cell23_413468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_413468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413468 prefixEnd_413468 := by exact prefixLift 413468
  have htrace : WordTrace (prefixWord ++ tailWord_413468) baseStart_413468 baseEnd_413468 := by
    simpa [prefixWord, tailWord_413468, baseEnd_413468] using wordTrace_append hprefix tailTrace_413468
  have hstable : (prefixWord ++ tailWord_413468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413468).length < 2 ^ (prefixWord ++ tailWord_413468).sum := by decide
  have hdescent : baseEnd_413468 < baseStart_413468 := by decide
  rcases family_descends (prefixWord ++ tailWord_413468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413470 : List Nat := [4, 3, 2, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_413470 : Nat := 118140960795 + 413470 * 2 ^ 59
def prefixEnd_413470 : Nat := 4983230072969 + 3 ^ 40 * 413470 * 2
def baseEnd_413470 : Nat := 212308846214602530423493

theorem tailTrace_413470 : CollatzResearch.WordTrace tailWord_413470 prefixEnd_413470 212308846214602530423493 := by
  unfold tailWord_413470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1885061226509534987394733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10053659874717519932771909 1885061226509534987394733)
  ·
    refine ⟨706897959941075620273025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1885061226509534987394733 706897959941075620273025)
    ·
      refine ⟨530173469955806715204769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 706897959941075620273025 530173469955806715204769)
      ·
        refine ⟨397630102466855036403577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 530173469955806715204769 397630102466855036403577)
        ·
          refine ⟨298222576850141277302683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397630102466855036403577 298222576850141277302683)
          ·
            refine ⟨447333865275211915954025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298222576850141277302683 447333865275211915954025)
            ·
              refine ⟨335500398956408936965519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447333865275211915954025 335500398956408936965519)
              ·
                refine ⟨503250598434613405448279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335500398956408936965519 503250598434613405448279)
                ·
                  refine ⟨754875897651920108172419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 503250598434613405448279 754875897651920108172419)
                  ·
                    refine ⟨1132313846477880162258629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 754875897651920108172419 1132313846477880162258629)
                    ·
                      refine ⟨212308846214602530423493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1132313846477880162258629 212308846214602530423493)
                      ·
                        rfl

theorem cell23_413470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_413470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413470 prefixEnd_413470 := by exact prefixLift 413470
  have htrace : WordTrace (prefixWord ++ tailWord_413470) baseStart_413470 baseEnd_413470 := by
    simpa [prefixWord, tailWord_413470, baseEnd_413470] using wordTrace_append hprefix tailTrace_413470
  have hstable : (prefixWord ++ tailWord_413470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413470).length < 2 ^ (prefixWord ++ tailWord_413470).sum := by decide
  have hdescent : baseEnd_413470 < baseStart_413470 := by decide
  rcases family_descends (prefixWord ++ tailWord_413470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413565 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 6, 1, 4]
def baseStart_413565 : Nat := 118140960795 + 413565 * 2 ^ 59
def prefixEnd_413565 : Nat := 4983230072969 + 3 ^ 40 * 413565 * 2
def baseEnd_413565 : Nat := 212357626876779658735555

theorem tailTrace_413565 : CollatzResearch.WordTrace tailWord_413565 prefixEnd_413565 212357626876779658735555 := by
  unfold tailWord_413565
  simp only [CollatzResearch.WordTrace]
  refine ⟨15083954746732111123866149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10055969831154740749244099 15083954746732111123866149)
  ·
    refine ⟨2828241515012270835724903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15083954746732111123866149 2828241515012270835724903)
    ·
      refine ⟨4242362272518406253587355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2828241515012270835724903 4242362272518406253587355)
      ·
        refine ⟨6363543408777609380381033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4242362272518406253587355 6363543408777609380381033)
        ·
          refine ⟨4772657556583207035285775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6363543408777609380381033 4772657556583207035285775)
          ·
            refine ⟨7158986334874810552928663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4772657556583207035285775 7158986334874810552928663)
            ·
              refine ⟨10738479502312215829392995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7158986334874810552928663 10738479502312215829392995)
              ·
                refine ⟨16107719253468323744089493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10738479502312215829392995 16107719253468323744089493)
                ·
                  refine ⟨755049340006327675504195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16107719253468323744089493 755049340006327675504195)
                  ·
                    refine ⟨1132574010009491513256293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 755049340006327675504195 1132574010009491513256293)
                    ·
                      refine ⟨212357626876779658735555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1132574010009491513256293 212357626876779658735555)
                      ·
                        rfl

theorem cell23_413565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_413565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413565 prefixEnd_413565 := by exact prefixLift 413565
  have htrace : WordTrace (prefixWord ++ tailWord_413565) baseStart_413565 baseEnd_413565 := by
    simpa [prefixWord, tailWord_413565, baseEnd_413565] using wordTrace_append hprefix tailTrace_413565
  have hstable : (prefixWord ++ tailWord_413565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413565).length < 2 ^ (prefixWord ++ tailWord_413565).sum := by decide
  have hdescent : baseEnd_413565 < baseStart_413565 := by decide
  rcases family_descends (prefixWord ++ tailWord_413565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413585 : List Nat := [1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 3]
def baseStart_413585 : Nat := 118140960795 + 413585 * 2 ^ 59
def prefixEnd_413585 : Nat := 4983230072969 + 3 ^ 40 * 413585 * 2
def baseEnd_413585 : Nat := 212367896489869580485463

theorem tailTrace_413585 : CollatzResearch.WordTrace tailWord_413585 prefixEnd_413585 212367896489869580485463 := by
  unfold tailWord_413585
  simp only [CollatzResearch.WordTrace]
  refine ⟨15084684206659654539594209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10056456137773103026396139 15084684206659654539594209)
  ·
    refine ⟨11313513154994740904695657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15084684206659654539594209 11313513154994740904695657)
    ·
      refine ⟨8485134866246055678521743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11313513154994740904695657 8485134866246055678521743)
      ·
        refine ⟨12727702299369083517782615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8485134866246055678521743 12727702299369083517782615)
        ·
          refine ⟨19091553449053625276673923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12727702299369083517782615 19091553449053625276673923)
          ·
            refine ⟨28637330173580437915010885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19091553449053625276673923 28637330173580437915010885)
            ·
              refine ⟨5369499407546332109064541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28637330173580437915010885 5369499407546332109064541)
              ·
                refine ⟨2013562277829874540899203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5369499407546332109064541 2013562277829874540899203)
                ·
                  refine ⟨3020343416744811811348805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2013562277829874540899203 3020343416744811811348805)
                  ·
                    refine ⟨566314390639652214627901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3020343416744811811348805 566314390639652214627901)
                    ·
                      refine ⟨212367896489869580485463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 566314390639652214627901 212367896489869580485463)
                      ·
                        rfl

theorem cell23_413585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 3].length) (baseStart_413585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413585 prefixEnd_413585 := by exact prefixLift 413585
  have htrace : WordTrace (prefixWord ++ tailWord_413585) baseStart_413585 baseEnd_413585 := by
    simpa [prefixWord, tailWord_413585, baseEnd_413585] using wordTrace_append hprefix tailTrace_413585
  have hstable : (prefixWord ++ tailWord_413585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413585).length < 2 ^ (prefixWord ++ tailWord_413585).sum := by decide
  have hdescent : baseEnd_413585 < baseStart_413585 := by decide
  rcases family_descends (prefixWord ++ tailWord_413585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413665 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 3, 6]
def baseStart_413665 : Nat := 118140960795 + 413665 * 2 ^ 59
def prefixEnd_413665 : Nat := 4983230072969 + 3 ^ 40 * 413665 * 2
def baseEnd_413665 : Nat := 70802991647409755828365

theorem tailTrace_413665 : CollatzResearch.WordTrace tailWord_413665 prefixEnd_413665 70802991647409755828365 := by
  unfold tailWord_413665
  simp only [CollatzResearch.WordTrace]
  refine ⟨15087602046369828202506449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10058401364246552135004299 15087602046369828202506449)
  ·
    refine ⟨11315701534777371151879837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15087602046369828202506449 11315701534777371151879837)
    ·
      refine ⟨4243388075541514181954939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11315701534777371151879837 4243388075541514181954939)
      ·
        refine ⟨6365082113312271272932409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4243388075541514181954939 6365082113312271272932409)
        ·
          refine ⟨4773811584984203454699307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6365082113312271272932409 4773811584984203454699307)
          ·
            refine ⟨7160717377476305182048961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4773811584984203454699307 7160717377476305182048961)
            ·
              refine ⟨5370538033107228886536721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7160717377476305182048961 5370538033107228886536721)
              ·
                refine ⟨4027903524830421664902541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5370538033107228886536721 4027903524830421664902541)
                ·
                  refine ⟨1510463821811408124338453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4027903524830421664902541 1510463821811408124338453)
                  ·
                    refine ⟨70802991647409755828365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1510463821811408124338453 70802991647409755828365)
                    ·
                      rfl

theorem cell23_413665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_413665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413665 prefixEnd_413665 := by exact prefixLift 413665
  have htrace : WordTrace (prefixWord ++ tailWord_413665) baseStart_413665 baseEnd_413665 := by
    simpa [prefixWord, tailWord_413665, baseEnd_413665] using wordTrace_append hprefix tailTrace_413665
  have hstable : (prefixWord ++ tailWord_413665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413665).length < 2 ^ (prefixWord ++ tailWord_413665).sum := by decide
  have hdescent : baseEnd_413665 < baseStart_413665 := by decide
  rcases family_descends (prefixWord ++ tailWord_413665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413686 : List Nat := [5, 1, 1, 1, 4, 1, 2, 2, 1, 5]
def baseStart_413686 : Nat := 118140960795 + 413686 * 2 ^ 59
def prefixEnd_413686 : Nat := 4983230072969 + 3 ^ 40 * 413686 * 2
def baseEnd_413686 : Nat := 70806586011991228440833

theorem tailTrace_413686 : CollatzResearch.WordTrace tailWord_413686 prefixEnd_413686 70806586011991228440833 := by
  unfold tailWord_413686
  simp only [CollatzResearch.WordTrace]
  refine ⟨943022998705859299313807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10058911986195832526013941 943022998705859299313807)
  ·
    refine ⟨1414534498058788948970711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 943022998705859299313807 1414534498058788948970711)
    ·
      refine ⟨2121801747088183423456067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1414534498058788948970711 2121801747088183423456067)
      ·
        refine ⟨3182702620632275135184101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2121801747088183423456067 3182702620632275135184101)
        ·
          refine ⟨596756741368551587847019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3182702620632275135184101 596756741368551587847019)
          ·
            refine ⟨895135112052827381770529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596756741368551587847019 895135112052827381770529)
            ·
              refine ⟨671351334039620536327897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 895135112052827381770529 671351334039620536327897)
              ·
                refine ⟨503513500529715402245923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 671351334039620536327897 503513500529715402245923)
                ·
                  refine ⟨755270250794573103368885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 503513500529715402245923 755270250794573103368885)
                  ·
                    refine ⟨70806586011991228440833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 755270250794573103368885 70806586011991228440833)
                    ·
                      rfl

theorem cell23_413686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_413686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413686 prefixEnd_413686 := by exact prefixLift 413686
  have htrace : WordTrace (prefixWord ++ tailWord_413686) baseStart_413686 baseEnd_413686 := by
    simpa [prefixWord, tailWord_413686, baseEnd_413686] using wordTrace_append hprefix tailTrace_413686
  have hstable : (prefixWord ++ tailWord_413686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413686).length < 2 ^ (prefixWord ++ tailWord_413686).sum := by decide
  have hdescent : baseEnd_413686 < baseStart_413686 := by decide
  rcases family_descends (prefixWord ++ tailWord_413686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413689 : List Nat := [1, 2, 1, 3, 1, 5, 2, 2, 1, 1, 4]
def baseStart_413689 : Nat := 118140960795 + 413689 * 2 ^ 59
def prefixEnd_413689 : Nat := 4983230072969 + 3 ^ 40 * 413689 * 2
def baseEnd_413689 : Nat := 212421298477937173584985

theorem tailTrace_413689 : CollatzResearch.WordTrace tailWord_413689 prefixEnd_413689 212421298477937173584985 := by
  unfold tailWord_413689
  simp only [CollatzResearch.WordTrace]
  refine ⟨15088477398282880301380121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10058984932188586867586747 15088477398282880301380121)
  ·
    refine ⟨11316358048712160226035091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15088477398282880301380121 11316358048712160226035091)
    ·
      refine ⟨16974537073068240339052637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11316358048712160226035091 16974537073068240339052637)
      ·
        refine ⟨6365451402400590127144739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16974537073068240339052637 6365451402400590127144739)
        ·
          refine ⟨9548177103600885190717109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6365451402400590127144739 9548177103600885190717109)
          ·
            refine ⟨895141603462582986629729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9548177103600885190717109 895141603462582986629729)
            ·
              refine ⟨671356202596937239972297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 895141603462582986629729 671356202596937239972297)
              ·
                refine ⟨503517151947702929979223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 671356202596937239972297 503517151947702929979223)
                ·
                  refine ⟨755275727921554394968835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 503517151947702929979223 755275727921554394968835)
                  ·
                    refine ⟨1132913591882331592453253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 755275727921554394968835 1132913591882331592453253)
                    ·
                      refine ⟨212421298477937173584985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1132913591882331592453253 212421298477937173584985)
                      ·
                        rfl

theorem cell23_413689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_413689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413689 prefixEnd_413689 := by exact prefixLift 413689
  have htrace : WordTrace (prefixWord ++ tailWord_413689) baseStart_413689 baseEnd_413689 := by
    simpa [prefixWord, tailWord_413689, baseEnd_413689] using wordTrace_append hprefix tailTrace_413689
  have hstable : (prefixWord ++ tailWord_413689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413689).length < 2 ^ (prefixWord ++ tailWord_413689).sum := by decide
  have hdescent : baseEnd_413689 < baseStart_413689 := by decide
  rcases family_descends (prefixWord ++ tailWord_413689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413755 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 1, 8]
def baseStart_413755 : Nat := 118140960795 + 413755 * 2 ^ 59
def prefixEnd_413755 : Nat := 4983230072969 + 3 ^ 40 * 413755 * 2
def baseEnd_413755 : Nat := 70818396067044638453227

theorem tailTrace_413755 : CollatzResearch.WordTrace tailWord_413755 prefixEnd_413755 70818396067044638453227 := by
  unfold tailWord_413755
  simp only [CollatzResearch.WordTrace]
  refine ⟨15090884616043773573282719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10060589744029182382188479 15090884616043773573282719)
  ·
    refine ⟨22636326924065660359924079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15090884616043773573282719 22636326924065660359924079)
    ·
      refine ⟨33954490386098490539886119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22636326924065660359924079 33954490386098490539886119)
      ·
        refine ⟨50931735579147735809829179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33954490386098490539886119 50931735579147735809829179)
        ·
          refine ⟨76397603368721603714743769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50931735579147735809829179 76397603368721603714743769)
          ·
            refine ⟨57298202526541202786057827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76397603368721603714743769 57298202526541202786057827)
            ·
              refine ⟨85947303789811804179086741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57298202526541202786057827 85947303789811804179086741)
              ·
                refine ⟨4028779865147428320894691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85947303789811804179086741 4028779865147428320894691)
                ·
                  refine ⟨6043169797721142481342037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4028779865147428320894691 6043169797721142481342037)
                  ·
                    refine ⟨70818396067044638453227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6043169797721142481342037 70818396067044638453227)
                    ·
                      rfl

theorem cell23_413755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 8].length) (baseStart_413755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413755 prefixEnd_413755 := by exact prefixLift 413755
  have htrace : WordTrace (prefixWord ++ tailWord_413755) baseStart_413755 baseEnd_413755 := by
    simpa [prefixWord, tailWord_413755, baseEnd_413755] using wordTrace_append hprefix tailTrace_413755
  have hstable : (prefixWord ++ tailWord_413755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413755).length < 2 ^ (prefixWord ++ tailWord_413755).sum := by decide
  have hdescent : baseEnd_413755 < baseStart_413755 := by decide
  rcases family_descends (prefixWord ++ tailWord_413755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413773 : List Nat := [1, 6, 1, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_413773 : Nat := 118140960795 + 413773 * 2 ^ 59
def prefixEnd_413773 : Nat := 4983230072969 + 3 ^ 40 * 413773 * 2
def baseEnd_413773 : Nat := 212464430852914844934599

theorem tailTrace_413773 : CollatzResearch.WordTrace tailWord_413773 prefixEnd_413773 212464430852914844934599 := by
  unfold tailWord_413773
  simp only [CollatzResearch.WordTrace]
  refine ⟨15091541129978562647437973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10061027419985708431625315 15091541129978562647437973)
  ·
    refine ⟨707415990467745124098655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15091541129978562647437973 707415990467745124098655)
    ·
      refine ⟨1061123985701617686147983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 707415990467745124098655 1061123985701617686147983)
      ·
        refine ⟨1591685978552426529221975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1061123985701617686147983 1591685978552426529221975)
        ·
          refine ⟨2387528967828639793832963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1591685978552426529221975 2387528967828639793832963)
          ·
            refine ⟨3581293451742959690749445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2387528967828639793832963 3581293451742959690749445)
            ·
              refine ⟨671492522201804942015521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3581293451742959690749445 671492522201804942015521)
              ·
                refine ⟨503619391651353706511641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 671492522201804942015521 503619391651353706511641)
                ·
                  refine ⟨377714543738515279883731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503619391651353706511641 377714543738515279883731)
                  ·
                    refine ⟨566571815607772919825597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 377714543738515279883731 566571815607772919825597)
                    ·
                      refine ⟨212464430852914844934599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 566571815607772919825597 212464430852914844934599)
                      ·
                        rfl

theorem cell23_413773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_413773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413773 prefixEnd_413773 := by exact prefixLift 413773
  have htrace : WordTrace (prefixWord ++ tailWord_413773) baseStart_413773 baseEnd_413773 := by
    simpa [prefixWord, tailWord_413773, baseEnd_413773] using wordTrace_append hprefix tailTrace_413773
  have hstable : (prefixWord ++ tailWord_413773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413773).length < 2 ^ (prefixWord ++ tailWord_413773).sum := by decide
  have hdescent : baseEnd_413773 < baseStart_413773 := by decide
  rcases family_descends (prefixWord ++ tailWord_413773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413789 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 1, 8]
def baseStart_413789 : Nat := 118140960795 + 413789 * 2 ^ 59
def prefixEnd_413789 : Nat := 4983230072969 + 3 ^ 40 * 413789 * 2
def baseEnd_413789 : Nat := 70824215514462260778175

theorem tailTrace_413789 : CollatzResearch.WordTrace tailWord_413789 prefixEnd_413789 70824215514462260778175 := by
  unfold tailWord_413789
  simp only [CollatzResearch.WordTrace]
  refine ⟨15092124697920597380020421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10061416465280398253346947 15092124697920597380020421)
  ·
    refine ⟨2829773380860112008753829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15092124697920597380020421 2829773380860112008753829)
    ·
      refine ⟨530582508911271001641343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2829773380860112008753829 530582508911271001641343)
      ·
        refine ⟨795873763366906502462015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530582508911271001641343 795873763366906502462015)
        ·
          refine ⟨1193810645050359753693023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795873763366906502462015 1193810645050359753693023)
          ·
            refine ⟨1790715967575539630539535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1193810645050359753693023 1790715967575539630539535)
            ·
              refine ⟨2686073951363309445809303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1790715967575539630539535 2686073951363309445809303)
              ·
                refine ⟨4029110927044964168713955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2686073951363309445809303 4029110927044964168713955)
                ·
                  refine ⟨6043666390567446253070933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4029110927044964168713955 6043666390567446253070933)
                  ·
                    refine ⟨70824215514462260778175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6043666390567446253070933 70824215514462260778175)
                    ·
                      rfl

theorem cell23_413789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_413789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413789 prefixEnd_413789 := by exact prefixLift 413789
  have htrace : WordTrace (prefixWord ++ tailWord_413789) baseStart_413789 baseEnd_413789 := by
    simpa [prefixWord, tailWord_413789, baseEnd_413789] using wordTrace_append hprefix tailTrace_413789
  have hstable : (prefixWord ++ tailWord_413789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413789).length < 2 ^ (prefixWord ++ tailWord_413789).sum := by decide
  have hdescent : baseEnd_413789 < baseStart_413789 := by decide
  rcases family_descends (prefixWord ++ tailWord_413789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413790 : List Nat := [4, 4, 1, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_413790 : Nat := 118140960795 + 413790 * 2 ^ 59
def prefixEnd_413790 : Nat := 4983230072969 + 3 ^ 40 * 413790 * 2
def baseEnd_413790 : Nat := 212473160024041278422021

theorem tailTrace_413790 : CollatzResearch.WordTrace tailWord_413790 prefixEnd_413790 212473160024041278422021 := by
  unfold tailWord_413790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1886520146364621818850853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10061440780611316367204549 1886520146364621818850853)
  ·
    refine ⟨353722527443366591034535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1886520146364621818850853 353722527443366591034535)
    ·
      refine ⟨530583791165049886551803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353722527443366591034535 530583791165049886551803)
      ·
        refine ⟨795875686747574829827705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530583791165049886551803 795875686747574829827705)
        ·
          refine ⟨596906765060681122370779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 795875686747574829827705 596906765060681122370779)
          ·
            refine ⟨895360147591021683556169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596906765060681122370779 895360147591021683556169)
            ·
              refine ⟨671520110693266262667127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 895360147591021683556169 671520110693266262667127)
              ·
                refine ⟨1007280166039899394000691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671520110693266262667127 1007280166039899394000691)
                ·
                  refine ⟨1510920249059849091001037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1007280166039899394000691 1510920249059849091001037)
                  ·
                    refine ⟨566595093397443409125389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1510920249059849091001037 566595093397443409125389)
                    ·
                      refine ⟨212473160024041278422021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 566595093397443409125389 212473160024041278422021)
                      ·
                        rfl

theorem cell23_413790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_413790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413790 prefixEnd_413790 := by exact prefixLift 413790
  have htrace : WordTrace (prefixWord ++ tailWord_413790) baseStart_413790 baseEnd_413790 := by
    simpa [prefixWord, tailWord_413790, baseEnd_413790] using wordTrace_append hprefix tailTrace_413790
  have hstable : (prefixWord ++ tailWord_413790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413790).length < 2 ^ (prefixWord ++ tailWord_413790).sum := by decide
  have hdescent : baseEnd_413790 < baseStart_413790 := by decide
  rcases family_descends (prefixWord ++ tailWord_413790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413792 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 4]
def baseStart_413792 : Nat := 118140960795 + 413792 * 2 ^ 59
def prefixEnd_413792 : Nat := 4983230072969 + 3 ^ 40 * 413792 * 2
def baseEnd_413792 : Nat := 212474186985350270597011

theorem tailTrace_413792 : CollatzResearch.WordTrace tailWord_413792 prefixEnd_413792 212474186985350270597011 := by
  unfold tailWord_413792
  simp only [CollatzResearch.WordTrace]
  refine ⟨7546117058454864446189815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10061489411273152594919753 7546117058454864446189815)
  ·
    refine ⟨11319175587682296669284723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7546117058454864446189815 11319175587682296669284723)
    ·
      refine ⟨16978763381523445003927085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11319175587682296669284723 16978763381523445003927085)
      ·
        refine ⟨6367036268071291876472657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16978763381523445003927085 6367036268071291876472657)
        ·
          refine ⟨4775277201053468907354493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6367036268071291876472657 4775277201053468907354493)
          ·
            refine ⟨1790728950395050840257935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4775277201053468907354493 1790728950395050840257935)
            ·
              refine ⟨2686093425592576260386903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1790728950395050840257935 2686093425592576260386903)
              ·
                refine ⟨4029140138388864390580355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2686093425592576260386903 4029140138388864390580355)
                ·
                  refine ⟨6043710207583296585870533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4029140138388864390580355 6043710207583296585870533)
                  ·
                    refine ⟨1133195663921868109850725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6043710207583296585870533 1133195663921868109850725)
                    ·
                      refine ⟨212474186985350270597011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1133195663921868109850725 212474186985350270597011)
                      ·
                        rfl

theorem cell23_413792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_413792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413792 prefixEnd_413792 := by exact prefixLift 413792
  have htrace : WordTrace (prefixWord ++ tailWord_413792) baseStart_413792 baseEnd_413792 := by
    simpa [prefixWord, tailWord_413792, baseEnd_413792] using wordTrace_append hprefix tailTrace_413792
  have hstable : (prefixWord ++ tailWord_413792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413792).length < 2 ^ (prefixWord ++ tailWord_413792).sum := by decide
  have hdescent : baseEnd_413792 < baseStart_413792 := by decide
  rcases family_descends (prefixWord ++ tailWord_413792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413829 : List Nat := [1, 3, 1, 1, 5, 1, 1, 2, 2, 3, 3]
def baseStart_413829 : Nat := 118140960795 + 413829 * 2 ^ 59
def prefixEnd_413829 : Nat := 4983230072969 + 3 ^ 40 * 413829 * 2
def baseEnd_413829 : Nat := 212493185769566625834341

theorem tailTrace_413829 : CollatzResearch.WordTrace tailWord_413829 prefixEnd_413829 212493185769566625834341 := by
  unfold tailWord_413829
  simp only [CollatzResearch.WordTrace]
  refine ⟨15093583617775684211476541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10062389078517122807651027 15093583617775684211476541)
  ·
    refine ⟨5660093856665881579303703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15093583617775684211476541 5660093856665881579303703)
    ·
      refine ⟨8490140784998822368955555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5660093856665881579303703 8490140784998822368955555)
      ·
        refine ⟨12735211177498233553433333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8490140784998822368955555 12735211177498233553433333)
        ·
          refine ⟨1193926047890459395634375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12735211177498233553433333 1193926047890459395634375)
          ·
            refine ⟨1790889071835689093451563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1193926047890459395634375 1790889071835689093451563)
            ·
              refine ⟨2686333607753533640177345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1790889071835689093451563 2686333607753533640177345)
              ·
                refine ⟨2014750205815150230133009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2686333607753533640177345 2014750205815150230133009)
                ·
                  refine ⟨1511062654361362672599757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2014750205815150230133009 1511062654361362672599757)
                  ·
                    refine ⟨566648495385511002224909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1511062654361362672599757 566648495385511002224909)
                    ·
                      refine ⟨212493185769566625834341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 566648495385511002224909 212493185769566625834341)
                      ·
                        rfl

theorem cell23_413829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 3, 3].length) (baseStart_413829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413829 prefixEnd_413829 := by exact prefixLift 413829
  have htrace : WordTrace (prefixWord ++ tailWord_413829) baseStart_413829 baseEnd_413829 := by
    simpa [prefixWord, tailWord_413829, baseEnd_413829] using wordTrace_append hprefix tailTrace_413829
  have hstable : (prefixWord ++ tailWord_413829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413829).length < 2 ^ (prefixWord ++ tailWord_413829).sum := by decide
  have hdescent : baseEnd_413829 < baseStart_413829 := by decide
  rcases family_descends (prefixWord ++ tailWord_413829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413882 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6]
def baseStart_413882 : Nat := 118140960795 + 413882 * 2 ^ 59
def prefixEnd_413882 : Nat := 4983230072969 + 3 ^ 40 * 413882 * 2
def baseEnd_413882 : Nat := 212520400244254918471597

theorem tailTrace_413882 : CollatzResearch.WordTrace tailWord_413882 prefixEnd_413882 212520400244254918471597 := by
  unfold tailWord_413882
  simp only [CollatzResearch.WordTrace]
  refine ⟨3773879171645918565788975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10063677791055782842103933 3773879171645918565788975)
  ·
    refine ⟨5660818757468877848683463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3773879171645918565788975 5660818757468877848683463)
    ·
      refine ⟨8491228136203316773025195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5660818757468877848683463 8491228136203316773025195)
      ·
        refine ⟨12736842204304975159537793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8491228136203316773025195 12736842204304975159537793)
        ·
          refine ⟨9552631653228731369653345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12736842204304975159537793 9552631653228731369653345)
          ·
            refine ⟨7164473739921548527240009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9552631653228731369653345 7164473739921548527240009)
            ·
              refine ⟨5373355304941161395430007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7164473739921548527240009 5373355304941161395430007)
              ·
                refine ⟨8060032957411742093145011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5373355304941161395430007 8060032957411742093145011)
                ·
                  refine ⟨12090049436117613139717517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8060032957411742093145011 12090049436117613139717517)
                  ·
                    refine ⟨4533768538544104927394069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12090049436117613139717517 4533768538544104927394069)
                    ·
                      refine ⟨212520400244254918471597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4533768538544104927394069 212520400244254918471597)
                      ·
                        rfl

theorem cell23_413882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_413882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413882 prefixEnd_413882 := by exact prefixLift 413882
  have htrace : WordTrace (prefixWord ++ tailWord_413882) baseStart_413882 baseEnd_413882 := by
    simpa [prefixWord, tailWord_413882, baseEnd_413882] using wordTrace_append hprefix tailTrace_413882
  have hstable : (prefixWord ++ tailWord_413882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413882).length < 2 ^ (prefixWord ++ tailWord_413882).sum := by decide
  have hdescent : baseEnd_413882 < baseStart_413882 := by decide
  rcases family_descends (prefixWord ++ tailWord_413882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413969 : List Nat := [1, 2, 2, 1, 1, 5, 1, 3, 1, 6]
def baseStart_413969 : Nat := 118140960795 + 413969 * 2 ^ 59
def prefixEnd_413969 : Nat := 4983230072969 + 3 ^ 40 * 413969 * 2
def baseEnd_413969 : Nat := 70855024353732026027899

theorem tailTrace_413969 : CollatzResearch.WordTrace tailWord_413969 prefixEnd_413969 70855024353732026027899 := by
  unfold tailWord_413969
  simp only [CollatzResearch.WordTrace]
  refine ⟨15098689837268488121572961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10065793224845658747715307 15098689837268488121572961)
  ·
    refine ⟨11324017377951366091179721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15098689837268488121572961 11324017377951366091179721)
    ·
      refine ⟨8493013033463524568384791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11324017377951366091179721 8493013033463524568384791)
      ·
        refine ⟨12739519550195286852577187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8493013033463524568384791 12739519550195286852577187)
        ·
          refine ⟨19109279325292930278865781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12739519550195286852577187 19109279325292930278865781)
          ·
            refine ⟨1791494936746212213643667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19109279325292930278865781 1791494936746212213643667)
            ·
              refine ⟨2687242405119318320465501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1791494936746212213643667 2687242405119318320465501)
              ·
                refine ⟨1007715901919744370174563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2687242405119318320465501 1007715901919744370174563)
                ·
                  refine ⟨1511573852879616555261845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1007715901919744370174563 1511573852879616555261845)
                  ·
                    refine ⟨70855024353732026027899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1511573852879616555261845 70855024353732026027899)
                    ·
                      rfl

theorem cell23_413969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 6].length) (baseStart_413969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413969 prefixEnd_413969 := by exact prefixLift 413969
  have htrace : WordTrace (prefixWord ++ tailWord_413969) baseStart_413969 baseEnd_413969 := by
    simpa [prefixWord, tailWord_413969, baseEnd_413969] using wordTrace_append hprefix tailTrace_413969
  have hstable : (prefixWord ++ tailWord_413969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413969).length < 2 ^ (prefixWord ++ tailWord_413969).sum := by decide
  have hdescent : baseEnd_413969 < baseStart_413969 := by decide
  rcases family_descends (prefixWord ++ tailWord_413969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413976 : List Nat := [2, 1, 2, 3, 1, 2, 2, 4, 1, 1, 4]
def baseStart_413976 : Nat := 118140960795 + 413976 * 2 ^ 59
def prefixEnd_413976 : Nat := 4983230072969 + 3 ^ 40 * 413976 * 2
def baseEnd_413976 : Nat := 212568667425777550696165

theorem tailTrace_413976 : CollatzResearch.WordTrace tailWord_413976 prefixEnd_413976 212568667425777550696165 := by
  unfold tailWord_413976
  simp only [CollatzResearch.WordTrace]
  refine ⟨7549472574121564158538891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10065963432162085544718521 7549472574121564158538891)
  ·
    refine ⟨11324208861182346237808337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7549472574121564158538891 11324208861182346237808337)
    ·
      refine ⟨8493156645886759678356253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11324208861182346237808337 8493156645886759678356253)
      ·
        refine ⟨3184933742207534879383595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8493156645886759678356253 3184933742207534879383595)
        ·
          refine ⟨4777400613311302319075393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3184933742207534879383595 4777400613311302319075393)
          ·
            refine ⟨3583050459983476739306545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4777400613311302319075393 3583050459983476739306545)
            ·
              refine ⟨2687287844987607554479909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3583050459983476739306545 2687287844987607554479909)
              ·
                refine ⟨503866470935176416464983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2687287844987607554479909 503866470935176416464983)
                ·
                  refine ⟨755799706402764624697475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 503866470935176416464983 755799706402764624697475)
                  ·
                    refine ⟨1133699559604146937046213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 755799706402764624697475 1133699559604146937046213)
                    ·
                      refine ⟨212568667425777550696165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1133699559604146937046213 212568667425777550696165)
                      ·
                        rfl

theorem cell23_413976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_413976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413976 prefixEnd_413976 := by exact prefixLift 413976
  have htrace : WordTrace (prefixWord ++ tailWord_413976) baseStart_413976 baseEnd_413976 := by
    simpa [prefixWord, tailWord_413976, baseEnd_413976] using wordTrace_append hprefix tailTrace_413976
  have hstable : (prefixWord ++ tailWord_413976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413976).length < 2 ^ (prefixWord ++ tailWord_413976).sum := by decide
  have hdescent : baseEnd_413976 < baseStart_413976 := by decide
  rcases family_descends (prefixWord ++ tailWord_413976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413986 : List Nat := [3, 3, 1, 1, 3, 1, 2, 2, 1, 6]
def baseStart_413986 : Nat := 118140960795 + 413986 * 2 ^ 59
def prefixEnd_413986 : Nat := 4983230072969 + 3 ^ 40 * 413986 * 2
def baseEnd_413986 : Nat := 70857934077440837190373

theorem tailTrace_413986 : CollatzResearch.WordTrace tailWord_413986 prefixEnd_413986 70857934077440837190373 := by
  unfold tailWord_413986
  simp only [CollatzResearch.WordTrace]
  refine ⟨3774827469551725006235453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10066206585471266683294541 3774827469551725006235453)
  ·
    refine ⟨1415560301081896877338295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3774827469551725006235453 1415560301081896877338295)
    ·
      refine ⟨2123340451622845316007443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1415560301081896877338295 2123340451622845316007443)
      ·
        refine ⟨3185010677434267974011165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2123340451622845316007443 3185010677434267974011165)
        ·
          refine ⟨1194379004037850490254187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3185010677434267974011165 1194379004037850490254187)
          ·
            refine ⟨1791568506056775735381281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1194379004037850490254187 1791568506056775735381281)
            ·
              refine ⟨1343676379542581801535961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1791568506056775735381281 1343676379542581801535961)
              ·
                refine ⟨1007757284656936351151971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1343676379542581801535961 1007757284656936351151971)
                ·
                  refine ⟨1511635926985404526727957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1007757284656936351151971 1511635926985404526727957)
                  ·
                    refine ⟨70857934077440837190373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1511635926985404526727957 70857934077440837190373)
                    ·
                      rfl

theorem cell23_413986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_413986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_413986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_413986 prefixEnd_413986 := by exact prefixLift 413986
  have htrace : WordTrace (prefixWord ++ tailWord_413986) baseStart_413986 baseEnd_413986 := by
    simpa [prefixWord, tailWord_413986, baseEnd_413986] using wordTrace_append hprefix tailTrace_413986
  have hstable : (prefixWord ++ tailWord_413986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413986).length < 2 ^ (prefixWord ++ tailWord_413986).sum := by decide
  have hdescent : baseEnd_413986 < baseStart_413986 := by decide
  rcases family_descends (prefixWord ++ tailWord_413986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414010 : List Nat := [3, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2]
def baseStart_414010 : Nat := 118140960795 + 414010 * 2 ^ 59
def prefixEnd_414010 : Nat := 4983230072969 + 3 ^ 40 * 414010 * 2
def baseEnd_414010 : Nat := 212586125768030417671009

theorem tailTrace_414010 : CollatzResearch.WordTrace tailWord_414010 prefixEnd_414010 212586125768030417671009 := by
  unfold tailWord_414010
  simp only [CollatzResearch.WordTrace]
  refine ⟨3775046307529988030953871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10066790153413301415876989 3775046307529988030953871)
  ·
    refine ⟨5662569461294982046430807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3775046307529988030953871 5662569461294982046430807)
    ·
      refine ⟨8493854191942473069646211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5662569461294982046430807 8493854191942473069646211)
      ·
        refine ⟨12740781287913709604469317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8493854191942473069646211 12740781287913709604469317)
        ·
          refine ⟨2388896491483820550837997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12740781287913709604469317 2388896491483820550837997)
          ·
            refine ⟨895836184306432706564249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2388896491483820550837997 895836184306432706564249)
            ·
              refine ⟨671877138229824529923187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 895836184306432706564249 671877138229824529923187)
              ·
                refine ⟨1007815707344736794884781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671877138229824529923187 1007815707344736794884781)
                ·
                  refine ⟨377930890254276298081793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1007815707344736794884781 377930890254276298081793)
                  ·
                    refine ⟨283448167690707223561345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 377930890254276298081793 283448167690707223561345)
                    ·
                      refine ⟨212586125768030417671009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 283448167690707223561345 212586125768030417671009)
                      ·
                        rfl

theorem cell23_414010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2].length) (baseStart_414010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414010 prefixEnd_414010 := by exact prefixLift 414010
  have htrace : WordTrace (prefixWord ++ tailWord_414010) baseStart_414010 baseEnd_414010 := by
    simpa [prefixWord, tailWord_414010, baseEnd_414010] using wordTrace_append hprefix tailTrace_414010
  have hstable : (prefixWord ++ tailWord_414010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414010).length < 2 ^ (prefixWord ++ tailWord_414010).sum := by decide
  have hdescent : baseEnd_414010 < baseStart_414010 := by decide
  rcases family_descends (prefixWord ++ tailWord_414010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414020 : List Nat := [2, 3, 4, 1, 2, 2, 1, 1, 1, 6]
def baseStart_414020 : Nat := 118140960795 + 414020 * 2 ^ 59
def prefixEnd_414020 : Nat := 4983230072969 + 3 ^ 40 * 414020 * 2
def baseEnd_414020 : Nat := 70863753524858459515321

theorem tailTrace_414020 : CollatzResearch.WordTrace tailWord_414020 prefixEnd_414020 70863753524858459515321 := by
  unfold tailWord_414020
  simp only [CollatzResearch.WordTrace]
  refine ⟨7550274980041861915839757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10067033306722482554453009 7550274980041861915839757)
  ·
    refine ⟨2831353117515698218439909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7550274980041861915839757 2831353117515698218439909)
    ·
      refine ⟨530878709534193415957483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2831353117515698218439909 530878709534193415957483)
      ·
        refine ⟨796318064301290123936225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530878709534193415957483 796318064301290123936225)
        ·
          refine ⟨597238548225967592952169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 796318064301290123936225 597238548225967592952169)
          ·
            refine ⟨447928911169475694714127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 597238548225967592952169 447928911169475694714127)
            ·
              refine ⟨671893366754213542071191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447928911169475694714127 671893366754213542071191)
              ·
                refine ⟨1007840050131320313106787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671893366754213542071191 1007840050131320313106787)
                ·
                  refine ⟨1511760075196980469660181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1007840050131320313106787 1511760075196980469660181)
                  ·
                    refine ⟨70863753524858459515321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1511760075196980469660181 70863753524858459515321)
                    ·
                      rfl

theorem cell23_414020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_414020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414020 prefixEnd_414020 := by exact prefixLift 414020
  have htrace : WordTrace (prefixWord ++ tailWord_414020) baseStart_414020 baseEnd_414020 := by
    simpa [prefixWord, tailWord_414020, baseEnd_414020] using wordTrace_append hprefix tailTrace_414020
  have hstable : (prefixWord ++ tailWord_414020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414020).length < 2 ^ (prefixWord ++ tailWord_414020).sum := by decide
  have hdescent : baseEnd_414020 < baseStart_414020 := by decide
  rcases family_descends (prefixWord ++ tailWord_414020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414039 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 5]
def baseStart_414039 : Nat := 118140960795 + 414039 * 2 ^ 59
def prefixEnd_414039 : Nat := 4983230072969 + 3 ^ 40 * 414039 * 2
def baseEnd_414039 : Nat := 212601016707010804208375

theorem tailTrace_414039 : CollatzResearch.WordTrace tailWord_414039 prefixEnd_414039 212601016707010804208375 := by
  unfold tailWord_414039
  simp only [CollatzResearch.WordTrace]
  refine ⟨15101242947014890076621171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10067495298009926717747447 15101242947014890076621171)
  ·
    refine ⟨22651864420522335114931757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15101242947014890076621171 22651864420522335114931757)
    ·
      refine ⟨8494449157695875668099409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22651864420522335114931757 8494449157695875668099409)
      ·
        refine ⟨6370836868271906751074557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8494449157695875668099409 6370836868271906751074557)
        ·
          refine ⟨2389063825601965031652959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6370836868271906751074557 2389063825601965031652959)
          ·
            refine ⟨3583595738402947547479439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2389063825601965031652959 3583595738402947547479439)
            ·
              refine ⟨5375393607604421321219159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3583595738402947547479439 5375393607604421321219159)
              ·
                refine ⟨8063090411406631981828739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5375393607604421321219159 8063090411406631981828739)
                ·
                  refine ⟨12094635617109947972743109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8063090411406631981828739 12094635617109947972743109)
                  ·
                    refine ⟨2267744178208115244889333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12094635617109947972743109 2267744178208115244889333)
                    ·
                      refine ⟨212601016707010804208375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2267744178208115244889333 212601016707010804208375)
                      ·
                        rfl

theorem cell23_414039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_414039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414039 prefixEnd_414039 := by exact prefixLift 414039
  have htrace : WordTrace (prefixWord ++ tailWord_414039) baseStart_414039 baseEnd_414039 := by
    simpa [prefixWord, tailWord_414039, baseEnd_414039] using wordTrace_append hprefix tailTrace_414039
  have hstable : (prefixWord ++ tailWord_414039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414039).length < 2 ^ (prefixWord ++ tailWord_414039).sum := by decide
  have hdescent : baseEnd_414039 < baseStart_414039 := by decide
  rcases family_descends (prefixWord ++ tailWord_414039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414049 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 3, 5, 4]
def baseStart_414049 : Nat := 118140960795 + 414049 * 2 ^ 59
def prefixEnd_414049 : Nat := 4983230072969 + 3 ^ 40 * 414049 * 2
def baseEnd_414049 : Nat := 212606151513555765083329

theorem tailTrace_414049 : CollatzResearch.WordTrace tailWord_414049 prefixEnd_414049 212606151513555765083329 := by
  unfold tailWord_414049
  simp only [CollatzResearch.WordTrace]
  refine ⟨15101607676978661784485201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10067738451319107856323467 15101607676978661784485201)
  ·
    refine ⟨11326205757733996338363901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15101607676978661784485201 11326205757733996338363901)
    ·
      refine ⟨4247327159150248626886463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11326205757733996338363901 4247327159150248626886463)
      ·
        refine ⟨6370990738725372940329695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4247327159150248626886463 6370990738725372940329695)
        ·
          refine ⟨9556486108088059410494543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6370990738725372940329695 9556486108088059410494543)
          ·
            refine ⟨14334729162132089115741815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9556486108088059410494543 14334729162132089115741815)
            ·
              refine ⟨21502093743198133673612723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14334729162132089115741815 21502093743198133673612723)
              ·
                refine ⟨32253140614797200510419085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21502093743198133673612723 32253140614797200510419085)
                ·
                  refine ⟨12094927730548950191407157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32253140614797200510419085 12094927730548950191407157)
                  ·
                    refine ⟨1133899474738964080444421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12094927730548950191407157 1133899474738964080444421)
                    ·
                      refine ⟨212606151513555765083329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1133899474738964080444421 212606151513555765083329)
                      ·
                        rfl

theorem cell23_414049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_414049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414049 prefixEnd_414049 := by exact prefixLift 414049
  have htrace : WordTrace (prefixWord ++ tailWord_414049) baseStart_414049 baseEnd_414049 := by
    simpa [prefixWord, tailWord_414049, baseEnd_414049] using wordTrace_append hprefix tailTrace_414049
  have hstable : (prefixWord ++ tailWord_414049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414049).length < 2 ^ (prefixWord ++ tailWord_414049).sum := by decide
  have hdescent : baseEnd_414049 < baseStart_414049 := by decide
  rcases family_descends (prefixWord ++ tailWord_414049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414077 : List Nat := [1, 4, 1, 1, 2, 5, 2, 1, 2, 1, 3]
def baseStart_414077 : Nat := 118140960795 + 414077 * 2 ^ 59
def prefixEnd_414077 : Nat := 4983230072969 + 3 ^ 40 * 414077 * 2
def baseEnd_414077 : Nat := 212620528971881655533201

theorem tailTrace_414077 : CollatzResearch.WordTrace tailWord_414077 prefixEnd_414077 212620528971881655533201 := by
  unfold tailWord_414077
  simp only [CollatzResearch.WordTrace]
  refine ⟨15102628920877222566504485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10068419280584815044336323 15102628920877222566504485)
  ·
    refine ⟨2831742922664479231219591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15102628920877222566504485 2831742922664479231219591)
    ·
      refine ⟨4247614383996718846829387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2831742922664479231219591 4247614383996718846829387)
      ·
        refine ⟨6371421575995078270244081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4247614383996718846829387 6371421575995078270244081)
        ·
          refine ⟨4778566181996308702683061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6371421575995078270244081 4778566181996308702683061)
          ·
            refine ⟨447990579562153940876537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4778566181996308702683061 447990579562153940876537)
            ·
              refine ⟨335992934671615455657403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447990579562153940876537 335992934671615455657403)
              ·
                refine ⟨503989402007423183486105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335992934671615455657403 503989402007423183486105)
                ·
                  refine ⟨377992051505567387614579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503989402007423183486105 377992051505567387614579)
                  ·
                    refine ⟨566988077258351081421869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 377992051505567387614579 566988077258351081421869)
                    ·
                      refine ⟨212620528971881655533201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 566988077258351081421869 212620528971881655533201)
                      ·
                        rfl

theorem cell23_414077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 2, 1, 3].length) (baseStart_414077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414077 prefixEnd_414077 := by exact prefixLift 414077
  have htrace : WordTrace (prefixWord ++ tailWord_414077) baseStart_414077 baseEnd_414077 := by
    simpa [prefixWord, tailWord_414077, baseEnd_414077] using wordTrace_append hprefix tailTrace_414077
  have hstable : (prefixWord ++ tailWord_414077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414077).length < 2 ^ (prefixWord ++ tailWord_414077).sum := by decide
  have hdescent : baseEnd_414077 < baseStart_414077 := by decide
  rcases family_descends (prefixWord ++ tailWord_414077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414173 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_414173 : Nat := 118140960795 + 414173 * 2 ^ 59
def prefixEnd_414173 : Nat := 4983230072969 + 3 ^ 40 * 414173 * 2
def baseEnd_414173 : Nat := 212669823114713279932759

theorem tailTrace_414173 : CollatzResearch.WordTrace tailWord_414173 prefixEnd_414173 212669823114713279932759 := by
  unfold tailWord_414173
  simp only [CollatzResearch.WordTrace]
  refine ⟨15106130328529430961999173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10070753552352953974666115 15106130328529430961999173)
  ·
    refine ⟨2832399436599268305374845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15106130328529430961999173 2832399436599268305374845)
    ·
      refine ⟨1062149788724725614515567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2832399436599268305374845 1062149788724725614515567)
      ·
        refine ⟨1593224683087088421773351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1062149788724725614515567 1593224683087088421773351)
        ·
          refine ⟨2389837024630632632660027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1593224683087088421773351 2389837024630632632660027)
          ·
            refine ⟨3584755536945948948990041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2389837024630632632660027 3584755536945948948990041)
            ·
              refine ⟨2688566652709461711742531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3584755536945948948990041 2688566652709461711742531)
              ·
                refine ⟨4032849979064192567613797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2688566652709461711742531 4032849979064192567613797)
                ·
                  refine ⟨756159371074536106427587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4032849979064192567613797 756159371074536106427587)
                  ·
                    refine ⟨1134239056611804159641381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 756159371074536106427587 1134239056611804159641381)
                    ·
                      refine ⟨212669823114713279932759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1134239056611804159641381 212669823114713279932759)
                      ·
                        rfl

theorem cell23_414173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_414173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414173 prefixEnd_414173 := by exact prefixLift 414173
  have htrace : WordTrace (prefixWord ++ tailWord_414173) baseStart_414173 baseEnd_414173 := by
    simpa [prefixWord, tailWord_414173, baseEnd_414173] using wordTrace_append hprefix tailTrace_414173
  have hstable : (prefixWord ++ tailWord_414173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414173).length < 2 ^ (prefixWord ++ tailWord_414173).sum := by decide
  have hdescent : baseEnd_414173 < baseStart_414173 := by decide
  rcases family_descends (prefixWord ++ tailWord_414173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414190 : List Nat := [4, 1, 2, 1, 2, 2, 2, 1, 2, 4, 2]
def baseStart_414190 : Nat := 118140960795 + 414190 * 2 ^ 59
def prefixEnd_414190 : Nat := 4983230072969 + 3 ^ 40 * 414190 * 2
def baseEnd_414190 : Nat := 212678552285839713420181

theorem tailTrace_414190 : CollatzResearch.WordTrace tailWord_414190 prefixEnd_414190 212678552285839713420181 := by
  unfold tailWord_414190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1888343796183480358171003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10071166912978561910245349 1888343796183480358171003)
  ·
    refine ⟨2832515694275220537256505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1888343796183480358171003 2832515694275220537256505)
    ·
      refine ⟨2124386770706415402942379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2832515694275220537256505 2124386770706415402942379)
      ·
        refine ⟨3186580156059623104413569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2124386770706415402942379 3186580156059623104413569)
        ·
          refine ⟨2389935117044717328310177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3186580156059623104413569 2389935117044717328310177)
          ·
            refine ⟨1792451337783537996232633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2389935117044717328310177 1792451337783537996232633)
            ·
              refine ⟨1344338503337653497174475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1792451337783537996232633 1344338503337653497174475)
              ·
                refine ⟨2016507755006480245761713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1344338503337653497174475 2016507755006480245761713)
                ·
                  refine ⟨1512380816254860184321285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2016507755006480245761713 1512380816254860184321285)
                  ·
                    refine ⟨283571403047786284560241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1512380816254860184321285 283571403047786284560241)
                    ·
                      refine ⟨212678552285839713420181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 283571403047786284560241 212678552285839713420181)
                      ·
                        rfl

theorem cell23_414190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_414190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414190 prefixEnd_414190 := by exact prefixLift 414190
  have htrace : WordTrace (prefixWord ++ tailWord_414190) baseStart_414190 baseEnd_414190 := by
    simpa [prefixWord, tailWord_414190, baseEnd_414190] using wordTrace_append hprefix tailTrace_414190
  have hstable : (prefixWord ++ tailWord_414190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414190).length < 2 ^ (prefixWord ++ tailWord_414190).sum := by decide
  have hdescent : baseEnd_414190 < baseStart_414190 := by decide
  rcases family_descends (prefixWord ++ tailWord_414190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414223 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 7, 1, 3]
def baseStart_414223 : Nat := 118140960795 + 414223 * 2 ^ 59
def prefixEnd_414223 : Nat := 4983230072969 + 3 ^ 40 * 414223 * 2
def baseEnd_414223 : Nat := 212695497147438084307529

theorem tailTrace_414223 : CollatzResearch.WordTrace tailWord_414223 prefixEnd_414223 212695497147438084307529 := by
  unfold tailWord_414223
  simp only [CollatzResearch.WordTrace]
  refine ⟨15107953978348289501319323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10071969318898859667546215 15107953978348289501319323)
  ·
    refine ⟨22661930967522434251978985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15107953978348289501319323 22661930967522434251978985)
    ·
      refine ⟨16996448225641825688984239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22661930967522434251978985 16996448225641825688984239)
      ·
        refine ⟨25494672338462738533476359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16996448225641825688984239 25494672338462738533476359)
        ·
          refine ⟨38242008507694107800214539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25494672338462738533476359 38242008507694107800214539)
          ·
            refine ⟨57363012761541161700321809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38242008507694107800214539 57363012761541161700321809)
            ·
              refine ⟨43022259571155871275241357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57363012761541161700321809 43022259571155871275241357)
              ·
                refine ⟨16133347339183451728215509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43022259571155871275241357 16133347339183451728215509)
                ·
                  refine ⟨378125328262112149880051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16133347339183451728215509 378125328262112149880051)
                  ·
                    refine ⟨567187992393168224820077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 378125328262112149880051 567187992393168224820077)
                    ·
                      refine ⟨212695497147438084307529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 567187992393168224820077 212695497147438084307529)
                      ·
                        rfl

theorem cell23_414223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 1, 3].length) (baseStart_414223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414223 prefixEnd_414223 := by exact prefixLift 414223
  have htrace : WordTrace (prefixWord ++ tailWord_414223) baseStart_414223 baseEnd_414223 := by
    simpa [prefixWord, tailWord_414223, baseEnd_414223] using wordTrace_append hprefix tailTrace_414223
  have hstable : (prefixWord ++ tailWord_414223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414223).length < 2 ^ (prefixWord ++ tailWord_414223).sum := by decide
  have hdescent : baseEnd_414223 < baseStart_414223 := by decide
  rcases family_descends (prefixWord ++ tailWord_414223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414247 : List Nat := [1, 1, 7, 2, 1, 1, 1, 3, 6]
def baseStart_414247 : Nat := 118140960795 + 414247 * 2 ^ 59
def prefixEnd_414247 : Nat := 4983230072969 + 3 ^ 40 * 414247 * 2
def baseEnd_414247 : Nat := 23634202298127332267491

theorem tailTrace_414247 : CollatzResearch.WordTrace tailWord_414247 prefixEnd_414247 23634202298127332267491 := by
  unfold tailWord_414247
  simp only [CollatzResearch.WordTrace]
  refine ⟨15108829330261341600192995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10072552886840894400128663 15108829330261341600192995)
  ·
    refine ⟨22663243995392012400289493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15108829330261341600192995 22663243995392012400289493)
    ·
      refine ⟨531169781142000290631785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 22663243995392012400289493 531169781142000290631785)
      ·
        refine ⟨398377335856500217973839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 531169781142000290631785 398377335856500217973839)
        ·
          refine ⟨597566003784750326960759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398377335856500217973839 597566003784750326960759)
          ·
            refine ⟨896349005677125490441139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597566003784750326960759 896349005677125490441139)
            ·
              refine ⟨1344523508515688235661709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 896349005677125490441139 1344523508515688235661709)
              ·
                refine ⟨504196315693383088373141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1344523508515688235661709 504196315693383088373141)
                ·
                  refine ⟨23634202298127332267491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 504196315693383088373141 23634202298127332267491)
                  ·
                    rfl

theorem cell23_414247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 6].length) (baseStart_414247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414247 prefixEnd_414247 := by exact prefixLift 414247
  have htrace : WordTrace (prefixWord ++ tailWord_414247) baseStart_414247 baseEnd_414247 := by
    simpa [prefixWord, tailWord_414247, baseEnd_414247] using wordTrace_append hprefix tailTrace_414247
  have hstable : (prefixWord ++ tailWord_414247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414247).length < 2 ^ (prefixWord ++ tailWord_414247).sum := by decide
  have hdescent : baseEnd_414247 < baseStart_414247 := by decide
  rcases family_descends (prefixWord ++ tailWord_414247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414263 : List Nat := [1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 4]
def baseStart_414263 : Nat := 118140960795 + 414263 * 2 ^ 59
def prefixEnd_414263 : Nat := 4983230072969 + 3 ^ 40 * 414263 * 2
def baseEnd_414263 : Nat := 212716036373617927807345

theorem tailTrace_414263 : CollatzResearch.WordTrace tailWord_414263 prefixEnd_414263 212716036373617927807345 := by
  unfold tailWord_414263
  simp only [CollatzResearch.WordTrace]
  refine ⟨15109412898203376332775443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10072941932135584221850295 15109412898203376332775443)
  ·
    refine ⟨22664119347305064499163165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15109412898203376332775443 22664119347305064499163165)
    ·
      refine ⟨8499044755239399187186187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22664119347305064499163165 8499044755239399187186187)
      ·
        refine ⟨12748567132859098780779281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8499044755239399187186187 12748567132859098780779281)
        ·
          refine ⟨9561425349644324085584461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12748567132859098780779281 9561425349644324085584461)
          ·
            refine ⟨3585534506116621532094173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9561425349644324085584461 3585534506116621532094173)
            ·
              refine ⟨1344575439793733074535315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3585534506116621532094173 1344575439793733074535315)
              ·
                refine ⟨2016863159690599611802973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1344575439793733074535315 2016863159690599611802973)
                ·
                  refine ⟨756323684883974854426115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2016863159690599611802973 756323684883974854426115)
                  ·
                    refine ⟨1134485527325962281639173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 756323684883974854426115 1134485527325962281639173)
                    ·
                      refine ⟨212716036373617927807345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1134485527325962281639173 212716036373617927807345)
                      ·
                        rfl

theorem cell23_414263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_414263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414263 prefixEnd_414263 := by exact prefixLift 414263
  have htrace : WordTrace (prefixWord ++ tailWord_414263) baseStart_414263 baseEnd_414263 := by
    simpa [prefixWord, tailWord_414263, baseEnd_414263] using wordTrace_append hprefix tailTrace_414263
  have hstable : (prefixWord ++ tailWord_414263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414263).length < 2 ^ (prefixWord ++ tailWord_414263).sum := by decide
  have hdescent : baseEnd_414263 < baseStart_414263 := by decide
  rcases family_descends (prefixWord ++ tailWord_414263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414273 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 3, 6]
def baseStart_414273 : Nat := 118140960795 + 414273 * 2 ^ 59
def prefixEnd_414273 : Nat := 4983230072969 + 3 ^ 40 * 414273 * 2
def baseEnd_414273 : Nat := 70907057060054296227433

theorem tailTrace_414273 : CollatzResearch.WordTrace tailWord_414273 prefixEnd_414273 70907057060054296227433 := by
  unfold tailWord_414273
  simp only [CollatzResearch.WordTrace]
  refine ⟨15109777628167148040639473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10073185085444765360426315 15109777628167148040639473)
  ·
    refine ⟨11332333221125361030479605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15109777628167148040639473 11332333221125361030479605)
    ·
      refine ⟨1062406239480502596607463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11332333221125361030479605 1062406239480502596607463)
      ·
        refine ⟨1593609359220753894911195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1062406239480502596607463 1593609359220753894911195)
        ·
          refine ⟨2390414038831130842366793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1593609359220753894911195 2390414038831130842366793)
          ·
            refine ⟨1792810529123348131775095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2390414038831130842366793 1792810529123348131775095)
            ·
              refine ⟨2689215793685022197662643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1792810529123348131775095 2689215793685022197662643)
              ·
                refine ⟨4033823690527533296493965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2689215793685022197662643 4033823690527533296493965)
                ·
                  refine ⟨1512683883947824986185237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4033823690527533296493965 1512683883947824986185237)
                  ·
                    refine ⟨70907057060054296227433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1512683883947824986185237 70907057060054296227433)
                    ·
                      rfl

theorem cell23_414273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_414273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414273 prefixEnd_414273 := by exact prefixLift 414273
  have htrace : WordTrace (prefixWord ++ tailWord_414273) baseStart_414273 baseEnd_414273 := by
    simpa [prefixWord, tailWord_414273, baseEnd_414273] using wordTrace_append hprefix tailTrace_414273
  have hstable : (prefixWord ++ tailWord_414273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414273).length < 2 ^ (prefixWord ++ tailWord_414273).sum := by decide
  have hdescent : baseEnd_414273 < baseStart_414273 := by decide
  rcases family_descends (prefixWord ++ tailWord_414273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414283 : List Nat := [1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 5]
def baseStart_414283 : Nat := 118140960795 + 414283 * 2 ^ 59
def prefixEnd_414283 : Nat := 4983230072969 + 3 ^ 40 * 414283 * 2
def baseEnd_414283 : Nat := 212726305986707849557253

theorem tailTrace_414283 : CollatzResearch.WordTrace tailWord_414283 prefixEnd_414283 212726305986707849557253 := by
  unfold tailWord_414283
  simp only [CollatzResearch.WordTrace]
  refine ⟨15110142358130919748503503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10073428238753946499002335 15110142358130919748503503)
  ·
    refine ⟨22665213537196379622755255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15110142358130919748503503 22665213537196379622755255)
    ·
      refine ⟨33997820305794569434132883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22665213537196379622755255 33997820305794569434132883)
      ·
        refine ⟨50996730458691854151199325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33997820305794569434132883 50996730458691854151199325)
        ·
          refine ⟨19123773922009445306699747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50996730458691854151199325 19123773922009445306699747)
          ·
            refine ⟨28685660883014167960049621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19123773922009445306699747 28685660883014167960049621)
            ·
              refine ⟨672320176945644561563663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 28685660883014167960049621 672320176945644561563663)
              ·
                refine ⟨1008480265418466842345495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672320176945644561563663 1008480265418466842345495)
                ·
                  refine ⟨1512720398127700263518243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1008480265418466842345495 1512720398127700263518243)
                  ·
                    refine ⟨2269080597191550395277365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1512720398127700263518243 2269080597191550395277365)
                    ·
                      refine ⟨212726305986707849557253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2269080597191550395277365 212726305986707849557253)
                      ·
                        rfl

theorem cell23_414283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 5].length) (baseStart_414283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414283 prefixEnd_414283 := by exact prefixLift 414283
  have htrace : WordTrace (prefixWord ++ tailWord_414283) baseStart_414283 baseEnd_414283 := by
    simpa [prefixWord, tailWord_414283, baseEnd_414283] using wordTrace_append hprefix tailTrace_414283
  have hstable : (prefixWord ++ tailWord_414283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414283).length < 2 ^ (prefixWord ++ tailWord_414283).sum := by decide
  have hdescent : baseEnd_414283 < baseStart_414283 := by decide
  rcases family_descends (prefixWord ++ tailWord_414283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414320 : List Nat := [2, 1, 1, 1, 7, 1, 3, 7]
def baseStart_414320 : Nat := 118140960795 + 414320 * 2 ^ 59
def prefixEnd_414320 : Nat := 4983230072969 + 3 ^ 40 * 414320 * 2
def baseEnd_414320 : Nat := 7879455732256452029429

theorem tailTrace_414320 : CollatzResearch.WordTrace tailWord_414320 prefixEnd_414320 7879455732256452029429 := by
  unfold tailWord_414320
  simp only [CollatzResearch.WordTrace]
  refine ⟨7555745929498437533800207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10074327905997916711733609 7555745929498437533800207)
  ·
    refine ⟨11333618894247656300700311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7555745929498437533800207 11333618894247656300700311)
    ·
      refine ⟨17000428341371484451050467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11333618894247656300700311 17000428341371484451050467)
      ·
        refine ⟨25500642512057226676575701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17000428341371484451050467 25500642512057226676575701)
        ·
          refine ⟨597671308876341250232243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 25500642512057226676575701 597671308876341250232243)
          ·
            refine ⟨896506963314511875348365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597671308876341250232243 896506963314511875348365)
            ·
              refine ⟨336190111242941953255637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 896506963314511875348365 336190111242941953255637)
              ·
                refine ⟨7879455732256452029429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 336190111242941953255637 7879455732256452029429)
                ·
                  rfl

theorem cell23_414320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 7].length) (baseStart_414320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414320 prefixEnd_414320 := by exact prefixLift 414320
  have htrace : WordTrace (prefixWord ++ tailWord_414320) baseStart_414320 baseEnd_414320 := by
    simpa [prefixWord, tailWord_414320, baseEnd_414320] using wordTrace_append hprefix tailTrace_414320
  have hstable : (prefixWord ++ tailWord_414320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414320).length < 2 ^ (prefixWord ++ tailWord_414320).sum := by decide
  have hdescent : baseEnd_414320 < baseStart_414320 := by decide
  rcases family_descends (prefixWord ++ tailWord_414320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414373 : List Nat := [1, 3, 1, 2, 1, 2, 1, 4, 2, 1, 5]
def baseStart_414373 : Nat := 118140960795 + 414373 * 2 ^ 59
def prefixEnd_414373 : Nat := 4983230072969 + 3 ^ 40 * 414373 * 2
def baseEnd_414373 : Nat := 212772519245612497431839

theorem tailTrace_414373 : CollatzResearch.WordTrace tailWord_414373 prefixEnd_414373 212772519245612497431839 := by
  unfold tailWord_414373
  simp only [CollatzResearch.WordTrace]
  refine ⟨15113424927804865119279773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10075616618536576746186515 15113424927804865119279773)
  ·
    refine ⟨5667534347926824419729915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15113424927804865119279773 5667534347926824419729915)
    ·
      refine ⟨8501301521890236629594873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5667534347926824419729915 8501301521890236629594873)
      ·
        refine ⟨6375976141417677472196155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8501301521890236629594873 6375976141417677472196155)
        ·
          refine ⟨9563964212126516208294233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6375976141417677472196155 9563964212126516208294233)
          ·
            refine ⟨7172973159094887156220675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9563964212126516208294233 7172973159094887156220675)
            ·
              refine ⟨10759459738642330734331013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7172973159094887156220675 10759459738642330734331013)
              ·
                refine ⟨2017398700995437012687065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10759459738642330734331013 2017398700995437012687065)
                ·
                  refine ⟨1513049025746577759515299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2017398700995437012687065 1513049025746577759515299)
                  ·
                    refine ⟨2269573538619866639272949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1513049025746577759515299 2269573538619866639272949)
                    ·
                      refine ⟨212772519245612497431839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2269573538619866639272949 212772519245612497431839)
                      ·
                        rfl

theorem cell23_414373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_414373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414373 prefixEnd_414373 := by exact prefixLift 414373
  have htrace : WordTrace (prefixWord ++ tailWord_414373) baseStart_414373 baseEnd_414373 := by
    simpa [prefixWord, tailWord_414373, baseEnd_414373] using wordTrace_append hprefix tailTrace_414373
  have hstable : (prefixWord ++ tailWord_414373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414373).length < 2 ^ (prefixWord ++ tailWord_414373).sum := by decide
  have hdescent : baseEnd_414373 < baseStart_414373 := by decide
  rcases family_descends (prefixWord ++ tailWord_414373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414387 : List Nat := [1, 1, 1, 2, 3, 4, 1, 2, 4, 2, 2]
def baseStart_414387 : Nat := 118140960795 + 414387 * 2 ^ 59
def prefixEnd_414387 : Nat := 4983230072969 + 3 ^ 40 * 414387 * 2
def baseEnd_414387 : Nat := 212779707974775442656775

theorem tailTrace_414387 : CollatzResearch.WordTrace tailWord_414387 prefixEnd_414387 212779707974775442656775 := by
  unfold tailWord_414387
  simp only [CollatzResearch.WordTrace]
  refine ⟨15113935549754145510289415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10075957033169430340192943 15113935549754145510289415)
  ·
    refine ⟨22670903324631218265434123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15113935549754145510289415 22670903324631218265434123)
    ·
      refine ⟨34006354986946827398151185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22670903324631218265434123 34006354986946827398151185)
      ·
        refine ⟨25504766240210120548613389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34006354986946827398151185 25504766240210120548613389)
        ·
          refine ⟨9564287340078795205730021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25504766240210120548613389 9564287340078795205730021)
          ·
            refine ⟨1793303876264774101074379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9564287340078795205730021 1793303876264774101074379)
            ·
              refine ⟨2689955814397161151611569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1793303876264774101074379 2689955814397161151611569)
              ·
                refine ⟨2017466860797870863708677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2689955814397161151611569 2017466860797870863708677)
                ·
                  refine ⟨378275036399600786945377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2017466860797870863708677 378275036399600786945377)
                  ·
                    refine ⟨283706277299700590209033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 378275036399600786945377 283706277299700590209033)
                    ·
                      refine ⟨212779707974775442656775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 283706277299700590209033 212779707974775442656775)
                      ·
                        rfl

theorem cell23_414387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 2, 2].length) (baseStart_414387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414387 prefixEnd_414387 := by exact prefixLift 414387
  have htrace : WordTrace (prefixWord ++ tailWord_414387) baseStart_414387 baseEnd_414387 := by
    simpa [prefixWord, tailWord_414387, baseEnd_414387] using wordTrace_append hprefix tailTrace_414387
  have hstable : (prefixWord ++ tailWord_414387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414387).length < 2 ^ (prefixWord ++ tailWord_414387).sum := by decide
  have hdescent : baseEnd_414387 < baseStart_414387 := by decide
  rcases family_descends (prefixWord ++ tailWord_414387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414404 : List Nat := [2, 3, 3, 1, 1, 2, 2, 1, 4, 2, 2]
def baseStart_414404 : Nat := 118140960795 + 414404 * 2 ^ 59
def prefixEnd_414404 : Nat := 4983230072969 + 3 ^ 40 * 414404 * 2
def baseEnd_414404 : Nat := 212788437145901876144197

theorem tailTrace_414404 : CollatzResearch.WordTrace tailWord_414404 prefixEnd_414404 212788437145901876144197 := by
  unfold tailWord_414404
  simp only [CollatzResearch.WordTrace]
  refine ⟨7557277795346278706829133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10076370393795038275772177 7557277795346278706829133)
  ·
    refine ⟨2833979173254854515060925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7557277795346278706829133 2833979173254854515060925)
    ·
      refine ⟨1062742189970570443147847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2833979173254854515060925 1062742189970570443147847)
      ·
        refine ⟨1594113284955855664721771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1062742189970570443147847 1594113284955855664721771)
        ·
          refine ⟨2391169927433783497082657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1594113284955855664721771 2391169927433783497082657)
          ·
            refine ⟨1793377445575337622811993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2391169927433783497082657 1793377445575337622811993)
            ·
              refine ⟨1345033084181503217108995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1793377445575337622811993 1345033084181503217108995)
              ·
                refine ⟨2017549626272254825663493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1345033084181503217108995 2017549626272254825663493)
                ·
                  refine ⟨378290554926047779811905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2017549626272254825663493 378290554926047779811905)
                  ·
                    refine ⟨283717916194535834858929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 378290554926047779811905 283717916194535834858929)
                    ·
                      refine ⟨212788437145901876144197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 283717916194535834858929 212788437145901876144197)
                      ·
                        rfl

theorem cell23_414404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_414404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414404 prefixEnd_414404 := by exact prefixLift 414404
  have htrace : WordTrace (prefixWord ++ tailWord_414404) baseStart_414404 baseEnd_414404 := by
    simpa [prefixWord, tailWord_414404, baseEnd_414404] using wordTrace_append hprefix tailTrace_414404
  have hstable : (prefixWord ++ tailWord_414404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414404).length < 2 ^ (prefixWord ++ tailWord_414404).sum := by decide
  have hdescent : baseEnd_414404 < baseStart_414404 := by decide
  rcases family_descends (prefixWord ++ tailWord_414404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414410 : List Nat := [3, 1, 2, 1, 4, 1, 3, 1, 7]
def baseStart_414410 : Nat := 118140960795 + 414410 * 2 ^ 59
def prefixEnd_414410 : Nat := 4983230072969 + 3 ^ 40 * 414410 * 2
def baseEnd_414410 : Nat := 23643502003314316963241

theorem tailTrace_414410 : CollatzResearch.WordTrace tailWord_414410 prefixEnd_414410 23643502003314316963241 := by
  unfold tailWord_414410
  simp only [CollatzResearch.WordTrace]
  refine ⟨3778693607167705109594171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10076516285780546958917789 3778693607167705109594171)
  ·
    refine ⟨5668040410751557664391257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3778693607167705109594171 5668040410751557664391257)
    ·
      refine ⟨4251030308063668248293443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5668040410751557664391257 4251030308063668248293443)
      ·
        refine ⟨6376545462095502372440165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4251030308063668248293443 6376545462095502372440165)
        ·
          refine ⟨1195602274142906694832531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6376545462095502372440165 1195602274142906694832531)
          ·
            refine ⟨1793403411214360042248797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1195602274142906694832531 1793403411214360042248797)
            ·
              refine ⟨672526279205385015843299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1793403411214360042248797 672526279205385015843299)
              ·
                refine ⟨1008789418808077523764949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672526279205385015843299 1008789418808077523764949)
                ·
                  refine ⟨23643502003314316963241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1008789418808077523764949 23643502003314316963241)
                  ·
                    rfl

theorem cell23_414410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 7].length) (baseStart_414410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414410 prefixEnd_414410 := by exact prefixLift 414410
  have htrace : WordTrace (prefixWord ++ tailWord_414410) baseStart_414410 baseEnd_414410 := by
    simpa [prefixWord, tailWord_414410, baseEnd_414410] using wordTrace_append hprefix tailTrace_414410
  have hstable : (prefixWord ++ tailWord_414410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414410).length < 2 ^ (prefixWord ++ tailWord_414410).sum := by decide
  have hdescent : baseEnd_414410 < baseStart_414410 := by decide
  rcases family_descends (prefixWord ++ tailWord_414410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414450 : List Nat := [3, 2, 1, 3, 1, 2, 1, 2, 1, 2, 5]
def baseStart_414450 : Nat := 118140960795 + 414450 * 2 ^ 59
def prefixEnd_414450 : Nat := 4983230072969 + 3 ^ 40 * 414450 * 2
def baseEnd_414450 : Nat := 212812057256008696168985

theorem tailTrace_414450 : CollatzResearch.WordTrace tailWord_414450 prefixEnd_414450 212812057256008696168985 := by
  unfold tailWord_414450
  simp only [CollatzResearch.WordTrace]
  refine ⟨3779058337131476817458201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10077488899017271513221869 3779058337131476817458201)
  ·
    refine ⟨2834293752848607613093651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3779058337131476817458201 2834293752848607613093651)
    ·
      refine ⟨4251440629272911419640477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2834293752848607613093651 4251440629272911419640477)
      ·
        refine ⟨1594290235977341782365179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4251440629272911419640477 1594290235977341782365179)
        ·
          refine ⟨2391435353966012673547769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1594290235977341782365179 2391435353966012673547769)
          ·
            refine ⟨1793576515474509505160827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2391435353966012673547769 1793576515474509505160827)
            ·
              refine ⟨2690364773211764257741241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1793576515474509505160827 2690364773211764257741241)
              ·
                refine ⟨2017773579908823193305931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2690364773211764257741241 2017773579908823193305931)
                ·
                  refine ⟨3026660369863234789958897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2017773579908823193305931 3026660369863234789958897)
                  ·
                    refine ⟨2269995277397426092469173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3026660369863234789958897 2269995277397426092469173)
                    ·
                      refine ⟨212812057256008696168985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2269995277397426092469173 212812057256008696168985)
                      ·
                        rfl

theorem cell23_414450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_414450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414450 prefixEnd_414450 := by exact prefixLift 414450
  have htrace : WordTrace (prefixWord ++ tailWord_414450) baseStart_414450 baseEnd_414450 := by
    simpa [prefixWord, tailWord_414450, baseEnd_414450] using wordTrace_append hprefix tailTrace_414450
  have hstable : (prefixWord ++ tailWord_414450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414450).length < 2 ^ (prefixWord ++ tailWord_414450).sum := by decide
  have hdescent : baseEnd_414450 < baseStart_414450 := by decide
  rcases family_descends (prefixWord ++ tailWord_414450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414463 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 5]
def baseStart_414463 : Nat := 118140960795 + 414463 * 2 ^ 59
def prefixEnd_414463 : Nat := 4983230072969 + 3 ^ 40 * 414463 * 2
def baseEnd_414463 : Nat := 212818732504517145306425

theorem tailTrace_414463 : CollatzResearch.WordTrace tailWord_414463 prefixEnd_414463 212818732504517145306425 := by
  unfold tailWord_414463
  simp only [CollatzResearch.WordTrace]
  refine ⟨15116707497478810490056043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10077804998319206993370695 15116707497478810490056043)
  ·
    refine ⟨22675061246218215735084065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15116707497478810490056043 22675061246218215735084065)
    ·
      refine ⟨17006295934663661801313049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22675061246218215735084065 17006295934663661801313049)
      ·
        refine ⟨12754721950997746350984787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17006295934663661801313049 12754721950997746350984787)
        ·
          refine ⟨19132082926496619526477181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12754721950997746350984787 19132082926496619526477181)
          ·
            refine ⟨7174531097436232322428943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19132082926496619526477181 7174531097436232322428943)
            ·
              refine ⟨10761796646154348483643415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7174531097436232322428943 10761796646154348483643415)
              ·
                refine ⟨16142694969231522725465123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10761796646154348483643415 16142694969231522725465123)
                ·
                  refine ⟨24214042453847284088197685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16142694969231522725465123 24214042453847284088197685)
                  ·
                    refine ⟨2270066480048182883268533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24214042453847284088197685 2270066480048182883268533)
                    ·
                      refine ⟨212818732504517145306425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2270066480048182883268533 212818732504517145306425)
                      ·
                        rfl

theorem cell23_414463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_414463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414463 prefixEnd_414463 := by exact prefixLift 414463
  have htrace : WordTrace (prefixWord ++ tailWord_414463) baseStart_414463 baseEnd_414463 := by
    simpa [prefixWord, tailWord_414463, baseEnd_414463] using wordTrace_append hprefix tailTrace_414463
  have hstable : (prefixWord ++ tailWord_414463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414463).length < 2 ^ (prefixWord ++ tailWord_414463).sum := by decide
  have hdescent : baseEnd_414463 < baseStart_414463 := by decide
  rcases family_descends (prefixWord ++ tailWord_414463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414517 : List Nat := [1, 3, 3, 1, 3, 1, 3, 2, 6]
def baseStart_414517 : Nat := 118140960795 + 414517 * 2 ^ 59
def prefixEnd_414517 : Nat := 4983230072969 + 3 ^ 40 * 414517 * 2
def baseEnd_414517 : Nat := 23649606717762214892353

theorem tailTrace_414517 : CollatzResearch.WordTrace tailWord_414517 prefixEnd_414517 23649606717762214892353 := by
  unfold tailWord_414517
  simp only [CollatzResearch.WordTrace]
  refine ⟨15118677039283177712521805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10079118026188785141681203 15118677039283177712521805)
  ·
    refine ⟨5669503889731191642195677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15118677039283177712521805 5669503889731191642195677)
    ·
      refine ⟨2126063958649196865823379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5669503889731191642195677 2126063958649196865823379)
      ·
        refine ⟨3189095937973795298735069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2126063958649196865823379 3189095937973795298735069)
        ·
          refine ⟨1195910976740173237025651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3189095937973795298735069 1195910976740173237025651)
          ·
            refine ⟨1793866465110259855538477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1195910976740173237025651 1793866465110259855538477)
            ·
              refine ⟨672699924416347445826929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1793866465110259855538477 672699924416347445826929)
              ·
                refine ⟨504524943312260584370197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 672699924416347445826929 504524943312260584370197)
                ·
                  refine ⟨23649606717762214892353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 504524943312260584370197 23649606717762214892353)
                  ·
                    rfl

theorem cell23_414517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 6].length) (baseStart_414517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414517 prefixEnd_414517 := by exact prefixLift 414517
  have htrace : WordTrace (prefixWord ++ tailWord_414517) baseStart_414517 baseEnd_414517 := by
    simpa [prefixWord, tailWord_414517, baseEnd_414517] using wordTrace_append hprefix tailTrace_414517
  have hstable : (prefixWord ++ tailWord_414517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414517).length < 2 ^ (prefixWord ++ tailWord_414517).sum := by decide
  have hdescent : baseEnd_414517 < baseStart_414517 := by decide
  rcases family_descends (prefixWord ++ tailWord_414517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414537 : List Nat := [1, 2, 1, 1, 2, 5, 1, 2, 1, 5, 2]
def baseStart_414537 : Nat := 118140960795 + 414537 * 2 ^ 59
def prefixEnd_414537 : Nat := 4983230072969 + 3 ^ 40 * 414537 * 2
def baseEnd_414537 : Nat := 212856730072949855781085

theorem tailTrace_414537 : CollatzResearch.WordTrace tailWord_414537 prefixEnd_414537 212856730072949855781085 := by
  unfold tailWord_414537
  simp only [CollatzResearch.WordTrace]
  refine ⟨15119406499210721128249865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10079604332807147418833243 15119406499210721128249865)
  ·
    refine ⟨11339554874408040846187399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15119406499210721128249865 11339554874408040846187399)
    ·
      refine ⟨17009332311612061269281099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11339554874408040846187399 17009332311612061269281099)
      ·
        refine ⟨25513998467418091903921649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17009332311612061269281099 25513998467418091903921649)
        ·
          refine ⟨19135498850563568927941237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25513998467418091903921649 19135498850563568927941237)
          ·
            refine ⟨1793953017240334586994491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19135498850563568927941237 1793953017240334586994491)
            ·
              refine ⟨2690929525860501880491737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1793953017240334586994491 2690929525860501880491737)
              ·
                refine ⟨2018197144395376410368803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2690929525860501880491737 2018197144395376410368803)
                ·
                  refine ⟨3027295716593064615553205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2018197144395376410368803 3027295716593064615553205)
                  ·
                    refine ⟨283808973430599807708113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3027295716593064615553205 283808973430599807708113)
                    ·
                      refine ⟨212856730072949855781085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 283808973430599807708113 212856730072949855781085)
                      ·
                        rfl

theorem cell23_414537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 5, 2].length) (baseStart_414537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414537 prefixEnd_414537 := by exact prefixLift 414537
  have htrace : WordTrace (prefixWord ++ tailWord_414537) baseStart_414537 baseEnd_414537 := by
    simpa [prefixWord, tailWord_414537, baseEnd_414537] using wordTrace_append hprefix tailTrace_414537
  have hstable : (prefixWord ++ tailWord_414537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414537).length < 2 ^ (prefixWord ++ tailWord_414537).sum := by decide
  have hdescent : baseEnd_414537 < baseStart_414537 := by decide
  rcases family_descends (prefixWord ++ tailWord_414537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414560 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 3, 6]
def baseStart_414560 : Nat := 118140960795 + 414560 * 2 ^ 59
def prefixEnd_414560 : Nat := 4983230072969 + 3 ^ 40 * 414560 * 2
def baseEnd_414560 : Nat := 70956180042667755264493

theorem tailTrace_414560 : CollatzResearch.WordTrace tailWord_414560 prefixEnd_414560 70956180042667755264493 := by
  unfold tailWord_414560
  simp only [CollatzResearch.WordTrace]
  refine ⟨7560122689063698028168567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10080163585418264037558089 7560122689063698028168567)
  ·
    refine ⟨11340184033595547042252851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7560122689063698028168567 11340184033595547042252851)
    ·
      refine ⟨17010276050393320563379277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11340184033595547042252851 17010276050393320563379277)
      ·
        refine ⟨6378853518897495211267229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17010276050393320563379277 6378853518897495211267229)
        ·
          refine ⟨2392070069586560704225211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6378853518897495211267229 2392070069586560704225211)
          ·
            refine ⟨3588105104379841056337817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2392070069586560704225211 3588105104379841056337817)
            ·
              refine ⟨2691078828284880792253363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3588105104379841056337817 2691078828284880792253363)
              ·
                refine ⟨4036618242427321188380045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2691078828284880792253363 4036618242427321188380045)
                ·
                  refine ⟨1513731840910245445642517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4036618242427321188380045 1513731840910245445642517)
                  ·
                    refine ⟨70956180042667755264493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1513731840910245445642517 70956180042667755264493)
                    ·
                      rfl

theorem cell23_414560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 3, 6].length) (baseStart_414560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414560 prefixEnd_414560 := by exact prefixLift 414560
  have htrace : WordTrace (prefixWord ++ tailWord_414560) baseStart_414560 baseEnd_414560 := by
    simpa [prefixWord, tailWord_414560, baseEnd_414560] using wordTrace_append hprefix tailTrace_414560
  have hstable : (prefixWord ++ tailWord_414560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414560).length < 2 ^ (prefixWord ++ tailWord_414560).sum := by decide
  have hdescent : baseEnd_414560 < baseStart_414560 := by decide
  rcases family_descends (prefixWord ++ tailWord_414560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414577 : List Nat := [1, 2, 2, 2, 1, 4, 2, 1, 4, 4]
def baseStart_414577 : Nat := 118140960795 + 414577 * 2 ^ 59
def prefixEnd_414577 : Nat := 4983230072969 + 3 ^ 40 * 414577 * 2
def baseEnd_414577 : Nat := 70959089766376566426967

theorem tailTrace_414577 : CollatzResearch.WordTrace tailWord_414577 prefixEnd_414577 70959089766376566426967 := by
  unfold tailWord_414577
  simp only [CollatzResearch.WordTrace]
  refine ⟨15120865419065807959705985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10080576946043871973137323 15120865419065807959705985)
  ·
    refine ⟨11340649064299355969779489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15120865419065807959705985 11340649064299355969779489)
    ·
      refine ⟨8505486798224516977334617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11340649064299355969779489 8505486798224516977334617)
      ·
        refine ⟨6379115098668387733000963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8505486798224516977334617 6379115098668387733000963)
        ·
          refine ⟨9568672648002581599501445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6379115098668387733000963 9568672648002581599501445)
          ·
            refine ⟨1794126121500484049906521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9568672648002581599501445 1794126121500484049906521)
            ·
              refine ⟨1345594591125363037429891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1794126121500484049906521 1345594591125363037429891)
              ·
                refine ⟨2018391886688044556144837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1345594591125363037429891 2018391886688044556144837)
                ·
                  refine ⟨378448478754008354277157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2018391886688044556144837 378448478754008354277157)
                  ·
                    refine ⟨70959089766376566426967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 378448478754008354277157 70959089766376566426967)
                    ·
                      rfl

theorem cell23_414577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 4].length) (baseStart_414577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414577 prefixEnd_414577 := by exact prefixLift 414577
  have htrace : WordTrace (prefixWord ++ tailWord_414577) baseStart_414577 baseEnd_414577 := by
    simpa [prefixWord, tailWord_414577, baseEnd_414577] using wordTrace_append hprefix tailTrace_414577
  have hstable : (prefixWord ++ tailWord_414577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414577).length < 2 ^ (prefixWord ++ tailWord_414577).sum := by decide
  have hdescent : baseEnd_414577 < baseStart_414577 := by decide
  rcases family_descends (prefixWord ++ tailWord_414577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414584 : List Nat := [2, 1, 2, 1, 1, 1, 1, 7, 3, 2, 2]
def baseStart_414584 : Nat := 118140960795 + 414584 * 2 ^ 59
def prefixEnd_414584 : Nat := 4983230072969 + 3 ^ 40 * 414584 * 2
def baseEnd_414584 : Nat := 212880863663711171893369

theorem tailTrace_414584 : CollatzResearch.WordTrace tailWord_414584 prefixEnd_414584 212880863663711171893369 := by
  unfold tailWord_414584
  simp only [CollatzResearch.WordTrace]
  refine ⟨7560560365020224077605403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10080747153360298770140537 7560560365020224077605403)
  ·
    refine ⟨11340840547530336116408105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7560560365020224077605403 11340840547530336116408105)
    ·
      refine ⟨8505630410647752087306079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11340840547530336116408105 8505630410647752087306079)
      ·
        refine ⟨12758445615971628130959119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8505630410647752087306079 12758445615971628130959119)
        ·
          refine ⟨19137668423957442196438679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12758445615971628130959119 19137668423957442196438679)
          ·
            refine ⟨28706502635936163294658019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19137668423957442196438679 28706502635936163294658019)
            ·
              refine ⟨43059753953904244941987029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28706502635936163294658019 43059753953904244941987029)
              ·
                refine ⟨1009212983294630740827821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 43059753953904244941987029 1009212983294630740827821)
                ·
                  refine ⟨378454868735486527810433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1009212983294630740827821 378454868735486527810433)
                  ·
                    refine ⟨283841151551614895857825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 378454868735486527810433 283841151551614895857825)
                    ·
                      refine ⟨212880863663711171893369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 283841151551614895857825 212880863663711171893369)
                      ·
                        rfl

theorem cell23_414584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 3, 2, 2].length) (baseStart_414584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414584 prefixEnd_414584 := by exact prefixLift 414584
  have htrace : WordTrace (prefixWord ++ tailWord_414584) baseStart_414584 baseEnd_414584 := by
    simpa [prefixWord, tailWord_414584, baseEnd_414584] using wordTrace_append hprefix tailTrace_414584
  have hstable : (prefixWord ++ tailWord_414584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414584).length < 2 ^ (prefixWord ++ tailWord_414584).sum := by decide
  have hdescent : baseEnd_414584 < baseStart_414584 := by decide
  rcases family_descends (prefixWord ++ tailWord_414584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414604 : List Nat := [2, 2, 1, 2, 1, 2, 5, 2, 1, 2, 3]
def baseStart_414604 : Nat := 118140960795 + 414604 * 2 ^ 59
def prefixEnd_414604 : Nat := 4983230072969 + 3 ^ 40 * 414604 * 2
def baseEnd_414604 : Nat := 212891133276801093643277

theorem tailTrace_414604 : CollatzResearch.WordTrace tailWord_414604 prefixEnd_414604 212891133276801093643277 := by
  unfold tailWord_414604
  simp only [CollatzResearch.WordTrace]
  refine ⟨7560925094983995785469433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10081233459978661047292577 7560925094983995785469433)
  ·
    refine ⟨5670693821237996839102075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7560925094983995785469433 5670693821237996839102075)
    ·
      refine ⟨8506040731856995258653113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5670693821237996839102075 8506040731856995258653113)
      ·
        refine ⟨6379530548892746443989835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8506040731856995258653113 6379530548892746443989835)
        ·
          refine ⟨9569295823339119665984753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6379530548892746443989835 9569295823339119665984753)
          ·
            refine ⟨7176971867504339749488565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9569295823339119665984753 7176971867504339749488565)
            ·
              refine ⟨672841112578531851514553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7176971867504339749488565 672841112578531851514553)
              ·
                refine ⟨504630834433898888635915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 672841112578531851514553 504630834433898888635915)
                ·
                  refine ⟨756946251650848332953873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 504630834433898888635915 756946251650848332953873)
                  ·
                    refine ⟨567709688738136249715405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 756946251650848332953873 567709688738136249715405)
                    ·
                      refine ⟨212891133276801093643277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 567709688738136249715405 212891133276801093643277)
                      ·
                        rfl

theorem cell23_414604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_414604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414604 prefixEnd_414604 := by exact prefixLift 414604
  have htrace : WordTrace (prefixWord ++ tailWord_414604) baseStart_414604 baseEnd_414604 := by
    simpa [prefixWord, tailWord_414604, baseEnd_414604] using wordTrace_append hprefix tailTrace_414604
  have hstable : (prefixWord ++ tailWord_414604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414604).length < 2 ^ (prefixWord ++ tailWord_414604).sum := by decide
  have hdescent : baseEnd_414604 < baseStart_414604 := by decide
  rcases family_descends (prefixWord ++ tailWord_414604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414621 : List Nat := [1, 4, 2, 1, 2, 1, 5, 1, 1, 2, 3]
def baseStart_414621 : Nat := 118140960795 + 414621 * 2 ^ 59
def prefixEnd_414621 : Nat := 4983230072969 + 3 ^ 40 * 414621 * 2
def baseEnd_414621 : Nat := 212899862447927527130699

theorem tailTrace_414621 : CollatzResearch.WordTrace tailWord_414621 prefixEnd_414621 212899862447927527130699 := by
  unfold tailWord_414621
  simp only [CollatzResearch.WordTrace]
  refine ⟨15122470230906403474307717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10081646820604268982871811 15122470230906403474307717)
  ·
    refine ⟨2835463168294950651432697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15122470230906403474307717 2835463168294950651432697)
    ·
      refine ⟨2126597376221212988574523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2835463168294950651432697 2126597376221212988574523)
      ·
        refine ⟨3189896064331819482861785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2126597376221212988574523 3189896064331819482861785)
        ·
          refine ⟨2392422048248864612146339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3189896064331819482861785 2392422048248864612146339)
          ·
            refine ⟨3588633072373296918219509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2392422048248864612146339 3588633072373296918219509)
            ·
              refine ⟨336434350534996586083079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3588633072373296918219509 336434350534996586083079)
              ·
                refine ⟨504651525802494879124619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 336434350534996586083079 504651525802494879124619)
                ·
                  refine ⟨756977288703742318686929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 504651525802494879124619 756977288703742318686929)
                  ·
                    refine ⟨567732966527806739015197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 756977288703742318686929 567732966527806739015197)
                    ·
                      refine ⟨212899862447927527130699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 567732966527806739015197 212899862447927527130699)
                      ·
                        rfl

theorem cell23_414621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_414621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414621 prefixEnd_414621 := by exact prefixLift 414621
  have htrace : WordTrace (prefixWord ++ tailWord_414621) baseStart_414621 baseEnd_414621 := by
    simpa [prefixWord, tailWord_414621, baseEnd_414621] using wordTrace_append hprefix tailTrace_414621
  have hstable : (prefixWord ++ tailWord_414621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414621).length < 2 ^ (prefixWord ++ tailWord_414621).sum := by decide
  have hdescent : baseEnd_414621 < baseStart_414621 := by decide
  rcases family_descends (prefixWord ++ tailWord_414621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414669 : List Nat := [1, 6, 3, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_414669 : Nat := 118140960795 + 414669 * 2 ^ 59
def prefixEnd_414669 : Nat := 4983230072969 + 3 ^ 40 * 414669 * 2
def baseEnd_414669 : Nat := 212924509519343339330479

theorem tailTrace_414669 : CollatzResearch.WordTrace tailWord_414669 prefixEnd_414669 212924509519343339330479 := by
  unfold tailWord_414669
  simp only [CollatzResearch.WordTrace]
  refine ⟨15124220934732507672055061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10082813956488338448036707 15124220934732507672055061)
  ·
    refine ⟨708947856315586297127581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15124220934732507672055061 708947856315586297127581)
    ·
      refine ⟨265855446118344861422843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 708947856315586297127581 265855446118344861422843)
      ·
        refine ⟨398783169177517292134265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265855446118344861422843 398783169177517292134265)
        ·
          refine ⟨299087376883137969100699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398783169177517292134265 299087376883137969100699)
          ·
            refine ⟨448631065324706953651049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299087376883137969100699 448631065324706953651049)
            ·
              refine ⟨336473298993530215238287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 448631065324706953651049 336473298993530215238287)
              ·
                refine ⟨504709948490295322857431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 336473298993530215238287 504709948490295322857431)
                ·
                  refine ⟨757064922735442984286147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 504709948490295322857431 757064922735442984286147)
                  ·
                    refine ⟨1135597384103164476429221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 757064922735442984286147 1135597384103164476429221)
                    ·
                      refine ⟨212924509519343339330479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1135597384103164476429221 212924509519343339330479)
                      ·
                        rfl

theorem cell23_414669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_414669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414669 prefixEnd_414669 := by exact prefixLift 414669
  have htrace : WordTrace (prefixWord ++ tailWord_414669) baseStart_414669 baseEnd_414669 := by
    simpa [prefixWord, tailWord_414669, baseEnd_414669] using wordTrace_append hprefix tailTrace_414669
  have hstable : (prefixWord ++ tailWord_414669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414669).length < 2 ^ (prefixWord ++ tailWord_414669).sum := by decide
  have hdescent : baseEnd_414669 < baseStart_414669 := by decide
  rcases family_descends (prefixWord ++ tailWord_414669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414691 : List Nat := [1, 1, 1, 6, 1, 1, 3, 1, 4, 2, 2]
def baseStart_414691 : Nat := 118140960795 + 414691 * 2 ^ 59
def prefixEnd_414691 : Nat := 4983230072969 + 3 ^ 40 * 414691 * 2
def baseEnd_414691 : Nat := 212935806093742253255377

theorem tailTrace_414691 : CollatzResearch.WordTrace tailWord_414691 prefixEnd_414691 212935806093742253255377 := by
  unfold tailWord_414691
  simp only [CollatzResearch.WordTrace]
  refine ⟨15125023340652805429355927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10083348893768536952903951 15125023340652805429355927)
  ·
    refine ⟨22687535010979208144033891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15125023340652805429355927 22687535010979208144033891)
    ·
      refine ⟨34031302516468812216050837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22687535010979208144033891 34031302516468812216050837)
      ·
        refine ⟨1595217305459475572627383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34031302516468812216050837 1595217305459475572627383)
        ·
          refine ⟨2392825958189213358941075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1595217305459475572627383 2392825958189213358941075)
          ·
            refine ⟨3589238937283820038411613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2392825958189213358941075 3589238937283820038411613)
            ·
              refine ⟨1345964601481432514404355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3589238937283820038411613 1345964601481432514404355)
              ·
                refine ⟨2018946902222148771606533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1345964601481432514404355 2018946902222148771606533)
                ·
                  refine ⟨378552544166652894676225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2018946902222148771606533 378552544166652894676225)
                  ·
                    refine ⟨283914408124989671007169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 378552544166652894676225 283914408124989671007169)
                    ·
                      refine ⟨212935806093742253255377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 283914408124989671007169 212935806093742253255377)
                      ·
                        rfl

theorem cell23_414691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_414691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414691 prefixEnd_414691 := by exact prefixLift 414691
  have htrace : WordTrace (prefixWord ++ tailWord_414691) baseStart_414691 baseEnd_414691 := by
    simpa [prefixWord, tailWord_414691, baseEnd_414691] using wordTrace_append hprefix tailTrace_414691
  have hstable : (prefixWord ++ tailWord_414691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414691).length < 2 ^ (prefixWord ++ tailWord_414691).sum := by decide
  have hdescent : baseEnd_414691 < baseStart_414691 := by decide
  rcases family_descends (prefixWord ++ tailWord_414691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414727 : List Nat := [1, 1, 4, 3, 1, 1, 1, 3, 1, 7]
def baseStart_414727 : Nat := 118140960795 + 414727 * 2 ^ 59
def prefixEnd_414727 : Nat := 4983230072969 + 3 ^ 40 * 414727 * 2
def baseEnd_414727 : Nat := 70984763799101370801737

theorem tailTrace_414727 : CollatzResearch.WordTrace tailWord_414727 prefixEnd_414727 70984763799101370801737 := by
  unfold tailWord_414727
  simp only [CollatzResearch.WordTrace]
  refine ⟨15126336368522383577666435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10084224245681589051777623 15126336368522383577666435)
  ·
    refine ⟨22689504552783575366499653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15126336368522383577666435 22689504552783575366499653)
    ·
      refine ⟨4254282103646920381218685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22689504552783575366499653 4254282103646920381218685)
      ·
        refine ⟨1595355788867595142957007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4254282103646920381218685 1595355788867595142957007)
        ·
          refine ⟨2393033683301392714435511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1595355788867595142957007 2393033683301392714435511)
          ·
            refine ⟨3589550524952089071653267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2393033683301392714435511 3589550524952089071653267)
            ·
              refine ⟨5384325787428133607479901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3589550524952089071653267 5384325787428133607479901)
              ·
                refine ⟨2019122170285550102804963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5384325787428133607479901 2019122170285550102804963)
                ·
                  refine ⟨3028683255428325154207445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2019122170285550102804963 3028683255428325154207445)
                  ·
                    refine ⟨70984763799101370801737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3028683255428325154207445 70984763799101370801737)
                    ·
                      rfl

theorem cell23_414727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_414727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414727 prefixEnd_414727 := by exact prefixLift 414727
  have htrace : WordTrace (prefixWord ++ tailWord_414727) baseStart_414727 baseEnd_414727 := by
    simpa [prefixWord, tailWord_414727, baseEnd_414727] using wordTrace_append hprefix tailTrace_414727
  have hstable : (prefixWord ++ tailWord_414727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414727).length < 2 ^ (prefixWord ++ tailWord_414727).sum := by decide
  have hdescent : baseEnd_414727 < baseStart_414727 := by decide
  rcases family_descends (prefixWord ++ tailWord_414727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414731 : List Nat := [1, 1, 1, 1, 6, 4, 1, 3, 5]
def baseStart_414731 : Nat := 118140960795 + 414731 * 2 ^ 59
def prefixEnd_414731 : Nat := 4983230072969 + 3 ^ 40 * 414731 * 2
def baseEnd_414731 : Nat := 23661816146658010750577

theorem tailTrace_414731 : CollatzResearch.WordTrace tailWord_414731 prefixEnd_414731 23661816146658010750577 := by
  unfold tailWord_414731
  simp only [CollatzResearch.WordTrace]
  refine ⟨15126482260507892260812047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10084321507005261507208031 15126482260507892260812047)
  ·
    refine ⟨22689723390761838391218071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15126482260507892260812047 22689723390761838391218071)
    ·
      refine ⟨34034585086142757586827107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22689723390761838391218071 34034585086142757586827107)
      ·
        refine ⟨51051877629214136380240661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34034585086142757586827107 51051877629214136380240661)
        ·
          refine ⟨2393056763869412642823781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51051877629214136380240661 2393056763869412642823781)
          ·
            refine ⟨448698143225514870529459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2393056763869412642823781 448698143225514870529459)
            ·
              refine ⟨673047214838272305794189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448698143225514870529459 673047214838272305794189)
              ·
                refine ⟨252392705564352114672821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 673047214838272305794189 252392705564352114672821)
                ·
                  refine ⟨23661816146658010750577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 252392705564352114672821 23661816146658010750577)
                  ·
                    rfl

theorem cell23_414731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 5].length) (baseStart_414731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414731 prefixEnd_414731 := by exact prefixLift 414731
  have htrace : WordTrace (prefixWord ++ tailWord_414731) baseStart_414731 baseEnd_414731 := by
    simpa [prefixWord, tailWord_414731, baseEnd_414731] using wordTrace_append hprefix tailTrace_414731
  have hstable : (prefixWord ++ tailWord_414731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414731).length < 2 ^ (prefixWord ++ tailWord_414731).sum := by decide
  have hdescent : baseEnd_414731 < baseStart_414731 := by decide
  rcases family_descends (prefixWord ++ tailWord_414731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414744 : List Nat := [2, 1, 2, 3, 2, 3, 1, 2, 2, 5]
def baseStart_414744 : Nat := 118140960795 + 414744 * 2 ^ 59
def prefixEnd_414744 : Nat := 4983230072969 + 3 ^ 40 * 414744 * 2
def baseEnd_414744 : Nat := 70987673522810181964211

theorem tailTrace_414744 : CollatzResearch.WordTrace tailWord_414744 prefixEnd_414744 70987673522810181964211 := by
  unfold tailWord_414744
  simp only [CollatzResearch.WordTrace]
  refine ⟨7563478204730397740517643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10084637606307196987356857 7563478204730397740517643)
  ·
    refine ⟨11345217307095596610776465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7563478204730397740517643 11345217307095596610776465)
    ·
      refine ⟨8508912980321697458082349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11345217307095596610776465 8508912980321697458082349)
      ·
        refine ⟨3190842367620636546780881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8508912980321697458082349 3190842367620636546780881)
        ·
          refine ⟨2393131775715477410085661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3190842367620636546780881 2393131775715477410085661)
          ·
            refine ⟨897424415893304028782123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2393131775715477410085661 897424415893304028782123)
            ·
              refine ⟨1346136623839956043173185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897424415893304028782123 1346136623839956043173185)
              ·
                refine ⟨1009602467879967032379889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1346136623839956043173185 1009602467879967032379889)
                ·
                  refine ⟨757201850909975274284917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1009602467879967032379889 757201850909975274284917)
                  ·
                    refine ⟨70987673522810181964211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 757201850909975274284917 70987673522810181964211)
                    ·
                      rfl

theorem cell23_414744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 2, 5].length) (baseStart_414744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414744 prefixEnd_414744 := by exact prefixLift 414744
  have htrace : WordTrace (prefixWord ++ tailWord_414744) baseStart_414744 baseEnd_414744 := by
    simpa [prefixWord, tailWord_414744, baseEnd_414744] using wordTrace_append hprefix tailTrace_414744
  have hstable : (prefixWord ++ tailWord_414744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414744).length < 2 ^ (prefixWord ++ tailWord_414744).sum := by decide
  have hdescent : baseEnd_414744 < baseStart_414744 := by decide
  rcases family_descends (prefixWord ++ tailWord_414744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414748 : List Nat := [2, 2, 3, 1, 4, 1, 3, 2, 5]
def baseStart_414748 : Nat := 118140960795 + 414748 * 2 ^ 59
def prefixEnd_414748 : Nat := 4983230072969 + 3 ^ 40 * 414748 * 2
def baseEnd_414748 : Nat := 23662786054560947804735

theorem tailTrace_414748 : CollatzResearch.WordTrace tailWord_414748 prefixEnd_414748 23662786054560947804735 := by
  unfold tailWord_414748
  simp only [CollatzResearch.WordTrace]
  refine ⟨7563551150723152082090449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10084734867630869442787265 7563551150723152082090449)
  ·
    refine ⟨5672663363042364061567837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7563551150723152082090449 5672663363042364061567837)
    ·
      refine ⟨2127248761140886523087939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5672663363042364061567837 2127248761140886523087939)
      ·
        refine ⟨3190873141711329784631909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2127248761140886523087939 3190873141711329784631909)
        ·
          refine ⟨598288714070874334618483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3190873141711329784631909 598288714070874334618483)
          ·
            refine ⟨897433071106311501927725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598288714070874334618483 897433071106311501927725)
            ·
              refine ⟨336537401664866813222897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 897433071106311501927725 336537401664866813222897)
              ·
                refine ⟨252403051248650109917173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 336537401664866813222897 252403051248650109917173)
                ·
                  refine ⟨23662786054560947804735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 252403051248650109917173 23662786054560947804735)
                  ·
                    rfl

theorem cell23_414748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 5].length) (baseStart_414748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414748 prefixEnd_414748 := by exact prefixLift 414748
  have htrace : WordTrace (prefixWord ++ tailWord_414748) baseStart_414748 baseEnd_414748 := by
    simpa [prefixWord, tailWord_414748, baseEnd_414748] using wordTrace_append hprefix tailTrace_414748
  have hstable : (prefixWord ++ tailWord_414748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414748).length < 2 ^ (prefixWord ++ tailWord_414748).sum := by decide
  have hdescent : baseEnd_414748 < baseStart_414748 := by decide
  rcases family_descends (prefixWord ++ tailWord_414748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414754 : List Nat := [3, 3, 1, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_414754 : Nat := 118140960795 + 414754 * 2 ^ 59
def prefixEnd_414754 : Nat := 4983230072969 + 3 ^ 40 * 414754 * 2
def baseEnd_414754 : Nat := 212968155374975506767587

theorem tailTrace_414754 : CollatzResearch.WordTrace tailWord_414754 prefixEnd_414754 212968155374975506767587 := by
  unfold tailWord_414754
  simp only [CollatzResearch.WordTrace]
  refine ⟨3781830284856141797224829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10084880759616378125932877 3781830284856141797224829)
  ·
    refine ⟨1418186356821053173959311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3781830284856141797224829 1418186356821053173959311)
    ·
      refine ⟨2127279535231579760938967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1418186356821053173959311 2127279535231579760938967)
      ·
        refine ⟨3190919302847369641408451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2127279535231579760938967 3190919302847369641408451)
        ·
          refine ⟨4786378954271054462112677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3190919302847369641408451 4786378954271054462112677)
          ·
            refine ⟨897446053925822711646127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4786378954271054462112677 897446053925822711646127)
            ·
              refine ⟨1346169080888734067469191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897446053925822711646127 1346169080888734067469191)
              ·
                refine ⟨2019253621333101101203787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1346169080888734067469191 2019253621333101101203787)
                ·
                  refine ⟨3028880431999651651805681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2019253621333101101203787 3028880431999651651805681)
                  ·
                    refine ⟨2271660323999738738854261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3028880431999651651805681 2271660323999738738854261)
                    ·
                      refine ⟨212968155374975506767587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2271660323999738738854261 212968155374975506767587)
                      ·
                        rfl

theorem cell23_414754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_414754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414754 prefixEnd_414754 := by exact prefixLift 414754
  have htrace : WordTrace (prefixWord ++ tailWord_414754) baseStart_414754 baseEnd_414754 := by
    simpa [prefixWord, tailWord_414754, baseEnd_414754] using wordTrace_append hprefix tailTrace_414754
  have hstable : (prefixWord ++ tailWord_414754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414754).length < 2 ^ (prefixWord ++ tailWord_414754).sum := by decide
  have hdescent : baseEnd_414754 < baseStart_414754 := by decide
  rcases family_descends (prefixWord ++ tailWord_414754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414764 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 1, 6, 2]
def baseStart_414764 : Nat := 118140960795 + 414764 * 2 ^ 59
def prefixEnd_414764 : Nat := 4983230072969 + 3 ^ 40 * 414764 * 2
def baseEnd_414764 : Nat := 212973290181520467642541

theorem tailTrace_414764 : CollatzResearch.WordTrace tailWord_414764 prefixEnd_414764 212973290181520467642541 := by
  unfold tailWord_414764
  simp only [CollatzResearch.WordTrace]
  refine ⟨7563842934694169448381673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10085123912925559264508897 7563842934694169448381673)
  ·
    refine ⟨5672882201020627086286255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7563842934694169448381673 5672882201020627086286255)
    ·
      refine ⟨8509323301530940629429383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5672882201020627086286255 8509323301530940629429383)
      ·
        refine ⟨12763984952296410944144075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8509323301530940629429383 12763984952296410944144075)
        ·
          refine ⟨19145977428444616416216113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12763984952296410944144075 19145977428444616416216113)
          ·
            refine ⟨14359483071333462312162085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19145977428444616416216113 14359483071333462312162085)
            ·
              refine ⟨2692403075875024183530391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14359483071333462312162085 2692403075875024183530391)
              ·
                refine ⟨4038604613812536275295587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2692403075875024183530391 4038604613812536275295587)
                ·
                  refine ⟨6057906920718804412943381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4038604613812536275295587 6057906920718804412943381)
                  ·
                    refine ⟨283964386908693956856721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6057906920718804412943381 283964386908693956856721)
                    ·
                      refine ⟨212973290181520467642541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 283964386908693956856721 212973290181520467642541)
                      ·
                        rfl

theorem cell23_414764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 6, 2].length) (baseStart_414764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414764 prefixEnd_414764 := by exact prefixLift 414764
  have htrace : WordTrace (prefixWord ++ tailWord_414764) baseStart_414764 baseEnd_414764 := by
    simpa [prefixWord, tailWord_414764, baseEnd_414764] using wordTrace_append hprefix tailTrace_414764
  have hstable : (prefixWord ++ tailWord_414764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414764).length < 2 ^ (prefixWord ++ tailWord_414764).sum := by decide
  have hdescent : baseEnd_414764 < baseStart_414764 := by decide
  rcases family_descends (prefixWord ++ tailWord_414764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414781 : List Nat := [1, 4, 1, 3, 1, 3, 2, 1, 2, 1, 4]
def baseStart_414781 : Nat := 118140960795 + 414781 * 2 ^ 59
def prefixEnd_414781 : Nat := 4983230072969 + 3 ^ 40 * 414781 * 2
def baseEnd_414781 : Nat := 212982019352646901129963

theorem tailTrace_414781 : CollatzResearch.WordTrace tailWord_414781 prefixEnd_414781 212982019352646901129963 := by
  unfold tailWord_414781
  simp only [CollatzResearch.WordTrace]
  refine ⟨15128305910326750800132197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10085537273551167200088131 15128305910326750800132197)
  ·
    refine ⟨2836557358186265775024787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15128305910326750800132197 2836557358186265775024787)
    ·
      refine ⟨4254836037279398662537181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2836557358186265775024787 4254836037279398662537181)
      ·
        refine ⟨1595563513979774498451443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4254836037279398662537181 1595563513979774498451443)
        ·
          refine ⟨2393345270969661747677165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1595563513979774498451443 2393345270969661747677165)
          ·
            refine ⟨897504476613623155378937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2393345270969661747677165 897504476613623155378937)
            ·
              refine ⟨673128357460217366534203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 897504476613623155378937 673128357460217366534203)
              ·
                refine ⟨1009692536190326049801305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 673128357460217366534203 1009692536190326049801305)
                ·
                  refine ⟨757269402142744537350979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1009692536190326049801305 757269402142744537350979)
                  ·
                    refine ⟨1135904103214116806026469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 757269402142744537350979 1135904103214116806026469)
                    ·
                      refine ⟨212982019352646901129963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1135904103214116806026469 212982019352646901129963)
                      ·
                        rfl

theorem cell23_414781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_414781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414781 prefixEnd_414781 := by exact prefixLift 414781
  have htrace : WordTrace (prefixWord ++ tailWord_414781) baseStart_414781 baseEnd_414781 := by
    simpa [prefixWord, tailWord_414781, baseEnd_414781] using wordTrace_append hprefix tailTrace_414781
  have hstable : (prefixWord ++ tailWord_414781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414781).length < 2 ^ (prefixWord ++ tailWord_414781).sum := by decide
  have hdescent : baseEnd_414781 < baseStart_414781 := by decide
  rcases family_descends (prefixWord ++ tailWord_414781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414804 : List Nat := [2, 4, 1, 1, 1, 1, 3, 4, 6]
def baseStart_414804 : Nat := 118140960795 + 414804 * 2 ^ 59
def prefixEnd_414804 : Nat := 4983230072969 + 3 ^ 40 * 414804 * 2
def baseEnd_414804 : Nat := 23665981045300034571373

theorem tailTrace_414804 : CollatzResearch.WordTrace tailWord_414804 prefixEnd_414804 23665981045300034571373 := by
  unfold tailWord_414804
  simp only [CollatzResearch.WordTrace]
  refine ⟨7564572394621712864109733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10086096526162283818812977 7564572394621712864109733)
  ·
    refine ⟨1418357323991571162020575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7564572394621712864109733 1418357323991571162020575)
    ·
      refine ⟨2127535985987356743030863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1418357323991571162020575 2127535985987356743030863)
      ·
        refine ⟨3191303978981035114546295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2127535985987356743030863 3191303978981035114546295)
        ·
          refine ⟨4786955968471552671819443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3191303978981035114546295 4786955968471552671819443)
          ·
            refine ⟨7180433952707329007729165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4786955968471552671819443 7180433952707329007729165)
            ·
              refine ⟨2692662732265248377898437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7180433952707329007729165 2692662732265248377898437)
              ·
                refine ⟨504874262299734070855957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2692662732265248377898437 504874262299734070855957)
                ·
                  refine ⟨23665981045300034571373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 504874262299734070855957 23665981045300034571373)
                  ·
                    rfl

theorem cell23_414804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_414804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414804 prefixEnd_414804 := by exact prefixLift 414804
  have htrace : WordTrace (prefixWord ++ tailWord_414804) baseStart_414804 baseEnd_414804 := by
    simpa [prefixWord, tailWord_414804, baseEnd_414804] using wordTrace_append hprefix tailTrace_414804
  have hstable : (prefixWord ++ tailWord_414804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414804).length < 2 ^ (prefixWord ++ tailWord_414804).sum := by decide
  have hdescent : baseEnd_414804 < baseStart_414804 := by decide
  rcases family_descends (prefixWord ++ tailWord_414804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414807 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 6]
def baseStart_414807 : Nat := 118140960795 + 414807 * 2 ^ 59
def prefixEnd_414807 : Nat := 4983230072969 + 3 ^ 40 * 414807 * 2
def baseEnd_414807 : Nat := 212995369849663799404843

theorem tailTrace_414807 : CollatzResearch.WordTrace tailWord_414807 prefixEnd_414807 212995369849663799404843 := by
  unfold tailWord_414807
  simp only [CollatzResearch.WordTrace]
  refine ⟨15129254208232557240578675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10086169472155038160385783 15129254208232557240578675)
  ·
    refine ⟨22693881312348835860868013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15129254208232557240578675 22693881312348835860868013)
    ·
      refine ⟨8510205492130813447825505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22693881312348835860868013 8510205492130813447825505)
      ·
        refine ⟨6382654119098110085869129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8510205492130813447825505 6382654119098110085869129)
        ·
          refine ⟨4786990589323582564401847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6382654119098110085869129 4786990589323582564401847)
          ·
            refine ⟨7180485883985373846602771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4786990589323582564401847 7180485883985373846602771)
            ·
              refine ⟨10770728825978060769904157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7180485883985373846602771 10770728825978060769904157)
              ·
                refine ⟨4039023309741772788714059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10770728825978060769904157 4039023309741772788714059)
                ·
                  refine ⟨6058534964612659183071089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4039023309741772788714059 6058534964612659183071089)
                  ·
                    refine ⟨4543901223459494387303317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6058534964612659183071089 4543901223459494387303317)
                    ·
                      refine ⟨212995369849663799404843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4543901223459494387303317 212995369849663799404843)
                      ·
                        rfl

theorem cell23_414807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_414807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414807 prefixEnd_414807 := by exact prefixLift 414807
  have htrace : WordTrace (prefixWord ++ tailWord_414807) baseStart_414807 baseEnd_414807 := by
    simpa [prefixWord, tailWord_414807, baseEnd_414807] using wordTrace_append hprefix tailTrace_414807
  have hstable : (prefixWord ++ tailWord_414807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414807).length < 2 ^ (prefixWord ++ tailWord_414807).sum := by decide
  have hdescent : baseEnd_414807 < baseStart_414807 := by decide
  rcases family_descends (prefixWord ++ tailWord_414807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414831 : List Nat := [1, 1, 2, 1, 3, 3, 3, 2, 3, 1, 3]
def baseStart_414831 : Nat := 118140960795 + 414831 * 2 ^ 59
def prefixEnd_414831 : Nat := 4983230072969 + 3 ^ 40 * 414831 * 2
def baseEnd_414831 : Nat := 213007693385371705504733

theorem tailTrace_414831 : CollatzResearch.WordTrace tailWord_414831 prefixEnd_414831 213007693385371705504733 := by
  unfold tailWord_414831
  simp only [CollatzResearch.WordTrace]
  refine ⟨15130129560145609339452347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10086753040097072892968231 15130129560145609339452347)
  ·
    refine ⟨22695194340218414009178521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15130129560145609339452347 22695194340218414009178521)
    ·
      refine ⟨17021395755163810506883891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22695194340218414009178521 17021395755163810506883891)
      ·
        refine ⟨25532093632745715760325837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17021395755163810506883891 25532093632745715760325837)
        ·
          refine ⟨9574535112279643410122189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25532093632745715760325837 9574535112279643410122189)
          ·
            refine ⟨3590450667104866278795821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9574535112279643410122189 3590450667104866278795821)
            ·
              refine ⟨1346419000164324854548433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3590450667104866278795821 1346419000164324854548433)
              ·
                refine ⟨1009814250123243640911325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1346419000164324854548433 1009814250123243640911325)
                ·
                  refine ⟨378680343796216365341747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1009814250123243640911325 378680343796216365341747)
                  ·
                    refine ⟨568020515694324548012621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 378680343796216365341747 568020515694324548012621)
                    ·
                      refine ⟨213007693385371705504733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 568020515694324548012621 213007693385371705504733)
                      ·
                        rfl

theorem cell23_414831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 1, 3].length) (baseStart_414831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414831 prefixEnd_414831 := by exact prefixLift 414831
  have htrace : WordTrace (prefixWord ++ tailWord_414831) baseStart_414831 baseEnd_414831 := by
    simpa [prefixWord, tailWord_414831, baseEnd_414831] using wordTrace_append hprefix tailTrace_414831
  have hstable : (prefixWord ++ tailWord_414831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414831).length < 2 ^ (prefixWord ++ tailWord_414831).sum := by decide
  have hdescent : baseEnd_414831 < baseStart_414831 := by decide
  rcases family_descends (prefixWord ++ tailWord_414831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414834 : List Nat := [3, 2, 1, 2, 2, 1, 1, 3, 3, 5]
def baseStart_414834 : Nat := 118140960795 + 414834 * 2 ^ 59
def prefixEnd_414834 : Nat := 4983230072969 + 3 ^ 40 * 414834 * 2
def baseEnd_414834 : Nat := 71003077942445064589073

theorem tailTrace_414834 : CollatzResearch.WordTrace tailWord_414834 prefixEnd_414834 71003077942445064589073 := by
  unfold tailWord_414834
  simp only [CollatzResearch.WordTrace]
  refine ⟨3782559744783685212952889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10086825986089827234541037 3782559744783685212952889)
  ·
    refine ⟨2836919808587763909714667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3782559744783685212952889 2836919808587763909714667)
    ·
      refine ⟨4255379712881645864572001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2836919808587763909714667 4255379712881645864572001)
      ·
        refine ⟨3191534784661234398429001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4255379712881645864572001 3191534784661234398429001)
        ·
          refine ⟨2393651088495925798821751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3191534784661234398429001 2393651088495925798821751)
          ·
            refine ⟨3590476632743888698232627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2393651088495925798821751 3590476632743888698232627)
            ·
              refine ⟨5385714949115833047348941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3590476632743888698232627 5385714949115833047348941)
              ·
                refine ⟨2019643105918437392755853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5385714949115833047348941 2019643105918437392755853)
                ·
                  refine ⟨757366164719414022283445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2019643105918437392755853 757366164719414022283445)
                  ·
                    refine ⟨71003077942445064589073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 757366164719414022283445 71003077942445064589073)
                    ·
                      rfl

theorem cell23_414834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_414834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414834 prefixEnd_414834 := by exact prefixLift 414834
  have htrace : WordTrace (prefixWord ++ tailWord_414834) baseStart_414834 baseEnd_414834 := by
    simpa [prefixWord, tailWord_414834, baseEnd_414834] using wordTrace_append hprefix tailTrace_414834
  have hstable : (prefixWord ++ tailWord_414834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414834).length < 2 ^ (prefixWord ++ tailWord_414834).sum := by decide
  have hdescent : baseEnd_414834 < baseStart_414834 := by decide
  rcases family_descends (prefixWord ++ tailWord_414834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414848 : List Nat := [2, 1, 1, 2, 1, 3, 3, 5, 1, 1, 3]
def baseStart_414848 : Nat := 118140960795 + 414848 * 2 ^ 59
def prefixEnd_414848 : Nat := 4983230072969 + 3 ^ 40 * 414848 * 2
def baseEnd_414848 : Nat := 213016422556498138992155

theorem tailTrace_414848 : CollatzResearch.WordTrace tailWord_414848 prefixEnd_414848 213016422556498138992155 := by
  unfold tailWord_414848
  simp only [CollatzResearch.WordTrace]
  refine ⟨7565374800542010621410599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10087166400722680828547465 7565374800542010621410599)
  ·
    refine ⟨11348062200813015932115899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7565374800542010621410599 11348062200813015932115899)
    ·
      refine ⟨17022093301219523898173849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11348062200813015932115899 17022093301219523898173849)
      ·
        refine ⟨12766569975914642923630387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17022093301219523898173849 12766569975914642923630387)
        ·
          refine ⟨19149854963871964385445581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12766569975914642923630387 19149854963871964385445581)
          ·
            refine ⟨7181195611451986644542093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19149854963871964385445581 7181195611451986644542093)
            ·
              refine ⟨2692948354294494991703285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7181195611451986644542093 2692948354294494991703285)
              ·
                refine ⟨252463908215108905472183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2692948354294494991703285 252463908215108905472183)
                ·
                  refine ⟨378695862322663358208275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 252463908215108905472183 378695862322663358208275)
                  ·
                    refine ⟨568043793483995037312413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 378695862322663358208275 568043793483995037312413)
                    ·
                      refine ⟨213016422556498138992155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 568043793483995037312413 213016422556498138992155)
                      ·
                        rfl

theorem cell23_414848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 1, 1, 3].length) (baseStart_414848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414848 prefixEnd_414848 := by exact prefixLift 414848
  have htrace : WordTrace (prefixWord ++ tailWord_414848) baseStart_414848 baseEnd_414848 := by
    simpa [prefixWord, tailWord_414848, baseEnd_414848] using wordTrace_append hprefix tailTrace_414848
  have hstable : (prefixWord ++ tailWord_414848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414848).length < 2 ^ (prefixWord ++ tailWord_414848).sum := by decide
  have hdescent : baseEnd_414848 < baseStart_414848 := by decide
  rcases family_descends (prefixWord ++ tailWord_414848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414908 : List Nat := [2, 2, 2, 3, 2, 1, 2, 3, 1, 2, 3]
def baseStart_414908 : Nat := 118140960795 + 414908 * 2 ^ 59
def prefixEnd_414908 : Nat := 4983230072969 + 3 ^ 40 * 414908 * 2
def baseEnd_414908 : Nat := 213047231395767904241879

theorem tailTrace_414908 : CollatzResearch.WordTrace tailWord_414908 prefixEnd_414908 213047231395767904241879 := by
  unfold tailWord_414908
  simp only [CollatzResearch.WordTrace]
  refine ⟨7566468990433325745002689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10088625320577767660003585 7566468990433325745002689)
  ·
    refine ⟨5674851742824994308752017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7566468990433325745002689 5674851742824994308752017)
    ·
      refine ⟨4256138807118745731564013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5674851742824994308752017 4256138807118745731564013)
      ·
        refine ⟨1596052052669529649336505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4256138807118745731564013 1596052052669529649336505)
        ·
          refine ⟨1197039039502147237002379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1596052052669529649336505 1197039039502147237002379)
          ·
            refine ⟨1795558559253220855503569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1197039039502147237002379 1795558559253220855503569)
            ·
              refine ⟨1346668919439915641627677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1795558559253220855503569 1346668919439915641627677)
              ·
                refine ⟨505000844789968365610379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1346668919439915641627677 505000844789968365610379)
                ·
                  refine ⟨757501267184952548415569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 505000844789968365610379 757501267184952548415569)
                  ·
                    refine ⟨568125950388714411311677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 757501267184952548415569 568125950388714411311677)
                    ·
                      refine ⟨213047231395767904241879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 568125950388714411311677 213047231395767904241879)
                      ·
                        rfl

theorem cell23_414908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_414908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414908 prefixEnd_414908 := by exact prefixLift 414908
  have htrace : WordTrace (prefixWord ++ tailWord_414908) baseStart_414908 baseEnd_414908 := by
    simpa [prefixWord, tailWord_414908, baseEnd_414908] using wordTrace_append hprefix tailTrace_414908
  have hstable : (prefixWord ++ tailWord_414908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414908).length < 2 ^ (prefixWord ++ tailWord_414908).sum := by decide
  have hdescent : baseEnd_414908 < baseStart_414908 := by decide
  rcases family_descends (prefixWord ++ tailWord_414908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414931 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 5, 3, 2]
def baseStart_414931 : Nat := 118140960795 + 414931 * 2 ^ 59
def prefixEnd_414931 : Nat := 4983230072969 + 3 ^ 40 * 414931 * 2
def baseEnd_414931 : Nat := 213059041450821314254273

theorem tailTrace_414931 : CollatzResearch.WordTrace tailWord_414931 prefixEnd_414931 213059041450821314254273 := by
  unfold tailWord_414931
  simp only [CollatzResearch.WordTrace]
  refine ⟨15133776859783326418092647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10089184573188884278728431 15133776859783326418092647)
  ·
    refine ⟨22700665289674989627138971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15133776859783326418092647 22700665289674989627138971)
    ·
      refine ⟨34050997934512484440708457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22700665289674989627138971 34050997934512484440708457)
      ·
        refine ⟨25538248450884363330531343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34050997934512484440708457 25538248450884363330531343)
        ·
          refine ⟨38307372676326544995797015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25538248450884363330531343 38307372676326544995797015)
          ·
            refine ⟨57461059014489817493695523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38307372676326544995797015 57461059014489817493695523)
            ·
              refine ⟨86191588521734726240543285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57461059014489817493695523 86191588521734726240543285)
              ·
                refine ⟨8080461423912630585050933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86191588521734726240543285 8080461423912630585050933)
                ·
                  refine ⟨757543258491809117348525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8080461423912630585050933 757543258491809117348525)
                  ·
                    refine ⟨284078721934428419005697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 757543258491809117348525 284078721934428419005697)
                    ·
                      refine ⟨213059041450821314254273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 284078721934428419005697 213059041450821314254273)
                      ·
                        rfl

theorem cell23_414931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 3, 2].length) (baseStart_414931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_414931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_414931 prefixEnd_414931 := by exact prefixLift 414931
  have htrace : WordTrace (prefixWord ++ tailWord_414931) baseStart_414931 baseEnd_414931 := by
    simpa [prefixWord, tailWord_414931, baseEnd_414931] using wordTrace_append hprefix tailTrace_414931
  have hstable : (prefixWord ++ tailWord_414931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414931).length < 2 ^ (prefixWord ++ tailWord_414931).sum := by decide
  have hdescent : baseEnd_414931 < baseStart_414931 := by decide
  rcases family_descends (prefixWord ++ tailWord_414931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415028 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_415028 : Nat := 118140960795 + 415028 * 2 ^ 59
def prefixEnd_415028 : Nat := 4983230072969 + 3 ^ 40 * 415028 * 2
def baseEnd_415028 : Nat := 213108849074307434741327

theorem tailTrace_415028 : CollatzResearch.WordTrace tailWord_415028 prefixEnd_415028 213108849074307434741327 := by
  unfold tailWord_415028
  simp only [CollatzResearch.WordTrace]
  refine ⟨7568657370215955992186869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10091543160287941322915825 7568657370215955992186869)
  ·
    refine ⟨709561628457745874267519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7568657370215955992186869 709561628457745874267519)
    ·
      refine ⟨1064342442686618811401279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 709561628457745874267519 1064342442686618811401279)
      ·
        refine ⟨1596513664029928217101919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1064342442686618811401279 1596513664029928217101919)
        ·
          refine ⟨2394770496044892325652879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1596513664029928217101919 2394770496044892325652879)
          ·
            refine ⟨3592155744067338488479319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2394770496044892325652879 3592155744067338488479319)
            ·
              refine ⟨5388233616101007732718979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3592155744067338488479319 5388233616101007732718979)
              ·
                refine ⟨8082350424151511599078469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5388233616101007732718979 8082350424151511599078469)
                ·
                  refine ⟨1515440704528408424827213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8082350424151511599078469 1515440704528408424827213)
                  ·
                    refine ⟨568290264198153159310205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1515440704528408424827213 568290264198153159310205)
                    ·
                      refine ⟨213108849074307434741327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 568290264198153159310205 213108849074307434741327)
                      ·
                        rfl

theorem cell23_415028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_415028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415028 prefixEnd_415028 := by exact prefixLift 415028
  have htrace : WordTrace (prefixWord ++ tailWord_415028) baseStart_415028 baseEnd_415028 := by
    simpa [prefixWord, tailWord_415028, baseEnd_415028] using wordTrace_append hprefix tailTrace_415028
  have hstable : (prefixWord ++ tailWord_415028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415028).length < 2 ^ (prefixWord ++ tailWord_415028).sum := by decide
  have hdescent : baseEnd_415028 < baseStart_415028 := by decide
  rcases family_descends (prefixWord ++ tailWord_415028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415046 : List Nat := [6, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2]
def baseStart_415046 : Nat := 118140960795 + 415046 * 2 ^ 59
def prefixEnd_415046 : Nat := 4983230072969 + 3 ^ 40 * 415046 * 2
def baseEnd_415046 : Nat := 213118091726088364316245

theorem tailTrace_415046 : CollatzResearch.WordTrace tailWord_415046 prefixEnd_415046 213118091726088364316245 := by
  unfold tailWord_415046
  simp only [CollatzResearch.WordTrace]
  refine ⟨473061601698959408079031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10091980836244467372352661 473061601698959408079031)
  ·
    refine ⟨709592402548439112118547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 473061601698959408079031 709592402548439112118547)
    ·
      refine ⟨1064388603822658668177821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 709592402548439112118547 1064388603822658668177821)
      ·
        refine ⟨399145726433497000566683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1064388603822658668177821 399145726433497000566683)
        ·
          refine ⟨598718589650245500850025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399145726433497000566683 598718589650245500850025)
          ·
            refine ⟨449038942237684125637519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 598718589650245500850025 449038942237684125637519)
            ·
              refine ⟨673558413356526188456279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449038942237684125637519 673558413356526188456279)
              ·
                refine ⟨1010337620034789282684419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 673558413356526188456279 1010337620034789282684419)
                ·
                  refine ⟨1515506430052183924026629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1010337620034789282684419 1515506430052183924026629)
                  ·
                    refine ⟨284157455634784485754993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1515506430052183924026629 284157455634784485754993)
                    ·
                      refine ⟨213118091726088364316245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 284157455634784485754993 213118091726088364316245)
                      ·
                        rfl

theorem cell23_415046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_415046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415046 prefixEnd_415046 := by exact prefixLift 415046
  have htrace : WordTrace (prefixWord ++ tailWord_415046) baseStart_415046 baseEnd_415046 := by
    simpa [prefixWord, tailWord_415046, baseEnd_415046] using wordTrace_append hprefix tailTrace_415046
  have hstable : (prefixWord ++ tailWord_415046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415046).length < 2 ^ (prefixWord ++ tailWord_415046).sum := by decide
  have hdescent : baseEnd_415046 < baseStart_415046 := by decide
  rcases family_descends (prefixWord ++ tailWord_415046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415088 : List Nat := [2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 3]
def baseStart_415088 : Nat := 118140960795 + 415088 * 2 ^ 59
def prefixEnd_415088 : Nat := 4983230072969 + 3 ^ 40 * 415088 * 2
def baseEnd_415088 : Nat := 213139657913577199991051

theorem tailTrace_415088 : CollatzResearch.WordTrace tailWord_415088 prefixEnd_415088 213139657913577199991051 := by
  unfold tailWord_415088
  simp only [CollatzResearch.WordTrace]
  refine ⟨7569751560107271115778959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10093002080143028154371945 7569751560107271115778959)
  ·
    refine ⟨11354627340160906673668439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7569751560107271115778959 11354627340160906673668439)
    ·
      refine ⟨17031941010241360010502659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11354627340160906673668439 17031941010241360010502659)
      ·
        refine ⟨25547911515362040015753989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17031941010241360010502659 25547911515362040015753989)
        ·
          refine ⟨4790233409130382502953873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25547911515362040015753989 4790233409130382502953873)
          ·
            refine ⟨3592675056847786877215405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4790233409130382502953873 3592675056847786877215405)
            ·
              refine ⟨1347253146317920078955777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3592675056847786877215405 1347253146317920078955777)
              ·
                refine ⟨1010439859738440059216833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1347253146317920078955777 1010439859738440059216833)
                ·
                  refine ⟨757829894803830044412625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1010439859738440059216833 757829894803830044412625)
                  ·
                    refine ⟨568372421102872533309469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 757829894803830044412625 568372421102872533309469)
                    ·
                      refine ⟨213139657913577199991051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 568372421102872533309469 213139657913577199991051)
                      ·
                        rfl

theorem cell23_415088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 3].length) (baseStart_415088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415088 prefixEnd_415088 := by exact prefixLift 415088
  have htrace : WordTrace (prefixWord ++ tailWord_415088) baseStart_415088 baseEnd_415088 := by
    simpa [prefixWord, tailWord_415088, baseEnd_415088] using wordTrace_append hprefix tailTrace_415088
  have hstable : (prefixWord ++ tailWord_415088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415088).length < 2 ^ (prefixWord ++ tailWord_415088).sum := by decide
  have hdescent : baseEnd_415088 < baseStart_415088 := by decide
  rcases family_descends (prefixWord ++ tailWord_415088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415108 : List Nat := [2, 3, 2, 1, 1, 4, 1, 3, 6]
def baseStart_415108 : Nat := 118140960795 + 415108 * 2 ^ 59
def prefixEnd_415108 : Nat := 4983230072969 + 3 ^ 40 * 415108 * 2
def baseEnd_415108 : Nat := 23683325280740791304551

theorem tailTrace_415108 : CollatzResearch.WordTrace tailWord_415108 prefixEnd_415108 23683325280740791304551 := by
  unfold tailWord_415108
  simp only [CollatzResearch.WordTrace]
  refine ⟨7570116290071042823642989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10093488386761390431523985 7570116290071042823642989)
  ·
    refine ⟨2838793608776641058866121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7570116290071042823642989 2838793608776641058866121)
    ·
      refine ⟨2129095206582480794149591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2838793608776641058866121 2129095206582480794149591)
      ·
        refine ⟨3193642809873721191224387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2129095206582480794149591 3193642809873721191224387)
        ·
          refine ⟨4790464214810581786836581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3193642809873721191224387 4790464214810581786836581)
          ·
            refine ⟨898212040276984085031859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4790464214810581786836581 898212040276984085031859)
            ·
              refine ⟨1347318060415476127547789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 898212040276984085031859 1347318060415476127547789)
              ·
                refine ⟨505244272655803547830421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1347318060415476127547789 505244272655803547830421)
                ·
                  refine ⟨23683325280740791304551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 505244272655803547830421 23683325280740791304551)
                  ·
                    rfl

theorem cell23_415108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_415108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415108 prefixEnd_415108 := by exact prefixLift 415108
  have htrace : WordTrace (prefixWord ++ tailWord_415108) baseStart_415108 baseEnd_415108 := by
    simpa [prefixWord, tailWord_415108, baseEnd_415108] using wordTrace_append hprefix tailTrace_415108
  have hstable : (prefixWord ++ tailWord_415108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415108).length < 2 ^ (prefixWord ++ tailWord_415108).sum := by decide
  have hdescent : baseEnd_415108 < baseStart_415108 := by decide
  rcases family_descends (prefixWord ++ tailWord_415108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415121 : List Nat := [1, 2, 2, 1, 1, 1, 2, 5, 3, 5]
def baseStart_415121 : Nat := 118140960795 + 415121 * 2 ^ 59
def prefixEnd_415121 : Nat := 4983230072969 + 3 ^ 40 * 415121 * 2
def baseEnd_415121 : Nat := 71052200925058523626133

theorem tailTrace_415121 : CollatzResearch.WordTrace tailWord_415121 prefixEnd_415121 71052200925058523626133 := by
  unfold tailWord_415121
  simp only [CollatzResearch.WordTrace]
  refine ⟨15140706729094988867509217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10093804486063325911672811 15140706729094988867509217)
  ·
    refine ⟨11355530046821241650631913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15140706729094988867509217 11355530046821241650631913)
    ·
      refine ⟨8516647535115931237973935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11355530046821241650631913 8516647535115931237973935)
      ·
        refine ⟨12774971302673896856960903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8516647535115931237973935 12774971302673896856960903)
        ·
          refine ⟨19162456954010845285441355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12774971302673896856960903 19162456954010845285441355)
          ·
            refine ⟨28743685431016267928162033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19162456954010845285441355 28743685431016267928162033)
            ·
              refine ⟨21557764073262200946121525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28743685431016267928162033 21557764073262200946121525)
              ·
                refine ⟨2021040381868331338698893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21557764073262200946121525 2021040381868331338698893)
                ·
                  refine ⟨757890143200624252012085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2021040381868331338698893 757890143200624252012085)
                  ·
                    refine ⟨71052200925058523626133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 757890143200624252012085 71052200925058523626133)
                    ·
                      rfl

theorem cell23_415121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 5].length) (baseStart_415121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415121 prefixEnd_415121 := by exact prefixLift 415121
  have htrace : WordTrace (prefixWord ++ tailWord_415121) baseStart_415121 baseEnd_415121 := by
    simpa [prefixWord, tailWord_415121, baseEnd_415121] using wordTrace_append hprefix tailTrace_415121
  have hstable : (prefixWord ++ tailWord_415121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415121).length < 2 ^ (prefixWord ++ tailWord_415121).sum := by decide
  have hdescent : baseEnd_415121 < baseStart_415121 := by decide
  rcases family_descends (prefixWord ++ tailWord_415121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415171 : List Nat := [1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 6]
def baseStart_415171 : Nat := 118140960795 + 415171 * 2 ^ 59
def prefixEnd_415171 : Nat := 4983230072969 + 3 ^ 40 * 415171 * 2
def baseEnd_415171 : Nat := 213182276807900375253169

theorem tailTrace_415171 : CollatzResearch.WordTrace tailWord_415171 prefixEnd_415171 213182276807900375253169 := by
  unfold tailWord_415171
  simp only [CollatzResearch.WordTrace]
  refine ⟨15142530378913847406829367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10095020252609231604552911 15142530378913847406829367)
  ·
    refine ⟨22713795568370771110244051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15142530378913847406829367 22713795568370771110244051)
    ·
      refine ⟨34070693352556156665366077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22713795568370771110244051 34070693352556156665366077)
      ·
        refine ⟨12776510007208558749512279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34070693352556156665366077 12776510007208558749512279)
        ·
          refine ⟨19164765010812838124268419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12776510007208558749512279 19164765010812838124268419)
          ·
            refine ⟨28747147516219257186402629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19164765010812838124268419 28747147516219257186402629)
            ·
              refine ⟨5390090159291110722450493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28747147516219257186402629 5390090159291110722450493)
              ·
                refine ⟨2021283809734166520918935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5390090159291110722450493 2021283809734166520918935)
                ·
                  refine ⟨3031925714601249781378403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2021283809734166520918935 3031925714601249781378403)
                  ·
                    refine ⟨4547888571901874672067605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3031925714601249781378403 4547888571901874672067605)
                    ·
                      refine ⟨213182276807900375253169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4547888571901874672067605 213182276807900375253169)
                      ·
                        rfl

theorem cell23_415171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_415171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415171 prefixEnd_415171 := by exact prefixLift 415171
  have htrace : WordTrace (prefixWord ++ tailWord_415171) baseStart_415171 baseEnd_415171 := by
    simpa [prefixWord, tailWord_415171, baseEnd_415171] using wordTrace_append hprefix tailTrace_415171
  have hstable : (prefixWord ++ tailWord_415171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415171).length < 2 ^ (prefixWord ++ tailWord_415171).sum := by decide
  have hdescent : baseEnd_415171 < baseStart_415171 := by decide
  rcases family_descends (prefixWord ++ tailWord_415171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415211 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 2, 7]
def baseStart_415211 : Nat := 118140960795 + 415211 * 2 ^ 59
def prefixEnd_415211 : Nat := 4983230072969 + 3 ^ 40 * 415211 * 2
def baseEnd_415211 : Nat := 71067605344693406250995

theorem tailTrace_415211 : CollatzResearch.WordTrace tailWord_415211 prefixEnd_415211 71067605344693406250995 := by
  unfold tailWord_415211
  simp only [CollatzResearch.WordTrace]
  refine ⟨15143989298768934238285487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10095992865845956158856991 15143989298768934238285487)
  ·
    refine ⟨22715983948153401357428231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15143989298768934238285487 22715983948153401357428231)
    ·
      refine ⟨34073975922230102036142347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22715983948153401357428231 34073975922230102036142347)
      ·
        refine ⟨51110963883345153054213521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34073975922230102036142347 51110963883345153054213521)
        ·
          refine ⟨38333222912508864790660141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51110963883345153054213521 38333222912508864790660141)
          ·
            refine ⟨14374958592190824296497553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38333222912508864790660141 14374958592190824296497553)
            ·
              refine ⟨10781218944143118222373165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14374958592190824296497553 10781218944143118222373165)
              ·
                refine ⟨4042957104053669333389937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10781218944143118222373165 4042957104053669333389937)
                ·
                  refine ⟨3032217828040252000042453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4042957104053669333389937 3032217828040252000042453)
                  ·
                    refine ⟨71067605344693406250995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3032217828040252000042453 71067605344693406250995)
                    ·
                      rfl

theorem cell23_415211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 7].length) (baseStart_415211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415211 prefixEnd_415211 := by exact prefixLift 415211
  have htrace : WordTrace (prefixWord ++ tailWord_415211) baseStart_415211 baseEnd_415211 := by
    simpa [prefixWord, tailWord_415211, baseEnd_415211] using wordTrace_append hprefix tailTrace_415211
  have hstable : (prefixWord ++ tailWord_415211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415211).length < 2 ^ (prefixWord ++ tailWord_415211).sum := by decide
  have hdescent : baseEnd_415211 < baseStart_415211 := by decide
  rcases family_descends (prefixWord ++ tailWord_415211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415222 : List Nat := [5, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4]
def baseStart_415222 : Nat := 118140960795 + 415222 * 2 ^ 59
def prefixEnd_415222 : Nat := 4983230072969 + 3 ^ 40 * 415222 * 2
def baseEnd_415222 : Nat := 213208464321279675715435

theorem tailTrace_415222 : CollatzResearch.WordTrace tailWord_415222 prefixEnd_415222 213208464321279675715435 := by
  unfold tailWord_415222
  simp only [CollatzResearch.WordTrace]
  refine ⟨946524406358067694808495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10096260334486055411290613 946524406358067694808495)
  ·
    refine ⟨1419786609537101542212743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 946524406358067694808495 1419786609537101542212743)
    ·
      refine ⟨2129679914305652313319115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1419786609537101542212743 2129679914305652313319115)
      ·
        refine ⟨3194519871458478469978673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2129679914305652313319115 3194519871458478469978673)
        ·
          refine ⟨2395889903593858852484005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3194519871458478469978673 2395889903593858852484005)
          ·
            refine ⟨449229356923848534840751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2395889903593858852484005 449229356923848534840751)
            ·
              refine ⟨673844035385772802261127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449229356923848534840751 673844035385772802261127)
              ·
                refine ⟨1010766053078659203391691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 673844035385772802261127 1010766053078659203391691)
                ·
                  refine ⟨1516149079617988805087537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1010766053078659203391691 1516149079617988805087537)
                  ·
                    refine ⟨1137111809713491603815653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1516149079617988805087537 1137111809713491603815653)
                    ·
                      refine ⟨213208464321279675715435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1137111809713491603815653 213208464321279675715435)
                      ·
                        rfl

theorem cell23_415222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_415222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415222 prefixEnd_415222 := by exact prefixLift 415222
  have htrace : WordTrace (prefixWord ++ tailWord_415222) baseStart_415222 baseEnd_415222 := by
    simpa [prefixWord, tailWord_415222, baseEnd_415222] using wordTrace_append hprefix tailTrace_415222
  have hstable : (prefixWord ++ tailWord_415222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415222).length < 2 ^ (prefixWord ++ tailWord_415222).sum := by decide
  have hdescent : baseEnd_415222 < baseStart_415222 := by decide
  rcases family_descends (prefixWord ++ tailWord_415222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415231 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 8]
def baseStart_415231 : Nat := 118140960795 + 415231 * 2 ^ 59
def prefixEnd_415231 : Nat := 4983230072969 + 3 ^ 40 * 415231 * 2
def baseEnd_415231 : Nat := 213213085647170140502893

theorem tailTrace_415231 : CollatzResearch.WordTrace tailWord_415231 prefixEnd_415231 213213085647170140502893 := by
  unfold tailWord_415231
  simp only [CollatzResearch.WordTrace]
  refine ⟨15144718758696477654013547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10096479172464318436009031 15144718758696477654013547)
  ·
    refine ⟨22717078138044716481020321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15144718758696477654013547 22717078138044716481020321)
    ·
      refine ⟨17037808603533537360765241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22717078138044716481020321 17037808603533537360765241)
      ·
        refine ⟨12778356452650153020573931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17037808603533537360765241 12778356452650153020573931)
        ·
          refine ⟨19167534678975229530860897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12778356452650153020573931 19167534678975229530860897)
          ·
            refine ⟨14375651009231422148145673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19167534678975229530860897 14375651009231422148145673)
            ·
              refine ⟨10781738256923566611109255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14375651009231422148145673 10781738256923566611109255)
              ·
                refine ⟨16172607385385349916663883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10781738256923566611109255 16172607385385349916663883)
                ·
                  refine ⟨24258911078078024874995825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16172607385385349916663883 24258911078078024874995825)
                  ·
                    refine ⟨18194183308558518656246869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24258911078078024874995825 18194183308558518656246869)
                    ·
                      refine ⟨213213085647170140502893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 18194183308558518656246869 213213085647170140502893)
                      ·
                        rfl

theorem cell23_415231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_415231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415231 prefixEnd_415231 := by exact prefixLift 415231
  have htrace : WordTrace (prefixWord ++ tailWord_415231) baseStart_415231 baseEnd_415231 := by
    simpa [prefixWord, tailWord_415231, baseEnd_415231] using wordTrace_append hprefix tailTrace_415231
  have hstable : (prefixWord ++ tailWord_415231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415231).length < 2 ^ (prefixWord ++ tailWord_415231).sum := by decide
  have hdescent : baseEnd_415231 < baseStart_415231 := by decide
  rcases family_descends (prefixWord ++ tailWord_415231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415243 : List Nat := [1, 1, 1, 1, 9, 1, 1, 3, 1, 2, 2]
def baseStart_415243 : Nat := 118140960795 + 415243 * 2 ^ 59
def prefixEnd_415243 : Nat := 4983230072969 + 3 ^ 40 * 415243 * 2
def baseEnd_415243 : Nat := 213219247415024093552839

theorem tailTrace_415243 : CollatzResearch.WordTrace tailWord_415243 prefixEnd_415243 213219247415024093552839 := by
  unfold tailWord_415243
  simp only [CollatzResearch.WordTrace]
  refine ⟨15145156434653003703450383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10096770956435335802300255 15145156434653003703450383)
  ·
    refine ⟨22717734651979505555175575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15145156434653003703450383 22717734651979505555175575)
    ·
      refine ⟨34076601977969258332763363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22717734651979505555175575 34076601977969258332763363)
      ·
        refine ⟨51114902966953887499145045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34076601977969258332763363 51114902966953887499145045)
        ·
          refine ⟨299501384571995434565303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 51114902966953887499145045 299501384571995434565303)
          ·
            refine ⟨449252076857993151847955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299501384571995434565303 449252076857993151847955)
            ·
              refine ⟨673878115286989727771933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449252076857993151847955 673878115286989727771933)
              ·
                refine ⟨252704293232621147914475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 673878115286989727771933 252704293232621147914475)
                ·
                  refine ⟨379056439848931721871713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 252704293232621147914475 379056439848931721871713)
                  ·
                    refine ⟨284292329886698791403785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 379056439848931721871713 284292329886698791403785)
                    ·
                      refine ⟨213219247415024093552839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 284292329886698791403785 213219247415024093552839)
                      ·
                        rfl

theorem cell23_415243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 1, 2, 2].length) (baseStart_415243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415243 prefixEnd_415243 := by exact prefixLift 415243
  have htrace : WordTrace (prefixWord ++ tailWord_415243) baseStart_415243 baseEnd_415243 := by
    simpa [prefixWord, tailWord_415243, baseEnd_415243] using wordTrace_append hprefix tailTrace_415243
  have hstable : (prefixWord ++ tailWord_415243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415243).length < 2 ^ (prefixWord ++ tailWord_415243).sum := by decide
  have hdescent : baseEnd_415243 < baseStart_415243 := by decide
  rcases family_descends (prefixWord ++ tailWord_415243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415355 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 1, 6, 2]
def baseStart_415355 : Nat := 118140960795 + 415355 * 2 ^ 59
def prefixEnd_415355 : Nat := 4983230072969 + 3 ^ 40 * 415355 * 2
def baseEnd_415355 : Nat := 213276757248327655352323

theorem tailTrace_415355 : CollatzResearch.WordTrace tailWord_415355 prefixEnd_415355 213276757248327655352323 := by
  unfold tailWord_415355
  simp only [CollatzResearch.WordTrace]
  refine ⟨15149241410247246831527519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10099494273498164554351679 15149241410247246831527519)
  ·
    refine ⟨22723862115370870247291279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15149241410247246831527519 22723862115370870247291279)
    ·
      refine ⟨34085793173056305370936919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22723862115370870247291279 34085793173056305370936919)
      ·
        refine ⟨51128689759584458056405379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34085793173056305370936919 51128689759584458056405379)
        ·
          refine ⟨76693034639376687084608069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51128689759584458056405379 76693034639376687084608069)
          ·
            refine ⟨14379943994883128828364013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76693034639376687084608069 14379943994883128828364013)
            ·
              refine ⟨5392478998081173310636505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14379943994883128828364013 5392478998081173310636505)
              ·
                refine ⟨4044359248560879982977379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5392478998081173310636505 4044359248560879982977379)
                ·
                  refine ⟨6066538872841319974466069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4044359248560879982977379 6066538872841319974466069)
                  ·
                    refine ⟨284369009664436873803097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6066538872841319974466069 284369009664436873803097)
                    ·
                      refine ⟨213276757248327655352323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 284369009664436873803097 213276757248327655352323)
                      ·
                        rfl

theorem cell23_415355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 6, 2].length) (baseStart_415355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415355 prefixEnd_415355 := by exact prefixLift 415355
  have htrace : WordTrace (prefixWord ++ tailWord_415355) baseStart_415355 baseEnd_415355 := by
    simpa [prefixWord, tailWord_415355, baseEnd_415355] using wordTrace_append hprefix tailTrace_415355
  have hstable : (prefixWord ++ tailWord_415355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415355).length < 2 ^ (prefixWord ++ tailWord_415355).sum := by decide
  have hdescent : baseEnd_415355 < baseStart_415355 := by decide
  rcases family_descends (prefixWord ++ tailWord_415355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415365 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 5, 4]
def baseStart_415365 : Nat := 118140960795 + 415365 * 2 ^ 59
def prefixEnd_415365 : Nat := 4983230072969 + 3 ^ 40 * 415365 * 2
def baseEnd_415365 : Nat := 71093964018290872075759

theorem tailTrace_415365 : CollatzResearch.WordTrace tailWord_415365 prefixEnd_415365 71093964018290872075759 := by
  unfold tailWord_415365
  simp only [CollatzResearch.WordTrace]
  refine ⟨15149606140211018539391549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10099737426807345692927699 15149606140211018539391549)
  ·
    refine ⟨5681102302579131952271831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15149606140211018539391549 5681102302579131952271831)
    ·
      refine ⟨8521653453868697928407747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5681102302579131952271831 8521653453868697928407747)
      ·
        refine ⟨12782480180803046892611621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8521653453868697928407747 12782480180803046892611621)
        ·
          refine ⟨2396715033900571292364679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12782480180803046892611621 2396715033900571292364679)
          ·
            refine ⟨3595072550850856938547019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2396715033900571292364679 3595072550850856938547019)
            ·
              refine ⟨5392608826276285407820529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3595072550850856938547019 5392608826276285407820529)
              ·
                refine ⟨4044456619707214055865397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5392608826276285407820529 4044456619707214055865397)
                ·
                  refine ⟨379167808097551317737381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4044456619707214055865397 379167808097551317737381)
                  ·
                    refine ⟨71093964018290872075759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 379167808097551317737381 71093964018290872075759)
                    ·
                      rfl

theorem cell23_415365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 4].length) (baseStart_415365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415365 prefixEnd_415365 := by exact prefixLift 415365
  have htrace : WordTrace (prefixWord ++ tailWord_415365) baseStart_415365 baseEnd_415365 := by
    simpa [prefixWord, tailWord_415365, baseEnd_415365] using wordTrace_append hprefix tailTrace_415365
  have hstable : (prefixWord ++ tailWord_415365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415365).length < 2 ^ (prefixWord ++ tailWord_415365).sum := by decide
  have hdescent : baseEnd_415365 < baseStart_415365 := by decide
  rcases family_descends (prefixWord ++ tailWord_415365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415439 : List Nat := [1, 1, 2, 1, 1, 3, 1, 8, 1, 1, 3]
def baseStart_415439 : Nat := 118140960795 + 415439 * 2 ^ 59
def prefixEnd_415439 : Nat := 4983230072969 + 3 ^ 40 * 415439 * 2
def baseEnd_415439 : Nat := 213319889623305326701937

theorem tailTrace_415439 : CollatzResearch.WordTrace tailWord_415439 prefixEnd_415439 213319889623305326701937 := by
  unfold tailWord_415439
  simp only [CollatzResearch.WordTrace]
  refine ⟨15152305141942929177585371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10101536761295286118390247 15152305141942929177585371)
  ·
    refine ⟨22728457712914393766378057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15152305141942929177585371 22728457712914393766378057)
    ·
      refine ⟨17046343284685795324783543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22728457712914393766378057 17046343284685795324783543)
      ·
        refine ⟨25569514927028692987175315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17046343284685795324783543 25569514927028692987175315)
        ·
          refine ⟨38354272390543039480762973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25569514927028692987175315 38354272390543039480762973)
          ·
            refine ⟨14382852146453639805286115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38354272390543039480762973 14382852146453639805286115)
            ·
              refine ⟨21574278219680459707929173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14382852146453639805286115 21574278219680459707929173)
              ·
                refine ⟨252823572886880387202295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 21574278219680459707929173 252823572886880387202295)
                ·
                  refine ⟨379235359330320580803443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 252823572886880387202295 379235359330320580803443)
                  ·
                    refine ⟨568853038995480871205165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 379235359330320580803443 568853038995480871205165)
                    ·
                      refine ⟨213319889623305326701937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 568853038995480871205165 213319889623305326701937)
                      ·
                        rfl

theorem cell23_415439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 1, 1, 3].length) (baseStart_415439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415439 prefixEnd_415439 := by exact prefixLift 415439
  have htrace : WordTrace (prefixWord ++ tailWord_415439) baseStart_415439 baseEnd_415439 := by
    simpa [prefixWord, tailWord_415439, baseEnd_415439] using wordTrace_append hprefix tailTrace_415439
  have hstable : (prefixWord ++ tailWord_415439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415439).length < 2 ^ (prefixWord ++ tailWord_415439).sum := by decide
  have hdescent : baseEnd_415439 < baseStart_415439 := by decide
  rcases family_descends (prefixWord ++ tailWord_415439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415446 : List Nat := [5, 2, 1, 3, 1, 1, 1, 3, 6]
def baseStart_415446 : Nat := 118140960795 + 415446 * 2 ^ 59
def prefixEnd_415446 : Nat := 4983230072969 + 3 ^ 40 * 415446 * 2
def baseEnd_415446 : Nat := 23702609331987422146045

theorem tailTrace_415446 : CollatzResearch.WordTrace tailWord_415446 prefixEnd_415446 23702609331987422146045 := by
  unfold tailWord_415446
  simp only [CollatzResearch.WordTrace]
  refine ⟨947035028307348085818137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10101706968611712915393461 947035028307348085818137)
  ·
    refine ⟨710276271230511064363603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 947035028307348085818137 710276271230511064363603)
    ·
      refine ⟨1065414406845766596545405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 710276271230511064363603 1065414406845766596545405)
      ·
        refine ⟨399530402567162473704527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1065414406845766596545405 399530402567162473704527)
        ·
          refine ⟨599295603850743710556791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399530402567162473704527 599295603850743710556791)
          ·
            refine ⟨898943405776115565835187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599295603850743710556791 898943405776115565835187)
            ·
              refine ⟨1348415108664173348752781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 898943405776115565835187 1348415108664173348752781)
              ·
                refine ⟨505655665749065005782293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1348415108664173348752781 505655665749065005782293)
                ·
                  refine ⟨23702609331987422146045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 505655665749065005782293 23702609331987422146045)
                  ·
                    rfl

theorem cell23_415446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_415446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415446 prefixEnd_415446 := by exact prefixLift 415446
  have htrace : WordTrace (prefixWord ++ tailWord_415446) baseStart_415446 baseEnd_415446 := by
    simpa [prefixWord, tailWord_415446, baseEnd_415446] using wordTrace_append hprefix tailTrace_415446
  have hstable : (prefixWord ++ tailWord_415446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415446).length < 2 ^ (prefixWord ++ tailWord_415446).sum := by decide
  have hdescent : baseEnd_415446 < baseStart_415446 := by decide
  rcases family_descends (prefixWord ++ tailWord_415446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415455 : List Nat := [1, 1, 2, 3, 2, 2, 2, 3, 1, 6]
def baseStart_415455 : Nat := 118140960795 + 415455 * 2 ^ 59
def prefixEnd_415455 : Nat := 4983230072969 + 3 ^ 40 * 415455 * 2
def baseEnd_415455 : Nat := 71109368437925754700621

theorem tailTrace_415455 : CollatzResearch.WordTrace tailWord_415455 prefixEnd_415455 71109368437925754700621 := by
  unfold tailWord_415455
  simp only [CollatzResearch.WordTrace]
  refine ⟨15152888709884963910167819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10101925806589975940111879 15152888709884963910167819)
  ·
    refine ⟨22729333064827445865251729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15152888709884963910167819 22729333064827445865251729)
    ·
      refine ⟨17046999798620584398938797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22729333064827445865251729 17046999798620584398938797)
      ·
        refine ⟨6392624924482719149602049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17046999798620584398938797 6392624924482719149602049)
        ·
          refine ⟨4794468693362039362201537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6392624924482719149602049 4794468693362039362201537)
          ·
            refine ⟨3595851520021529521651153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4794468693362039362201537 3595851520021529521651153)
            ·
              refine ⟨2696888640016147141238365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3595851520021529521651153 2696888640016147141238365)
              ·
                refine ⟨1011333240006055177964387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2696888640016147141238365 1011333240006055177964387)
                ·
                  refine ⟨1516999860009082766946581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1011333240006055177964387 1516999860009082766946581)
                  ·
                    refine ⟨71109368437925754700621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1516999860009082766946581 71109368437925754700621)
                    ·
                      rfl

theorem cell23_415455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 6].length) (baseStart_415455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415455 prefixEnd_415455 := by exact prefixLift 415455
  have htrace : WordTrace (prefixWord ++ tailWord_415455) baseStart_415455 baseEnd_415455 := by
    simpa [prefixWord, tailWord_415455, baseEnd_415455] using wordTrace_append hprefix tailTrace_415455
  have hstable : (prefixWord ++ tailWord_415455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415455).length < 2 ^ (prefixWord ++ tailWord_415455).sum := by decide
  have hdescent : baseEnd_415455 < baseStart_415455 := by decide
  rcases family_descends (prefixWord ++ tailWord_415455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415475 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 4]
def baseStart_415475 : Nat := 118140960795 + 415475 * 2 ^ 59
def prefixEnd_415475 : Nat := 4983230072969 + 3 ^ 40 * 415475 * 2
def baseEnd_415475 : Nat := 213338374926867185851771

theorem tailTrace_415475 : CollatzResearch.WordTrace tailWord_415475 prefixEnd_415475 213338374926867185851771 := by
  unfold tailWord_415475
  simp only [CollatzResearch.WordTrace]
  refine ⟨15153618169812507325895879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10102412113208338217263919 15153618169812507325895879)
  ·
    refine ⟨22730427254718760988843819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15153618169812507325895879 22730427254718760988843819)
    ·
      refine ⟨34095640882078141483265729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22730427254718760988843819 34095640882078141483265729)
      ·
        refine ⟨25571730661558606112449297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34095640882078141483265729 25571730661558606112449297)
        ·
          refine ⟨19178797996168954584336973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25571730661558606112449297 19178797996168954584336973)
          ·
            refine ⟨7192049248563357969126365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19178797996168954584336973 7192049248563357969126365)
            ·
              refine ⟨2697018468211259238422387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7192049248563357969126365 2697018468211259238422387)
              ·
                refine ⟨4045527702316888857633581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2697018468211259238422387 4045527702316888857633581)
                ·
                  refine ⟨1517072888368833321612593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4045527702316888857633581 1517072888368833321612593)
                  ·
                    refine ⟨1137804666276624991209445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1517072888368833321612593 1137804666276624991209445)
                    ·
                      refine ⟨213338374926867185851771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1137804666276624991209445 213338374926867185851771)
                      ·
                        rfl

theorem cell23_415475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 4].length) (baseStart_415475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415475 prefixEnd_415475 := by exact prefixLift 415475
  have htrace : WordTrace (prefixWord ++ tailWord_415475) baseStart_415475 baseEnd_415475 := by
    simpa [prefixWord, tailWord_415475, baseEnd_415475] using wordTrace_append hprefix tailTrace_415475
  have hstable : (prefixWord ++ tailWord_415475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415475).length < 2 ^ (prefixWord ++ tailWord_415475).sum := by decide
  have hdescent : baseEnd_415475 < baseStart_415475 := by decide
  rcases family_descends (prefixWord ++ tailWord_415475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415506 : List Nat := [3, 2, 4, 1, 1, 1, 2, 3, 2, 4]
def baseStart_415506 : Nat := 118140960795 + 415506 * 2 ^ 59
def prefixEnd_415506 : Nat := 4983230072969 + 3 ^ 40 * 415506 * 2
def baseEnd_415506 : Nat := 71118097609052188188043

theorem tailTrace_415506 : CollatzResearch.WordTrace tailWord_415506 prefixEnd_415506 71118097609052188188043 := by
  unfold tailWord_415506
  simp only [CollatzResearch.WordTrace]
  refine ⟨3788687208175049905068593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10103165888466799746849581 3788687208175049905068593)
  ·
    refine ⟨2841515406131287428801445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3788687208175049905068593 2841515406131287428801445)
    ·
      refine ⟨532784138649616392900271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2841515406131287428801445 532784138649616392900271)
      ·
        refine ⟨799176207974424589350407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532784138649616392900271 799176207974424589350407)
        ·
          refine ⟨1198764311961636884025611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 799176207974424589350407 1198764311961636884025611)
          ·
            refine ⟨1798146467942455326038417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1198764311961636884025611 1798146467942455326038417)
            ·
              refine ⟨1348609850956841494528813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1798146467942455326038417 1348609850956841494528813)
              ·
                refine ⟨505728694108815560448305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1348609850956841494528813 505728694108815560448305)
                ·
                  refine ⟨379296520581611670336229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 505728694108815560448305 379296520581611670336229)
                  ·
                    refine ⟨71118097609052188188043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 379296520581611670336229 71118097609052188188043)
                    ·
                      rfl

theorem cell23_415506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_415506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415506 prefixEnd_415506 := by exact prefixLift 415506
  have htrace : WordTrace (prefixWord ++ tailWord_415506) baseStart_415506 baseEnd_415506 := by
    simpa [prefixWord, tailWord_415506, baseEnd_415506] using wordTrace_append hprefix tailTrace_415506
  have hstable : (prefixWord ++ tailWord_415506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415506).length < 2 ^ (prefixWord ++ tailWord_415506).sum := by decide
  have hdescent : baseEnd_415506 < baseStart_415506 := by decide
  rcases family_descends (prefixWord ++ tailWord_415506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415512 : List Nat := [2, 1, 2, 3, 1, 1, 3, 3, 1, 3, 3]
def baseStart_415512 : Nat := 118140960795 + 415512 * 2 ^ 59
def prefixEnd_415512 : Nat := 4983230072969 + 3 ^ 40 * 415512 * 2
def baseEnd_415512 : Nat := 213357373711083541089101

theorem tailTrace_415512 : CollatzResearch.WordTrace tailWord_415512 prefixEnd_415512 213357373711083541089101 := by
  unfold tailWord_415512
  simp only [CollatzResearch.WordTrace]
  refine ⟨7577483835339231322496395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10103311780452308429995193 7577483835339231322496395)
  ·
    refine ⟨11366225753008846983744593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7577483835339231322496395 11366225753008846983744593)
    ·
      refine ⟨8524669314756635237808445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11366225753008846983744593 8524669314756635237808445)
      ·
        refine ⟨3196750993033738214178167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8524669314756635237808445 3196750993033738214178167)
        ·
          refine ⟨4795126489550607321267251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3196750993033738214178167 4795126489550607321267251)
          ·
            refine ⟨7192689734325910981900877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4795126489550607321267251 7192689734325910981900877)
            ·
              refine ⟨2697258650372216618212829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7192689734325910981900877 2697258650372216618212829)
              ·
                refine ⟨1011471993889581231829811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2697258650372216618212829 1011471993889581231829811)
                ·
                  refine ⟨1517207990834371847744717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1011471993889581231829811 1517207990834371847744717)
                  ·
                    refine ⟨568952996562889442904269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1517207990834371847744717 568952996562889442904269)
                    ·
                      refine ⟨213357373711083541089101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 568952996562889442904269 213357373711083541089101)
                      ·
                        rfl

theorem cell23_415512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_415512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415512 prefixEnd_415512 := by exact prefixLift 415512
  have htrace : WordTrace (prefixWord ++ tailWord_415512) baseStart_415512 baseEnd_415512 := by
    simpa [prefixWord, tailWord_415512, baseEnd_415512] using wordTrace_append hprefix tailTrace_415512
  have hstable : (prefixWord ++ tailWord_415512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415512).length < 2 ^ (prefixWord ++ tailWord_415512).sum := by decide
  have hdescent : baseEnd_415512 < baseStart_415512 := by decide
  rcases family_descends (prefixWord ++ tailWord_415512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415535 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 4]
def baseStart_415535 : Nat := 118140960795 + 415535 * 2 ^ 59
def prefixEnd_415535 : Nat := 4983230072969 + 3 ^ 40 * 415535 * 2
def baseEnd_415535 : Nat := 213369183766136951101495

theorem tailTrace_415535 : CollatzResearch.WordTrace tailWord_415535 prefixEnd_415535 213369183766136951101495 := by
  unfold tailWord_415535
  simp only [CollatzResearch.WordTrace]
  refine ⟨15155806549595137573080059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10103871033063425048720039 15155806549595137573080059)
  ·
    refine ⟨22733709824392706359620089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15155806549595137573080059 22733709824392706359620089)
    ·
      refine ⟨17050282368294529769715067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22733709824392706359620089 17050282368294529769715067)
      ·
        refine ⟨25575423552441794654572601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17050282368294529769715067 25575423552441794654572601)
        ·
          refine ⟨19181567664331345990929451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25575423552441794654572601 19181567664331345990929451)
          ·
            refine ⟨28772351496497018986394177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19181567664331345990929451 28772351496497018986394177)
            ·
              refine ⟨21579263622372764239795633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28772351496497018986394177 21579263622372764239795633)
              ·
                refine ⟨16184447716779573179846725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21579263622372764239795633 16184447716779573179846725)
                ·
                  refine ⟨3034583946896169971221261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16184447716779573179846725 3034583946896169971221261)
                  ·
                    refine ⟨1137968980086063739207973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3034583946896169971221261 1137968980086063739207973)
                    ·
                      refine ⟨213369183766136951101495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1137968980086063739207973 213369183766136951101495)
                      ·
                        rfl

theorem cell23_415535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 4].length) (baseStart_415535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415535 prefixEnd_415535 := by exact prefixLift 415535
  have htrace : WordTrace (prefixWord ++ tailWord_415535) baseStart_415535 baseEnd_415535 := by
    simpa [prefixWord, tailWord_415535, baseEnd_415535] using wordTrace_append hprefix tailTrace_415535
  have hstable : (prefixWord ++ tailWord_415535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415535).length < 2 ^ (prefixWord ++ tailWord_415535).sum := by decide
  have hdescent : baseEnd_415535 < baseStart_415535 := by decide
  rcases family_descends (prefixWord ++ tailWord_415535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415546 : List Nat := [3, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3]
def baseStart_415546 : Nat := 118140960795 + 415546 * 2 ^ 59
def prefixEnd_415546 : Nat := 4983230072969 + 3 ^ 40 * 415546 * 2
def baseEnd_415546 : Nat := 213374832053336408063945

theorem tailTrace_415546 : CollatzResearch.WordTrace tailWord_415546 prefixEnd_415546 213374832053336408063945 := by
  unfold tailWord_415546
  simp only [CollatzResearch.WordTrace]
  refine ⟨3789051938138821612932623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10104138501703524301153661 3789051938138821612932623)
  ·
    refine ⟨5683577907208232419398935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3789051938138821612932623 5683577907208232419398935)
    ·
      refine ⟨8525366860812348629098403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5683577907208232419398935 8525366860812348629098403)
      ·
        refine ⟨12788050291218522943647605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8525366860812348629098403 12788050291218522943647605)
        ·
          refine ⟨1198879714801736525966963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12788050291218522943647605 1198879714801736525966963)
          ·
            refine ⟨1798319572202604788950445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1198879714801736525966963 1798319572202604788950445)
            ·
              refine ⟨674369839575976795856417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1798319572202604788950445 674369839575976795856417)
              ·
                refine ⟨505777379681982596892313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 674369839575976795856417 505777379681982596892313)
                ·
                  refine ⟨379333034761486947669235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 505777379681982596892313 379333034761486947669235)
                  ·
                    refine ⟨568999552142230421503853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 379333034761486947669235 568999552142230421503853)
                    ·
                      refine ⟨213374832053336408063945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 568999552142230421503853 213374832053336408063945)
                      ·
                        rfl

theorem cell23_415546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3].length) (baseStart_415546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415546 prefixEnd_415546 := by exact prefixLift 415546
  have htrace : WordTrace (prefixWord ++ tailWord_415546) baseStart_415546 baseEnd_415546 := by
    simpa [prefixWord, tailWord_415546, baseEnd_415546] using wordTrace_append hprefix tailTrace_415546
  have hstable : (prefixWord ++ tailWord_415546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415546).length < 2 ^ (prefixWord ++ tailWord_415546).sum := by decide
  have hdescent : baseEnd_415546 < baseStart_415546 := by decide
  rcases family_descends (prefixWord ++ tailWord_415546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415552 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 2, 8, 2]
def baseStart_415552 : Nat := 118140960795 + 415552 * 2 ^ 59
def prefixEnd_415552 : Nat := 4983230072969 + 3 ^ 40 * 415552 * 2
def baseEnd_415552 : Nat := 213377912937263384588917

theorem tailTrace_415552 : CollatzResearch.WordTrace tailWord_415552 prefixEnd_415552 213377912937263384588917 := by
  unfold tailWord_415552
  simp only [CollatzResearch.WordTrace]
  refine ⟨7578213295266774738224455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10104284393689032984299273 7578213295266774738224455)
  ·
    refine ⟨11367319942900162107336683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7578213295266774738224455 11367319942900162107336683)
    ·
      refine ⟨17050979914350243161005025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11367319942900162107336683 17050979914350243161005025)
      ·
        refine ⟨12788234935762682370753769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17050979914350243161005025 12788234935762682370753769)
        ·
          refine ⟨9591176201822011778065327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12788234935762682370753769 9591176201822011778065327)
          ·
            refine ⟨14386764302733017667097991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9591176201822011778065327 14386764302733017667097991)
            ·
              refine ⟨21580146454099526500646987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14386764302733017667097991 21580146454099526500646987)
              ·
                refine ⟨32370219681149289750970481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21580146454099526500646987 32370219681149289750970481)
                ·
                  refine ⟨24277664760861967313227861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32370219681149289750970481 24277664760861967313227861)
                  ·
                    refine ⟨284503883916351179451889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24277664760861967313227861 284503883916351179451889)
                    ·
                      refine ⟨213377912937263384588917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 284503883916351179451889 213377912937263384588917)
                      ·
                        rfl

theorem cell23_415552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 8, 2].length) (baseStart_415552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415552 prefixEnd_415552 := by exact prefixLift 415552
  have htrace : WordTrace (prefixWord ++ tailWord_415552) baseStart_415552 baseEnd_415552 := by
    simpa [prefixWord, tailWord_415552, baseEnd_415552] using wordTrace_append hprefix tailTrace_415552
  have hstable : (prefixWord ++ tailWord_415552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415552).length < 2 ^ (prefixWord ++ tailWord_415552).sum := by decide
  have hdescent : baseEnd_415552 < baseStart_415552 := by decide
  rcases family_descends (prefixWord ++ tailWord_415552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415639 : List Nat := [1, 1, 3, 3, 1, 4, 2, 1, 2, 5]
def baseStart_415639 : Nat := 118140960795 + 415639 * 2 ^ 59
def prefixEnd_415639 : Nat := 4983230072969 + 3 ^ 40 * 415639 * 2
def baseEnd_415639 : Nat := 71140861918068181400339

theorem tailTrace_415639 : CollatzResearch.WordTrace tailWord_415639 prefixEnd_415639 71140861918068181400339 := by
  unfold tailWord_415639
  simp only [CollatzResearch.WordTrace]
  refine ⟨15159599741218363334865971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10106399827478908889910647 15159599741218363334865971)
  ·
    refine ⟨22739399611827545002298957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15159599741218363334865971 22739399611827545002298957)
    ·
      refine ⟨8527274854435329375862109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22739399611827545002298957 8527274854435329375862109)
      ·
        refine ⟨3197728070413248515948291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8527274854435329375862109 3197728070413248515948291)
        ·
          refine ⟨4796592105619872773922437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3197728070413248515948291 4796592105619872773922437)
          ·
            refine ⟨899361019803726145110457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4796592105619872773922437 899361019803726145110457)
            ·
              refine ⟨674520764852794608832843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899361019803726145110457 674520764852794608832843)
              ·
                refine ⟨1011781147279191913249265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674520764852794608832843 1011781147279191913249265)
                ·
                  refine ⟨758835860459393934936949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1011781147279191913249265 758835860459393934936949)
                  ·
                    refine ⟨71140861918068181400339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 758835860459393934936949 71140861918068181400339)
                    ·
                      rfl

theorem cell23_415639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 5].length) (baseStart_415639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415639 prefixEnd_415639 := by exact prefixLift 415639
  have htrace : WordTrace (prefixWord ++ tailWord_415639) baseStart_415639 baseEnd_415639 := by
    simpa [prefixWord, tailWord_415639, baseEnd_415639] using wordTrace_append hprefix tailTrace_415639
  have hstable : (prefixWord ++ tailWord_415639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415639).length < 2 ^ (prefixWord ++ tailWord_415639).sum := by decide
  have hdescent : baseEnd_415639 < baseStart_415639 := by decide
  rcases family_descends (prefixWord ++ tailWord_415639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415769 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 5, 2, 3]
def baseStart_415769 : Nat := 118140960795 + 415769 * 2 ^ 59
def prefixEnd_415769 : Nat := 4983230072969 + 3 ^ 40 * 415769 * 2
def baseEnd_415769 : Nat := 213489338239289035575419

theorem tailTrace_415769 : CollatzResearch.WordTrace tailWord_415769 prefixEnd_415769 213489338239289035575419 := by
  unfold tailWord_415769
  simp only [CollatzResearch.WordTrace]
  refine ⟨15164341230747395537098361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10109560820498263691398907 15164341230747395537098361)
  ·
    refine ⟨11373255923060546652823771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15164341230747395537098361 11373255923060546652823771)
    ·
      refine ⟨17059883884590819979235657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11373255923060546652823771 17059883884590819979235657)
      ·
        refine ⟨12794912913443114984426743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17059883884590819979235657 12794912913443114984426743)
        ·
          refine ⟨19192369370164672476640115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12794912913443114984426743 19192369370164672476640115)
          ·
            refine ⟨28788554055247008714960173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19192369370164672476640115 28788554055247008714960173)
            ·
              refine ⟨10795707770717628268110065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28788554055247008714960173 10795707770717628268110065)
              ·
                refine ⟨8096780828038221201082549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10795707770717628268110065 8096780828038221201082549)
                ·
                  refine ⟨759073202628583237601489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8096780828038221201082549 759073202628583237601489)
                  ·
                    refine ⟨569304901971437428201117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 759073202628583237601489 569304901971437428201117)
                    ·
                      refine ⟨213489338239289035575419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 569304901971437428201117 213489338239289035575419)
                      ·
                        rfl

theorem cell23_415769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 2, 3].length) (baseStart_415769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415769 prefixEnd_415769 := by exact prefixLift 415769
  have htrace : WordTrace (prefixWord ++ tailWord_415769) baseStart_415769 baseEnd_415769 := by
    simpa [prefixWord, tailWord_415769, baseEnd_415769] using wordTrace_append hprefix tailTrace_415769
  have hstable : (prefixWord ++ tailWord_415769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415769).length < 2 ^ (prefixWord ++ tailWord_415769).sum := by decide
  have hdescent : baseEnd_415769 < baseStart_415769 := by decide
  rcases family_descends (prefixWord ++ tailWord_415769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415777 : List Nat := [1, 2, 3, 2, 4, 1, 3, 2, 1, 1, 3]
def baseStart_415777 : Nat := 118140960795 + 415777 * 2 ^ 59
def prefixEnd_415777 : Nat := 4983230072969 + 3 ^ 40 * 415777 * 2
def baseEnd_415777 : Nat := 213493446084525004275383

theorem tailTrace_415777 : CollatzResearch.WordTrace tailWord_415777 prefixEnd_415777 213493446084525004275383 := by
  unfold tailWord_415777
  simp only [CollatzResearch.WordTrace]
  refine ⟨15164633014718412903389585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10109755343145608602259723 15164633014718412903389585)
  ·
    refine ⟨11373474761038809677542189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15164633014718412903389585 11373474761038809677542189)
    ·
      refine ⟨4265053035389553629078321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11373474761038809677542189 4265053035389553629078321)
      ·
        refine ⟨3198789776542165221808741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4265053035389553629078321 3198789776542165221808741)
        ·
          refine ⟨599773083101655979089139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3198789776542165221808741 599773083101655979089139)
          ·
            refine ⟨899659624652483968633709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599773083101655979089139 899659624652483968633709)
            ·
              refine ⟨337372359244681488237641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 899659624652483968633709 337372359244681488237641)
              ·
                refine ⟨253029269433511116178231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337372359244681488237641 253029269433511116178231)
                ·
                  refine ⟨379543904150266674267347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 253029269433511116178231 379543904150266674267347)
                  ·
                    refine ⟨569315856225400011401021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 379543904150266674267347 569315856225400011401021)
                    ·
                      refine ⟨213493446084525004275383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 569315856225400011401021 213493446084525004275383)
                      ·
                        rfl

theorem cell23_415777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_415777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415777 prefixEnd_415777 := by exact prefixLift 415777
  have htrace : WordTrace (prefixWord ++ tailWord_415777) baseStart_415777 baseEnd_415777 := by
    simpa [prefixWord, tailWord_415777, baseEnd_415777] using wordTrace_append hprefix tailTrace_415777
  have hstable : (prefixWord ++ tailWord_415777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415777).length < 2 ^ (prefixWord ++ tailWord_415777).sum := by decide
  have hdescent : baseEnd_415777 < baseStart_415777 := by decide
  rcases family_descends (prefixWord ++ tailWord_415777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415786 : List Nat := [3, 1, 4, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_415786 : Nat := 118140960795 + 415786 * 2 ^ 59
def prefixEnd_415786 : Nat := 4983230072969 + 3 ^ 40 * 415786 * 2
def baseEnd_415786 : Nat := 213498067410415469062841

theorem tailTrace_415786 : CollatzResearch.WordTrace tailWord_415786 prefixEnd_415786 213498067410415469062841 := by
  unfold tailWord_415786
  simp only [CollatzResearch.WordTrace]
  refine ⟨3791240317921451860116803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10109974181123871626978141 3791240317921451860116803)
  ·
    refine ⟨5686860476882177790175205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3791240317921451860116803 5686860476882177790175205)
    ·
      refine ⟨1066286339415408335657851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5686860476882177790175205 1066286339415408335657851)
      ·
        refine ⟨1599429509123112503486777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1066286339415408335657851 1599429509123112503486777)
        ·
          refine ⟨1199572131842334377615083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1599429509123112503486777 1199572131842334377615083)
          ·
            refine ⟨1799358197763501566422625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1199572131842334377615083 1799358197763501566422625)
            ·
              refine ⟨1349518648322626174816969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1799358197763501566422625 1349518648322626174816969)
              ·
                refine ⟨1012138986241969631112727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1349518648322626174816969 1012138986241969631112727)
                ·
                  refine ⟨1518208479362954446669091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1012138986241969631112727 1518208479362954446669091)
                  ·
                    refine ⟨2277312719044431670003637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1518208479362954446669091 2277312719044431670003637)
                    ·
                      refine ⟨213498067410415469062841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2277312719044431670003637 213498067410415469062841)
                      ·
                        rfl

theorem cell23_415786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_415786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415786 prefixEnd_415786 := by exact prefixLift 415786
  have htrace : WordTrace (prefixWord ++ tailWord_415786) baseStart_415786 baseEnd_415786 := by
    simpa [prefixWord, tailWord_415786, baseEnd_415786] using wordTrace_append hprefix tailTrace_415786
  have hstable : (prefixWord ++ tailWord_415786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415786).length < 2 ^ (prefixWord ++ tailWord_415786).sum := by decide
  have hdescent : baseEnd_415786 < baseStart_415786 := by decide
  rcases family_descends (prefixWord ++ tailWord_415786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415793 : List Nat := [1, 2, 2, 3, 1, 3, 4, 1, 2, 4]
def baseStart_415793 : Nat := 118140960795 + 415793 * 2 ^ 59
def prefixEnd_415793 : Nat := 4983230072969 + 3 ^ 40 * 415793 * 2
def baseEnd_415793 : Nat := 71167220591665647225103

theorem tailTrace_415793 : CollatzResearch.WordTrace tailWord_415793 prefixEnd_415793 71167220591665647225103 := by
  unfold tailWord_415793
  simp only [CollatzResearch.WordTrace]
  refine ⟨15165216582660447635972033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10110144388440298423981355 15165216582660447635972033)
  ·
    refine ⟨11373912436995335726979025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15165216582660447635972033 11373912436995335726979025)
    ·
      refine ⟨8530434327746501795234269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11373912436995335726979025 8530434327746501795234269)
      ·
        refine ⟨3198912872904938173212851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8530434327746501795234269 3198912872904938173212851)
        ·
          refine ⟨4798369309357407259819277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3198912872904938173212851 4798369309357407259819277)
          ·
            refine ⟨1799388491009027722432229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4798369309357407259819277 1799388491009027722432229)
            ·
              refine ⟨337385342064192697956043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1799388491009027722432229 337385342064192697956043)
              ·
                refine ⟨506078013096289046934065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 337385342064192697956043 506078013096289046934065)
                ·
                  refine ⟨379558509822216785200549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 506078013096289046934065 379558509822216785200549)
                  ·
                    refine ⟨71167220591665647225103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 379558509822216785200549 71167220591665647225103)
                    ·
                      rfl

theorem cell23_415793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 2, 4].length) (baseStart_415793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415793 prefixEnd_415793 := by exact prefixLift 415793
  have htrace : WordTrace (prefixWord ++ tailWord_415793) baseStart_415793 baseEnd_415793 := by
    simpa [prefixWord, tailWord_415793, baseEnd_415793] using wordTrace_append hprefix tailTrace_415793
  have hstable : (prefixWord ++ tailWord_415793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415793).length < 2 ^ (prefixWord ++ tailWord_415793).sum := by decide
  have hdescent : baseEnd_415793 < baseStart_415793 := by decide
  rcases family_descends (prefixWord ++ tailWord_415793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415800 : List Nat := [2, 1, 2, 1, 7, 1, 1, 2, 1, 1, 4]
def baseStart_415800 : Nat := 118140960795 + 415800 * 2 ^ 59
def prefixEnd_415800 : Nat := 4983230072969 + 3 ^ 40 * 415800 * 2
def baseEnd_415800 : Nat := 213505256139578414287777

theorem tailTrace_415800 : CollatzResearch.WordTrace tailWord_415800 prefixEnd_415800 213505256139578414287777 := by
  unfold tailWord_415800
  simp only [CollatzResearch.WordTrace]
  refine ⟨7582735946817543915738427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10110314595756725220984569 7582735946817543915738427)
  ·
    refine ⟨11374103920226315873607641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7582735946817543915738427 11374103920226315873607641)
    ·
      refine ⟨8530577940169736905205731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11374103920226315873607641 8530577940169736905205731)
      ·
        refine ⟨12795866910254605357808597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8530577940169736905205731 12795866910254605357808597)
        ·
          refine ⟨299903130709092313073639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 12795866910254605357808597 299903130709092313073639)
          ·
            refine ⟨449854696063638469610459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299903130709092313073639 449854696063638469610459)
            ·
              refine ⟨674782044095457704415689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449854696063638469610459 674782044095457704415689)
              ·
                refine ⟨506086533071593278311767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 674782044095457704415689 506086533071593278311767)
                ·
                  refine ⟨759129799607389917467651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 506086533071593278311767 759129799607389917467651)
                  ·
                    refine ⟨1138694699411084876201477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 759129799607389917467651 1138694699411084876201477)
                    ·
                      refine ⟨213505256139578414287777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1138694699411084876201477 213505256139578414287777)
                      ·
                        rfl

theorem cell23_415800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 1, 1, 4].length) (baseStart_415800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415800 prefixEnd_415800 := by exact prefixLift 415800
  have htrace : WordTrace (prefixWord ++ tailWord_415800) baseStart_415800 baseEnd_415800 := by
    simpa [prefixWord, tailWord_415800, baseEnd_415800] using wordTrace_append hprefix tailTrace_415800
  have hstable : (prefixWord ++ tailWord_415800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415800).length < 2 ^ (prefixWord ++ tailWord_415800).sum := by decide
  have hdescent : baseEnd_415800 < baseStart_415800 := by decide
  rcases family_descends (prefixWord ++ tailWord_415800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415816 : List Nat := [2, 1, 3, 1, 1, 1, 2, 4, 4, 1, 3]
def baseStart_415816 : Nat := 118140960795 + 415816 * 2 ^ 59
def prefixEnd_415816 : Nat := 4983230072969 + 3 ^ 40 * 415816 * 2
def baseEnd_415816 : Nat := 213513471830050351687703

theorem tailTrace_415816 : CollatzResearch.WordTrace tailWord_415816 prefixEnd_415816 213513471830050351687703 := by
  unfold tailWord_415816
  simp only [CollatzResearch.WordTrace]
  refine ⟨7583027730788561282029651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10110703641051415042706201 7583027730788561282029651)
  ·
    refine ⟨11374541596182841923044477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7583027730788561282029651 11374541596182841923044477)
    ·
      refine ⟨4265453098568565721141679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11374541596182841923044477 4265453098568565721141679)
      ·
        refine ⟨6398179647852848581712519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4265453098568565721141679 6398179647852848581712519)
        ·
          refine ⟨9597269471779272872568779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6398179647852848581712519 9597269471779272872568779)
          ·
            refine ⟨14395904207668909308853169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9597269471779272872568779 14395904207668909308853169)
            ·
              refine ⟨10796928155751681981639877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14395904207668909308853169 10796928155751681981639877)
              ·
                refine ⟨2024424029203440371557477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10796928155751681981639877 2024424029203440371557477)
                ·
                  refine ⟨379579505475645069667027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2024424029203440371557477 379579505475645069667027)
                  ·
                    refine ⟨569369258213467604500541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 379579505475645069667027 569369258213467604500541)
                    ·
                      refine ⟨213513471830050351687703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 569369258213467604500541 213513471830050351687703)
                      ·
                        rfl

theorem cell23_415816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_415816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415816 prefixEnd_415816 := by exact prefixLift 415816
  have htrace : WordTrace (prefixWord ++ tailWord_415816) baseStart_415816 baseEnd_415816 := by
    simpa [prefixWord, tailWord_415816, baseEnd_415816] using wordTrace_append hprefix tailTrace_415816
  have hstable : (prefixWord ++ tailWord_415816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415816).length < 2 ^ (prefixWord ++ tailWord_415816).sum := by decide
  have hdescent : baseEnd_415816 < baseStart_415816 := by decide
  rcases family_descends (prefixWord ++ tailWord_415816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415833 : List Nat := [1, 2, 1, 2, 2, 1, 6, 2, 2, 1, 3]
def baseStart_415833 : Nat := 118140960795 + 415833 * 2 ^ 59
def prefixEnd_415833 : Nat := 4983230072969 + 3 ^ 40 * 415833 * 2
def baseEnd_415833 : Nat := 213522201001176785175125

theorem tailTrace_415833 : CollatzResearch.WordTrace tailWord_415833 prefixEnd_415833 213522201001176785175125 := by
  unfold tailWord_415833
  simp only [CollatzResearch.WordTrace]
  refine ⟨15166675502515534467428153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10111117001677022978285435 15166675502515534467428153)
  ·
    refine ⟨11375006626886650850571115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15166675502515534467428153 11375006626886650850571115)
    ·
      refine ⟨17062509940329976275856673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11375006626886650850571115 17062509940329976275856673)
      ·
        refine ⟨12796882455247482206892505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17062509940329976275856673 12796882455247482206892505)
        ·
          refine ⟨9597661841435611655169379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12796882455247482206892505 9597661841435611655169379)
          ·
            refine ⟨14396492762153417482754069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9597661841435611655169379 14396492762153417482754069)
            ·
              refine ⟨674835598225941444504097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14396492762153417482754069 674835598225941444504097)
              ·
                refine ⟨506126698669456083378073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 674835598225941444504097 506126698669456083378073)
                ·
                  refine ⟨379595024002092062533555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 506126698669456083378073 379595024002092062533555)
                  ·
                    refine ⟨569392536003138093800333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 379595024002092062533555 569392536003138093800333)
                    ·
                      refine ⟨213522201001176785175125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 569392536003138093800333 213522201001176785175125)
                      ·
                        rfl

theorem cell23_415833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 1, 3].length) (baseStart_415833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415833 prefixEnd_415833 := by exact prefixLift 415833
  have htrace : WordTrace (prefixWord ++ tailWord_415833) baseStart_415833 baseEnd_415833 := by
    simpa [prefixWord, tailWord_415833, baseEnd_415833] using wordTrace_append hprefix tailTrace_415833
  have hstable : (prefixWord ++ tailWord_415833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415833).length < 2 ^ (prefixWord ++ tailWord_415833).sum := by decide
  have hdescent : baseEnd_415833 < baseStart_415833 := by decide
  rcases family_descends (prefixWord ++ tailWord_415833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415849 : List Nat := [1, 2, 1, 1, 1, 5, 3, 1, 2, 6]
def baseStart_415849 : Nat := 118140960795 + 415849 * 2 ^ 59
def prefixEnd_415849 : Nat := 4983230072969 + 3 ^ 40 * 415849 * 2
def baseEnd_415849 : Nat := 71176805563882907525017

theorem tailTrace_415849 : CollatzResearch.WordTrace tailWord_415849 prefixEnd_415849 71176805563882907525017 := by
  unfold tailWord_415849
  simp only [CollatzResearch.WordTrace]
  refine ⟨15167259070457569200010601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10111506046971712800007067 15167259070457569200010601)
  ·
    refine ⟨11375444302843176900007951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15167259070457569200010601 11375444302843176900007951)
    ·
      refine ⟨17063166454264765350011927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11375444302843176900007951 17063166454264765350011927)
      ·
        refine ⟨25594749681397148025017891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17063166454264765350011927 25594749681397148025017891)
        ·
          refine ⟨38392124522095722037526837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25594749681397148025017891 38392124522095722037526837)
          ·
            refine ⟨3599261673946473941018141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38392124522095722037526837 3599261673946473941018141)
            ·
              refine ⟨1349723127729927727881803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3599261673946473941018141 1349723127729927727881803)
              ·
                refine ⟨2024584691594891591822705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1349723127729927727881803 2024584691594891591822705)
                ·
                  refine ⟨1518438518696168693867029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2024584691594891591822705 1518438518696168693867029)
                  ·
                    refine ⟨71176805563882907525017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1518438518696168693867029 71176805563882907525017)
                    ·
                      rfl

theorem cell23_415849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 6].length) (baseStart_415849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415849 prefixEnd_415849 := by exact prefixLift 415849
  have htrace : WordTrace (prefixWord ++ tailWord_415849) baseStart_415849 baseEnd_415849 := by
    simpa [prefixWord, tailWord_415849, baseEnd_415849] using wordTrace_append hprefix tailTrace_415849
  have hstable : (prefixWord ++ tailWord_415849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415849).length < 2 ^ (prefixWord ++ tailWord_415849).sum := by decide
  have hdescent : baseEnd_415849 < baseStart_415849 := by decide
  rcases family_descends (prefixWord ++ tailWord_415849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415877 : List Nat := [1, 3, 1, 1, 5, 3, 2, 1, 1, 3, 2]
def baseStart_415877 : Nat := 118140960795 + 415877 * 2 ^ 59
def prefixEnd_415877 : Nat := 4983230072969 + 3 ^ 40 * 415877 * 2
def baseEnd_415877 : Nat := 213544794149974613024923

theorem tailTrace_415877 : CollatzResearch.WordTrace tailWord_415877 prefixEnd_415877 213544794149974613024923 := by
  unfold tailWord_415877
  simp only [CollatzResearch.WordTrace]
  refine ⟨15168280314356129982029885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10112186876237419988019923 15168280314356129982029885)
  ·
    refine ⟨5688105117883548743261207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15168280314356129982029885 5688105117883548743261207)
    ·
      refine ⟨8532157676825323114891811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5688105117883548743261207 8532157676825323114891811)
      ·
        refine ⟨12798236515237984672337717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8532157676825323114891811 12798236515237984672337717)
        ·
          refine ⟨1199834673303561063031661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12798236515237984672337717 1199834673303561063031661)
          ·
            refine ⟨449938002488835398636873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1199834673303561063031661 449938002488835398636873)
            ·
              refine ⟨337453501866626548977655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449938002488835398636873 337453501866626548977655)
              ·
                refine ⟨506180252799939823466483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 337453501866626548977655 506180252799939823466483)
                ·
                  refine ⟨759270379199909735199725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 506180252799939823466483 759270379199909735199725)
                  ·
                    refine ⟨284726392199966150699897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 759270379199909735199725 284726392199966150699897)
                    ·
                      refine ⟨213544794149974613024923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 284726392199966150699897 213544794149974613024923)
                      ·
                        rfl

theorem cell23_415877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 1, 3, 2].length) (baseStart_415877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415877 prefixEnd_415877 := by exact prefixLift 415877
  have htrace : WordTrace (prefixWord ++ tailWord_415877) baseStart_415877 baseEnd_415877 := by
    simpa [prefixWord, tailWord_415877, baseEnd_415877] using wordTrace_append hprefix tailTrace_415877
  have hstable : (prefixWord ++ tailWord_415877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415877).length < 2 ^ (prefixWord ++ tailWord_415877).sum := by decide
  have hdescent : baseEnd_415877 < baseStart_415877 := by decide
  rcases family_descends (prefixWord ++ tailWord_415877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415890 : List Nat := [3, 2, 3, 1, 1, 1, 3, 1, 4, 2, 2]
def baseStart_415890 : Nat := 118140960795 + 415890 * 2 ^ 59
def prefixEnd_415890 : Nat := 4983230072969 + 3 ^ 40 * 415890 * 2
def baseEnd_415890 : Nat := 213551469398483062162363

theorem tailTrace_415890 : CollatzResearch.WordTrace tailWord_415890 prefixEnd_415890 213551469398483062162363 := by
  unfold tailWord_415890
  simp only [CollatzResearch.WordTrace]
  refine ⟨3792188615827258300563281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10112502975539355468168749 3792188615827258300563281)
  ·
    refine ⟨2844141461870443725422461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3792188615827258300563281 2844141461870443725422461)
    ·
      refine ⟨1066553048201416397033423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2844141461870443725422461 1066553048201416397033423)
      ·
        refine ⟨1599829572302124595550135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1066553048201416397033423 1599829572302124595550135)
        ·
          refine ⟨2399744358453186893325203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599829572302124595550135 2399744358453186893325203)
          ·
            refine ⟨3599616537679780339987805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2399744358453186893325203 3599616537679780339987805)
            ·
              refine ⟨1349856201629917627495427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3599616537679780339987805 1349856201629917627495427)
              ·
                refine ⟨2024784302444876441243141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1349856201629917627495427 2024784302444876441243141)
                ·
                  refine ⟨379647056708414332733089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2024784302444876441243141 379647056708414332733089)
                  ·
                    refine ⟨284735292531310749549817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 379647056708414332733089 284735292531310749549817)
                    ·
                      refine ⟨213551469398483062162363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 284735292531310749549817 213551469398483062162363)
                      ·
                        rfl

theorem cell23_415890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_415890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415890 prefixEnd_415890 := by exact prefixLift 415890
  have htrace : WordTrace (prefixWord ++ tailWord_415890) baseStart_415890 baseEnd_415890 := by
    simpa [prefixWord, tailWord_415890, baseEnd_415890] using wordTrace_append hprefix tailTrace_415890
  have hstable : (prefixWord ++ tailWord_415890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415890).length < 2 ^ (prefixWord ++ tailWord_415890).sum := by decide
  have hdescent : baseEnd_415890 < baseStart_415890 := by decide
  rcases family_descends (prefixWord ++ tailWord_415890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415909 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 3, 7]
def baseStart_415909 : Nat := 118140960795 + 415909 * 2 ^ 59
def prefixEnd_415909 : Nat := 4983230072969 + 3 ^ 40 * 415909 * 2
def baseEnd_415909 : Nat := 71187075176972829274925

theorem tailTrace_415909 : CollatzResearch.WordTrace tailWord_415909 prefixEnd_415909 71187075176972829274925 := by
  unfold tailWord_415909
  simp only [CollatzResearch.WordTrace]
  refine ⟨15169447450240199447194781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10112964966826799631463187 15169447450240199447194781)
  ·
    refine ⟨5688542793840074792698043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15169447450240199447194781 5688542793840074792698043)
    ·
      refine ⟨8532814190760112189047065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5688542793840074792698043 8532814190760112189047065)
      ·
        refine ⟨6399610643070084141785299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8532814190760112189047065 6399610643070084141785299)
        ·
          refine ⟨9599415964605126212677949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6399610643070084141785299 9599415964605126212677949)
          ·
            refine ⟨3599780986726922329754231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9599415964605126212677949 3599780986726922329754231)
            ·
              refine ⟨5399671480090383494631347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3599780986726922329754231 5399671480090383494631347)
              ·
                refine ⟨8099507220135575241947021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5399671480090383494631347 8099507220135575241947021)
                ·
                  refine ⟨3037315207550840715730133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8099507220135575241947021 3037315207550840715730133)
                  ·
                    refine ⟨71187075176972829274925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3037315207550840715730133 71187075176972829274925)
                    ·
                      rfl

theorem cell23_415909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_415909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415909 prefixEnd_415909 := by exact prefixLift 415909
  have htrace : WordTrace (prefixWord ++ tailWord_415909) baseStart_415909 baseEnd_415909 := by
    simpa [prefixWord, tailWord_415909, baseEnd_415909] using wordTrace_append hprefix tailTrace_415909
  have hstable : (prefixWord ++ tailWord_415909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415909).length < 2 ^ (prefixWord ++ tailWord_415909).sum := by decide
  have hdescent : baseEnd_415909 < baseStart_415909 := by decide
  rcases family_descends (prefixWord ++ tailWord_415909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415916 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 3, 7, 2]
def baseStart_415916 : Nat := 118140960795 + 415916 * 2 ^ 59
def prefixEnd_415916 : Nat := 4983230072969 + 3 ^ 40 * 415916 * 2
def baseEnd_415916 : Nat := 213564819895499960437243

theorem tailTrace_415916 : CollatzResearch.WordTrace tailWord_415916 prefixEnd_415916 213564819895499960437243 := by
  unfold tailWord_415916
  simp only [CollatzResearch.WordTrace]
  refine ⟨7584851380607419821349801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10113135174143226428466401 7584851380607419821349801)
  ·
    refine ⟨5688638535455564866012351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7584851380607419821349801 5688638535455564866012351)
    ·
      refine ⟨8532957803183347299018527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5688638535455564866012351 8532957803183347299018527)
      ·
        refine ⟨12799436704775020948527791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8532957803183347299018527 12799436704775020948527791)
        ·
          refine ⟨19199155057162531422791687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12799436704775020948527791 19199155057162531422791687)
          ·
            refine ⟨28798732585743797134187531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19199155057162531422791687 28798732585743797134187531)
            ·
              refine ⟨43198098878615695701281297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28798732585743797134187531 43198098878615695701281297)
              ·
                refine ⟨32398574158961771775960973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43198098878615695701281297 32398574158961771775960973)
                ·
                  refine ⟨12149465309610664415985365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32398574158961771775960973 12149465309610664415985365)
                  ·
                    refine ⟨284753093193999947249657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12149465309610664415985365 284753093193999947249657)
                    ·
                      refine ⟨213564819895499960437243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 284753093193999947249657 213564819895499960437243)
                      ·
                        rfl

theorem cell23_415916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 7, 2].length) (baseStart_415916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415916 prefixEnd_415916 := by exact prefixLift 415916
  have htrace : WordTrace (prefixWord ++ tailWord_415916) baseStart_415916 baseEnd_415916 := by
    simpa [prefixWord, tailWord_415916, baseEnd_415916] using wordTrace_append hprefix tailTrace_415916
  have hstable : (prefixWord ++ tailWord_415916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415916).length < 2 ^ (prefixWord ++ tailWord_415916).sum := by decide
  have hdescent : baseEnd_415916 < baseStart_415916 := by decide
  rcases family_descends (prefixWord ++ tailWord_415916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415919 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 5]
def baseStart_415919 : Nat := 118140960795 + 415919 * 2 ^ 59
def prefixEnd_415919 : Nat := 4983230072969 + 3 ^ 40 * 415919 * 2
def baseEnd_415919 : Nat := 213566360337463448699729

theorem tailTrace_415919 : CollatzResearch.WordTrace tailWord_415919 prefixEnd_415919 213566360337463448699729 := by
  unfold tailWord_415919
  simp only [CollatzResearch.WordTrace]
  refine ⟨15169812180203971155058811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10113208120135980770039207 15169812180203971155058811)
  ·
    refine ⟨22754718270305956732588217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15169812180203971155058811 22754718270305956732588217)
    ·
      refine ⟨17066038702729467549441163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22754718270305956732588217 17066038702729467549441163)
      ·
        refine ⟨25599058054094201324161745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17066038702729467549441163 25599058054094201324161745)
        ·
          refine ⟨19199293540570650993121309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25599058054094201324161745 19199293540570650993121309)
          ·
            refine ⟨7199735077713994122420491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19199293540570650993121309 7199735077713994122420491)
            ·
              refine ⟨10799602616570991183630737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7199735077713994122420491 10799602616570991183630737)
              ·
                refine ⟨8099701962428243387723053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10799602616570991183630737 8099701962428243387723053)
                ·
                  refine ⟨3037388235910591270396145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8099701962428243387723053 3037388235910591270396145)
                  ·
                    refine ⟨2278041176932943452797109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3037388235910591270396145 2278041176932943452797109)
                    ·
                      refine ⟨213566360337463448699729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2278041176932943452797109 213566360337463448699729)
                      ·
                        rfl

theorem cell23_415919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 5].length) (baseStart_415919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415919 prefixEnd_415919 := by exact prefixLift 415919
  have htrace : WordTrace (prefixWord ++ tailWord_415919) baseStart_415919 baseEnd_415919 := by
    simpa [prefixWord, tailWord_415919, baseEnd_415919] using wordTrace_append hprefix tailTrace_415919
  have hstable : (prefixWord ++ tailWord_415919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415919).length < 2 ^ (prefixWord ++ tailWord_415919).sum := by decide
  have hdescent : baseEnd_415919 < baseStart_415919 := by decide
  rcases family_descends (prefixWord ++ tailWord_415919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415983 : List Nat := [1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 3]
def baseStart_415983 : Nat := 118140960795 + 415983 * 2 ^ 59
def prefixEnd_415983 : Nat := 4983230072969 + 3 ^ 40 * 415983 * 2
def baseEnd_415983 : Nat := 213599223099351198299435

theorem tailTrace_415983 : CollatzResearch.WordTrace tailWord_415983 prefixEnd_415983 213599223099351198299435 := by
  unfold tailWord_415983
  simp only [CollatzResearch.WordTrace]
  refine ⟨15172146451972110085388603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10114764301314740056925735 15172146451972110085388603)
  ·
    refine ⟨22758219677958165128082905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15172146451972110085388603 22758219677958165128082905)
    ·
      refine ⟨17068664758468623846062179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22758219677958165128082905 17068664758468623846062179)
      ·
        refine ⟨25602997137702935769093269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17068664758468623846062179 25602997137702935769093269)
        ·
          refine ⟨1200140490829825114176247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25602997137702935769093269 1200140490829825114176247)
          ·
            refine ⟨1800210736244737671264371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1200140490829825114176247 1800210736244737671264371)
            ·
              refine ⟨2700316104367106506896557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1800210736244737671264371 2700316104367106506896557)
              ·
                refine ⟨1012618539137664940086209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2700316104367106506896557 1012618539137664940086209)
                ·
                  refine ⟨759463904353248705064657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1012618539137664940086209 759463904353248705064657)
                  ·
                    refine ⟨569597928264936528798493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 759463904353248705064657 569597928264936528798493)
                    ·
                      refine ⟨213599223099351198299435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 569597928264936528798493 213599223099351198299435)
                      ·
                        rfl

theorem cell23_415983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 3].length) (baseStart_415983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_415983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_415983 prefixEnd_415983 := by exact prefixLift 415983
  have htrace : WordTrace (prefixWord ++ tailWord_415983) baseStart_415983 baseEnd_415983 := by
    simpa [prefixWord, tailWord_415983, baseEnd_415983] using wordTrace_append hprefix tailTrace_415983
  have hstable : (prefixWord ++ tailWord_415983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415983).length < 2 ^ (prefixWord ++ tailWord_415983).sum := by decide
  have hdescent : baseEnd_415983 < baseStart_415983 := by decide
  rcases family_descends (prefixWord ++ tailWord_415983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416050 : List Nat := [3, 2, 1, 1, 5, 1, 1, 3, 1, 5]
def baseStart_416050 : Nat := 118140960795 + 416050 * 2 ^ 59
def prefixEnd_416050 : Nat := 4983230072969 + 3 ^ 40 * 416050 * 2
def baseEnd_416050 : Nat := 71211208767734145387209

theorem tailTrace_416050 : CollatzResearch.WordTrace tailWord_416050 prefixEnd_416050 71211208767734145387209 := by
  unfold tailWord_416050
  simp only [CollatzResearch.WordTrace]
  refine ⟨3793647535682345132019401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10116393428486253685385069 3793647535682345132019401)
  ·
    refine ⟨2845235651761758849014551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3793647535682345132019401 2845235651761758849014551)
    ·
      refine ⟨4267853477642638273521827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2845235651761758849014551 4267853477642638273521827)
      ·
        refine ⟨6401780216463957410282741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4267853477642638273521827 6401780216463957410282741)
        ·
          refine ⟨600166895293496007214007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6401780216463957410282741 600166895293496007214007)
          ·
            refine ⟨900250342940244010821011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600166895293496007214007 900250342940244010821011)
            ·
              refine ⟨1350375514410366016231517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 900250342940244010821011 1350375514410366016231517)
              ·
                refine ⟨506390817903887256086819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1350375514410366016231517 506390817903887256086819)
                ·
                  refine ⟨759586226855830884130229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 506390817903887256086819 759586226855830884130229)
                  ·
                    refine ⟨71211208767734145387209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 759586226855830884130229 71211208767734145387209)
                    ·
                      rfl

theorem cell23_416050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_416050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416050 prefixEnd_416050 := by exact prefixLift 416050
  have htrace : WordTrace (prefixWord ++ tailWord_416050) baseStart_416050 baseEnd_416050 := by
    simpa [prefixWord, tailWord_416050, baseEnd_416050] using wordTrace_append hprefix tailTrace_416050
  have hstable : (prefixWord ++ tailWord_416050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416050).length < 2 ^ (prefixWord ++ tailWord_416050).sum := by decide
  have hdescent : baseEnd_416050 < baseStart_416050 := by decide
  rcases family_descends (prefixWord ++ tailWord_416050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416063 : List Nat := [1, 1, 2, 2, 4, 1, 3, 1, 4, 4]
def baseStart_416063 : Nat := 118140960795 + 416063 * 2 ^ 59
def prefixEnd_416063 : Nat := 4983230072969 + 3 ^ 40 * 416063 * 2
def baseEnd_416063 : Nat := 71213433850570295099689

theorem tailTrace_416063 : CollatzResearch.WordTrace tailWord_416063 prefixEnd_416063 71213433850570295099689 := by
  unfold tailWord_416063
  simp only [CollatzResearch.WordTrace]
  refine ⟨15175064291682283748300843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10116709527788189165533895 15175064291682283748300843)
  ·
    refine ⟨22762596437523425622451265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15175064291682283748300843 22762596437523425622451265)
    ·
      refine ⟨17071947328142569216838449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22762596437523425622451265 17071947328142569216838449)
      ·
        refine ⟨12803960496106926912628837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17071947328142569216838449 12803960496106926912628837)
        ·
          refine ⟨2400742593020048796117907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12803960496106926912628837 2400742593020048796117907)
          ·
            refine ⟨3601113889530073194176861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2400742593020048796117907 3601113889530073194176861)
            ·
              refine ⟨1350417708573777447816323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3601113889530073194176861 1350417708573777447816323)
              ·
                refine ⟨2025626562860666171724485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1350417708573777447816323 2025626562860666171724485)
                ·
                  refine ⟨379804980536374907198341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2025626562860666171724485 379804980536374907198341)
                  ·
                    refine ⟨71213433850570295099689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 379804980536374907198341 71213433850570295099689)
                    ·
                      rfl

theorem cell23_416063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 4].length) (baseStart_416063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416063 prefixEnd_416063 := by exact prefixLift 416063
  have htrace : WordTrace (prefixWord ++ tailWord_416063) baseStart_416063 baseEnd_416063 := by
    simpa [prefixWord, tailWord_416063, baseEnd_416063] using wordTrace_append hprefix tailTrace_416063
  have hstable : (prefixWord ++ tailWord_416063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416063).length < 2 ^ (prefixWord ++ tailWord_416063).sum := by decide
  have hdescent : baseEnd_416063 < baseStart_416063 := by decide
  rcases family_descends (prefixWord ++ tailWord_416063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
