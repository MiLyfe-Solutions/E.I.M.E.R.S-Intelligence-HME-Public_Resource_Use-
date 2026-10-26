import V185TrunkScan23Chunk0237

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1408232 : List Nat := [2, 1, 4, 1, 2, 1, 3, 1, 4, 1, 3]
def baseStart_1408232 : Nat := 118140960795 + 1408232 * 2 ^ 59
def prefixEnd_1408232 : Nat := 4983230072969 + 3 ^ 40 * 1408232 * 2
def baseEnd_1408232 : Nat := 723099889042439519523665

theorem tailTrace_1408232 : CollatzResearch.WordTrace tailWord_1408232 prefixEnd_1408232 723099889042439519523665 := by
  unfold tailWord_1408232
  simp only [CollatzResearch.WordTrace]
  refine ⟨25681220317111722861489475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34241627089482297148652633 25681220317111722861489475)
  ·
    refine ⟨38521830475667584292234213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25681220317111722861489475 38521830475667584292234213)
    ·
      refine ⟨7222843214187672054793915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38521830475667584292234213 7222843214187672054793915)
      ·
        refine ⟨10834264821281508082190873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7222843214187672054793915 10834264821281508082190873)
        ·
          refine ⟨8125698615961131061643155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10834264821281508082190873 8125698615961131061643155)
          ·
            refine ⟨12188547923941696592464733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8125698615961131061643155 12188547923941696592464733)
            ·
              refine ⟨4570705471478136222174275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12188547923941696592464733 4570705471478136222174275)
              ·
                refine ⟨6856058207217204333261413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4570705471478136222174275 6856058207217204333261413)
                ·
                  refine ⟨1285510913853225812486515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6856058207217204333261413 1285510913853225812486515)
                  ·
                    refine ⟨1928266370779838718729773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1285510913853225812486515 1928266370779838718729773)
                    ·
                      refine ⟨723099889042439519523665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1928266370779838718729773 723099889042439519523665)
                      ·
                        rfl

theorem cell23_1408232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_1408232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408232 prefixEnd_1408232 := by exact prefixLift 1408232
  have htrace : WordTrace (prefixWord ++ tailWord_1408232) baseStart_1408232 baseEnd_1408232 := by
    simpa [prefixWord, tailWord_1408232, baseEnd_1408232] using wordTrace_append hprefix tailTrace_1408232
  have hstable : (prefixWord ++ tailWord_1408232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408232).length < 2 ^ (prefixWord ++ tailWord_1408232).sum := by decide
  have hdescent : baseEnd_1408232 < baseStart_1408232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408249 : List Nat := [1, 2, 1, 3, 1, 1, 7, 1, 2, 1, 3]
def baseStart_1408249 : Nat := 118140960795 + 1408249 * 2 ^ 59
def prefixEnd_1408249 : Nat := 4983230072969 + 3 ^ 40 * 1408249 * 2
def baseEnd_1408249 : Nat := 723108618213565953011087

theorem tailTrace_1408249 : CollatzResearch.WordTrace tailWord_1408249 prefixEnd_1408249 723108618213565953011087 := by
  unfold tailWord_1408249
  simp only [CollatzResearch.WordTrace]
  refine ⟨51363060675161857626347801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34242040450107905084231867 51363060675161857626347801)
  ·
    refine ⟨38522295506371393219760851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51363060675161857626347801 38522295506371393219760851)
    ·
      refine ⟨57783443259557089829641277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38522295506371393219760851 57783443259557089829641277)
      ·
        refine ⟨21668791222333908686115479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57783443259557089829641277 21668791222333908686115479)
        ·
          refine ⟨32503186833500863029173219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21668791222333908686115479 32503186833500863029173219)
          ·
            refine ⟨48754780250251294543759829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32503186833500863029173219 48754780250251294543759829)
            ·
              refine ⟨1142690162115264715869371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 48754780250251294543759829 1142690162115264715869371)
              ·
                refine ⟨1714035243172897073804057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1142690162115264715869371 1714035243172897073804057)
                ·
                  refine ⟨1285526432379672805353043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1714035243172897073804057 1285526432379672805353043)
                  ·
                    refine ⟨1928289648569509208029565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1285526432379672805353043 1928289648569509208029565)
                    ·
                      refine ⟨723108618213565953011087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1928289648569509208029565 723108618213565953011087)
                      ·
                        rfl

theorem cell23_1408249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 2, 1, 3].length) (baseStart_1408249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408249 prefixEnd_1408249 := by exact prefixLift 1408249
  have htrace : WordTrace (prefixWord ++ tailWord_1408249) baseStart_1408249 baseEnd_1408249 := by
    simpa [prefixWord, tailWord_1408249, baseEnd_1408249] using wordTrace_append hprefix tailTrace_1408249
  have hstable : (prefixWord ++ tailWord_1408249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408249).length < 2 ^ (prefixWord ++ tailWord_1408249).sum := by decide
  have hdescent : baseEnd_1408249 < baseStart_1408249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408259 : List Nat := [1, 1, 1, 3, 2, 5, 2, 2, 1, 3, 2]
def baseStart_1408259 : Nat := 118140960795 + 1408259 * 2 ^ 59
def prefixEnd_1408259 : Nat := 4983230072969 + 3 ^ 40 * 1408259 * 2
def baseEnd_1408259 : Nat := 723113753020110913886041

theorem tailTrace_1408259 : CollatzResearch.WordTrace tailWord_1408259 prefixEnd_1408259 723113753020110913886041 := by
  unfold tailWord_1408259
  simp only [CollatzResearch.WordTrace]
  refine ⟨51363425405125629334211831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34242283603417086222807887 51363425405125629334211831)
  ·
    refine ⟨77045138107688444001317747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51363425405125629334211831 77045138107688444001317747)
    ·
      refine ⟨115567707161532666001976621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77045138107688444001317747 115567707161532666001976621)
      ·
        refine ⟨43337890185574749750741233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115567707161532666001976621 43337890185574749750741233)
        ·
          refine ⟨32503417639181062313055925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43337890185574749750741233 32503417639181062313055925)
          ·
            refine ⟨3047195403673224591848993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32503417639181062313055925 3047195403673224591848993)
            ·
              refine ⟨2285396552754918443886745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3047195403673224591848993 2285396552754918443886745)
              ·
                refine ⟨1714047414566188832915059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2285396552754918443886745 1714047414566188832915059)
                ·
                  refine ⟨2571071121849283249372589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1714047414566188832915059 2571071121849283249372589)
                  ·
                    refine ⟨964151670693481218514721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2571071121849283249372589 964151670693481218514721)
                    ·
                      refine ⟨723113753020110913886041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 964151670693481218514721 723113753020110913886041)
                      ·
                        rfl

theorem cell23_1408259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 3, 2].length) (baseStart_1408259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408259 prefixEnd_1408259 := by exact prefixLift 1408259
  have htrace : WordTrace (prefixWord ++ tailWord_1408259) baseStart_1408259 baseEnd_1408259 := by
    simpa [prefixWord, tailWord_1408259, baseEnd_1408259] using wordTrace_append hprefix tailTrace_1408259
  have hstable : (prefixWord ++ tailWord_1408259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408259).length < 2 ^ (prefixWord ++ tailWord_1408259).sum := by decide
  have hdescent : baseEnd_1408259 < baseStart_1408259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408289 : List Nat := [1, 2, 3, 2, 1, 1, 1, 6, 2, 2, 2]
def baseStart_1408289 : Nat := 118140960795 + 1408289 * 2 ^ 59
def prefixEnd_1408289 : Nat := 4983230072969 + 3 ^ 40 * 1408289 * 2
def baseEnd_1408289 : Nat := 723129157439745796510903

theorem tailTrace_1408289 : CollatzResearch.WordTrace tailWord_1408289 prefixEnd_1408289 723129157439745796510903 := by
  unfold tailWord_1408289
  simp only [CollatzResearch.WordTrace]
  refine ⟨51364519595016944457803921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34243013063344629638535947 51364519595016944457803921)
  ·
    refine ⟨38523389696262708343352941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51364519595016944457803921 38523389696262708343352941)
    ·
      refine ⟨14446271136098515628757353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38523389696262708343352941 14446271136098515628757353)
      ·
        refine ⟨10834703352073886721568015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14446271136098515628757353 10834703352073886721568015)
        ·
          refine ⟨16252055028110830082352023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10834703352073886721568015 16252055028110830082352023)
          ·
            refine ⟨24378082542166245123528035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16252055028110830082352023 24378082542166245123528035)
            ·
              refine ⟨36567123813249367685292053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24378082542166245123528035 36567123813249367685292053)
              ·
                refine ⟨1714083928746064110248065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36567123813249367685292053 1714083928746064110248065)
                ·
                  refine ⟨1285562946559548082686049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1714083928746064110248065 1285562946559548082686049)
                  ·
                    refine ⟨964172209919661062014537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1285562946559548082686049 964172209919661062014537)
                    ·
                      refine ⟨723129157439745796510903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 964172209919661062014537 723129157439745796510903)
                      ·
                        rfl

theorem cell23_1408289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_1408289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408289 prefixEnd_1408289 := by exact prefixLift 1408289
  have htrace : WordTrace (prefixWord ++ tailWord_1408289) baseStart_1408289 baseEnd_1408289 := by
    simpa [prefixWord, tailWord_1408289, baseEnd_1408289] using wordTrace_append hprefix tailTrace_1408289
  have hstable : (prefixWord ++ tailWord_1408289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408289).length < 2 ^ (prefixWord ++ tailWord_1408289).sum := by decide
  have hdescent : baseEnd_1408289 < baseStart_1408289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408306 : List Nat := [3, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2]
def baseStart_1408306 : Nat := 118140960795 + 1408306 * 2 ^ 59
def prefixEnd_1408306 : Nat := 4983230072969 + 3 ^ 40 * 1408306 * 2
def baseEnd_1408306 : Nat := 723137886610872229998325

theorem tailTrace_1408306 : CollatzResearch.WordTrace tailWord_1408306 prefixEnd_1408306 723137886610872229998325 := by
  unfold tailWord_1408306
  simp only [CollatzResearch.WordTrace]
  refine ⟨12841284908988839090293193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34243426423970237574115181 12841284908988839090293193)
  ·
    refine ⟨9630963681741629317719895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12841284908988839090293193 9630963681741629317719895)
    ·
      refine ⟨14446445522612443976579843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9630963681741629317719895 14446445522612443976579843)
      ·
        refine ⟨21669668283918665964869765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14446445522612443976579843 21669668283918665964869765)
        ·
          refine ⟨4063062803234749868413081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21669668283918665964869765 4063062803234749868413081)
          ·
            refine ⟨3047297102426062401309811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4063062803234749868413081 3047297102426062401309811)
            ·
              refine ⟨4570945653639093601964717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3047297102426062401309811 4570945653639093601964717)
              ·
                refine ⟨1714104620114660100736769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4570945653639093601964717 1714104620114660100736769)
                ·
                  refine ⟨1285578465085995075552577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1714104620114660100736769 1285578465085995075552577)
                  ·
                    refine ⟨964183848814496306664433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1285578465085995075552577 964183848814496306664433)
                    ·
                      refine ⟨723137886610872229998325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 964183848814496306664433 723137886610872229998325)
                      ·
                        rfl

theorem cell23_1408306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2].length) (baseStart_1408306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408306 prefixEnd_1408306 := by exact prefixLift 1408306
  have htrace : WordTrace (prefixWord ++ tailWord_1408306) baseStart_1408306 baseEnd_1408306 := by
    simpa [prefixWord, tailWord_1408306, baseEnd_1408306] using wordTrace_append hprefix tailTrace_1408306
  have hstable : (prefixWord ++ tailWord_1408306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408306).length < 2 ^ (prefixWord ++ tailWord_1408306).sum := by decide
  have hdescent : baseEnd_1408306 < baseStart_1408306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408310 : List Nat := [5, 1, 2, 3, 1, 2, 1, 2, 1, 3, 2]
def baseStart_1408310 : Nat := 118140960795 + 1408310 * 2 ^ 59
def prefixEnd_1408310 : Nat := 4983230072969 + 3 ^ 40 * 1408310 * 2
def baseEnd_1408310 : Nat := 723139940533490214348307

theorem tailTrace_1408310 : CollatzResearch.WordTrace tailWord_1408310 prefixEnd_1408310 723139940533490214348307 := by
  unfold tailWord_1408310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3210330345496304065269899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34243523685293910029545589 3210330345496304065269899)
  ·
    refine ⟨4815495518244456097904849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3210330345496304065269899 4815495518244456097904849)
    ·
      refine ⟨3611621638683342073428637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4815495518244456097904849 3611621638683342073428637)
      ·
        refine ⟨1354358114506253277535739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3611621638683342073428637 1354358114506253277535739)
        ·
          refine ⟨2031537171759379916303609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1354358114506253277535739 2031537171759379916303609)
          ·
            refine ⟨1523652878819534937227707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2031537171759379916303609 1523652878819534937227707)
            ·
              refine ⟨2285479318229302405841561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1523652878819534937227707 2285479318229302405841561)
              ·
                refine ⟨1714109488671976804381171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2285479318229302405841561 1714109488671976804381171)
                ·
                  refine ⟨2571164233007965206571757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1714109488671976804381171 2571164233007965206571757)
                  ·
                    refine ⟨964186587377986952464409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2571164233007965206571757 964186587377986952464409)
                    ·
                      refine ⟨723139940533490214348307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 964186587377986952464409 723139940533490214348307)
                      ·
                        rfl

theorem cell23_1408310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_1408310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408310 prefixEnd_1408310 := by exact prefixLift 1408310
  have htrace : WordTrace (prefixWord ++ tailWord_1408310) baseStart_1408310 baseEnd_1408310 := by
    simpa [prefixWord, tailWord_1408310, baseEnd_1408310] using wordTrace_append hprefix tailTrace_1408310
  have hstable : (prefixWord ++ tailWord_1408310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408310).length < 2 ^ (prefixWord ++ tailWord_1408310).sum := by decide
  have hdescent : baseEnd_1408310 < baseStart_1408310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408389 : List Nat := [1, 3, 1, 1, 3, 1, 3, 5, 1, 4]
def baseStart_1408389 : Nat := 118140960795 + 1408389 * 2 ^ 59
def prefixEnd_1408389 : Nat := 4983230072969 + 3 ^ 40 * 1408389 * 2
def baseEnd_1408389 : Nat := 241060168501731801753481

theorem tailTrace_1408389 : CollatzResearch.WordTrace tailWord_1408389 prefixEnd_1408389 241060168501731801753481 := by
  unfold tailWord_1408389
  simp only [CollatzResearch.WordTrace]
  refine ⟨51368166894654661536444221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34245444596436441024296147 51368166894654661536444221)
  ·
    refine ⟨19263062585495498076166583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51368166894654661536444221 19263062585495498076166583)
    ·
      refine ⟨28894593878243247114249875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19263062585495498076166583 28894593878243247114249875)
      ·
        refine ⟨43341890817364870671374813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28894593878243247114249875 43341890817364870671374813)
        ·
          refine ⟨16253209056511826501765555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43341890817364870671374813 16253209056511826501765555)
          ·
            refine ⟨24379813584767739752648333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16253209056511826501765555 24379813584767739752648333)
            ·
              refine ⟨9142430094287902407243125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24379813584767739752648333 9142430094287902407243125)
              ·
                refine ⟨857102821339490850679043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9142430094287902407243125 857102821339490850679043)
                ·
                  refine ⟨1285654232009236276018565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 857102821339490850679043 1285654232009236276018565)
                  ·
                    refine ⟨241060168501731801753481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1285654232009236276018565 241060168501731801753481)
                    ·
                      rfl

theorem cell23_1408389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 1, 4].length) (baseStart_1408389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408389 prefixEnd_1408389 := by exact prefixLift 1408389
  have htrace : WordTrace (prefixWord ++ tailWord_1408389) baseStart_1408389 baseEnd_1408389 := by
    simpa [prefixWord, tailWord_1408389, baseEnd_1408389] using wordTrace_append hprefix tailTrace_1408389
  have hstable : (prefixWord ++ tailWord_1408389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408389).length < 2 ^ (prefixWord ++ tailWord_1408389).sum := by decide
  have hdescent : baseEnd_1408389 < baseStart_1408389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408405 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 1, 2, 6]
def baseStart_1408405 : Nat := 118140960795 + 1408405 * 2 ^ 59
def prefixEnd_1408405 : Nat := 4983230072969 + 3 ^ 40 * 1408405 * 2
def baseEnd_1408405 : Nat := 723188721195667342660369

theorem tailTrace_1408405 : CollatzResearch.WordTrace tailWord_1408405 prefixEnd_1408405 723188721195667342660369 := by
  unfold tailWord_1408405
  simp only [CollatzResearch.WordTrace]
  refine ⟨51368750462596696269026669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34245833641731130846017779 51368750462596696269026669)
  ·
    refine ⟨19263281423473761100885001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51368750462596696269026669 19263281423473761100885001)
    ·
      refine ⟨14447461067605320825663751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19263281423473761100885001 14447461067605320825663751)
      ·
        refine ⟨21671191601407981238495627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14447461067605320825663751 21671191601407981238495627)
        ·
          refine ⟨32506787402111971857743441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21671191601407981238495627 32506787402111971857743441)
          ·
            refine ⟨24380090551583978893307581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32506787402111971857743441 24380090551583978893307581)
            ·
              refine ⟨9142533956843992084990343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24380090551583978893307581 9142533956843992084990343)
              ·
                refine ⟨13713800935265988127485515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9142533956843992084990343 13713800935265988127485515)
                ·
                  refine ⟨20570701402898982191228273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13713800935265988127485515 20570701402898982191228273)
                  ·
                    refine ⟨15428026052174236643421205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20570701402898982191228273 15428026052174236643421205)
                    ·
                      refine ⟨723188721195667342660369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15428026052174236643421205 723188721195667342660369)
                      ·
                        rfl

theorem cell23_1408405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_1408405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408405 prefixEnd_1408405 := by exact prefixLift 1408405
  have htrace : WordTrace (prefixWord ++ tailWord_1408405) baseStart_1408405 baseEnd_1408405 := by
    simpa [prefixWord, tailWord_1408405, baseEnd_1408405] using wordTrace_append hprefix tailTrace_1408405
  have hstable : (prefixWord ++ tailWord_1408405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408405).length < 2 ^ (prefixWord ++ tailWord_1408405).sum := by decide
  have hdescent : baseEnd_1408405 < baseStart_1408405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408435 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 4]
def baseStart_1408435 : Nat := 118140960795 + 1408435 * 2 ^ 59
def prefixEnd_1408435 : Nat := 4983230072969 + 3 ^ 40 * 1408435 * 2
def baseEnd_1408435 : Nat := 723204125615302225285231

theorem tailTrace_1408435 : CollatzResearch.WordTrace tailWord_1408435 prefixEnd_1408435 723204125615302225285231 := by
  unfold tailWord_1408435
  simp only [CollatzResearch.WordTrace]
  refine ⟨51369844652488011392618759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34246563101658674261745839 51369844652488011392618759)
  ·
    refine ⟨77054766978732017088928139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51369844652488011392618759 77054766978732017088928139)
    ·
      refine ⟨115582150468098025633392209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77054766978732017088928139 115582150468098025633392209)
      ·
        refine ⟨86686612851073519225044157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115582150468098025633392209 86686612851073519225044157)
        ·
          refine ⟨32507479819152569709391559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86686612851073519225044157 32507479819152569709391559)
          ·
            refine ⟨48761219728728854564087339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32507479819152569709391559 48761219728728854564087339)
            ·
              refine ⟨73141829593093281846131009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48761219728728854564087339 73141829593093281846131009)
              ·
                refine ⟨54856372194819961384598257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73141829593093281846131009 54856372194819961384598257)
                ·
                  refine ⟨41142279146114971038448693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54856372194819961384598257 41142279146114971038448693)
                  ·
                    refine ⟨3857088669948278534854565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41142279146114971038448693 3857088669948278534854565)
                    ·
                      refine ⟨723204125615302225285231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3857088669948278534854565 723204125615302225285231)
                      ·
                        rfl

theorem cell23_1408435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 4].length) (baseStart_1408435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408435 prefixEnd_1408435 := by exact prefixLift 1408435
  have htrace : WordTrace (prefixWord ++ tailWord_1408435) baseStart_1408435 baseEnd_1408435 := by
    simpa [prefixWord, tailWord_1408435, baseEnd_1408435] using wordTrace_append hprefix tailTrace_1408435
  have hstable : (prefixWord ++ tailWord_1408435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408435).length < 2 ^ (prefixWord ++ tailWord_1408435).sum := by decide
  have hdescent : baseEnd_1408435 < baseStart_1408435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408439 : List Nat := [1, 1, 3, 1, 3, 2, 2, 3, 2, 3, 2]
def baseStart_1408439 : Nat := 118140960795 + 1408439 * 2 ^ 59
def prefixEnd_1408439 : Nat := 4983230072969 + 3 ^ 40 * 1408439 * 2
def baseEnd_1408439 : Nat := 723206179537920209635213

theorem tailTrace_1408439 : CollatzResearch.WordTrace tailWord_1408439 prefixEnd_1408439 723206179537920209635213 := by
  unfold tailWord_1408439
  simp only [CollatzResearch.WordTrace]
  refine ⟨51369990544473520075764371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34246660362982346717176247 51369990544473520075764371)
  ·
    refine ⟨77054985816710280113646557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51369990544473520075764371 77054985816710280113646557)
    ·
      refine ⟨28895619681266355042617459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77054985816710280113646557 28895619681266355042617459)
      ·
        refine ⟨43343429521899532563926189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28895619681266355042617459 43343429521899532563926189)
        ·
          refine ⟨16253786070712324711472321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43343429521899532563926189 16253786070712324711472321)
          ·
            refine ⟨12190339553034243533604241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16253786070712324711472321 12190339553034243533604241)
            ·
              refine ⟨9142754664775682650203181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12190339553034243533604241 9142754664775682650203181)
              ·
                refine ⟨3428532999290880993826193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9142754664775682650203181 3428532999290880993826193)
                ·
                  refine ⟨2571399749468160745369645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3428532999290880993826193 2571399749468160745369645)
                  ·
                    refine ⟨964274906050560279513617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2571399749468160745369645 964274906050560279513617)
                    ·
                      refine ⟨723206179537920209635213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 964274906050560279513617 723206179537920209635213)
                      ·
                        rfl

theorem cell23_1408439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 3, 2].length) (baseStart_1408439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408439 prefixEnd_1408439 := by exact prefixLift 1408439
  have htrace : WordTrace (prefixWord ++ tailWord_1408439) baseStart_1408439 baseEnd_1408439 := by
    simpa [prefixWord, tailWord_1408439, baseEnd_1408439] using wordTrace_append hprefix tailTrace_1408439
  have hstable : (prefixWord ++ tailWord_1408439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408439).length < 2 ^ (prefixWord ++ tailWord_1408439).sum := by decide
  have hdescent : baseEnd_1408439 < baseStart_1408439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408472 : List Nat := [2, 1, 2, 2, 2, 1, 4, 2, 1, 1, 5]
def baseStart_1408472 : Nat := 118140960795 + 1408472 * 2 ^ 59
def prefixEnd_1408472 : Nat := 4983230072969 + 3 ^ 40 * 1408472 * 2
def baseEnd_1408472 : Nat := 723223124399518580522561

theorem tailTrace_1408472 : CollatzResearch.WordTrace tailWord_1408472 prefixEnd_1408472 723223124399518580522561 := by
  unfold tailWord_1408472
  simp only [CollatzResearch.WordTrace]
  refine ⟨25685597076676983355857835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34247462768902644474477113 25685597076676983355857835)
  ·
    refine ⟨38528395615015475033786753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25685597076676983355857835 38528395615015475033786753)
    ·
      refine ⟨28896296711261606275340065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38528395615015475033786753 28896296711261606275340065)
      ·
        refine ⟨21672222533446204706505049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28896296711261606275340065 21672222533446204706505049)
        ·
          refine ⟨16254166900084653529878787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21672222533446204706505049 16254166900084653529878787)
          ·
            refine ⟨24381250350126980294818181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16254166900084653529878787 24381250350126980294818181)
            ·
              refine ⟨4571484440648808805278409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24381250350126980294818181 4571484440648808805278409)
              ·
                refine ⟨3428613330486606603958807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4571484440648808805278409 3428613330486606603958807)
                ·
                  refine ⟨5142919995729909905938211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3428613330486606603958807 5142919995729909905938211)
                  ·
                    refine ⟨7714379993594864858907317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5142919995729909905938211 7714379993594864858907317)
                    ·
                      refine ⟨723223124399518580522561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7714379993594864858907317 723223124399518580522561)
                      ·
                        rfl

theorem cell23_1408472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_1408472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408472 prefixEnd_1408472 := by exact prefixLift 1408472
  have htrace : WordTrace (prefixWord ++ tailWord_1408472) baseStart_1408472 baseEnd_1408472 := by
    simpa [prefixWord, tailWord_1408472, baseEnd_1408472] using wordTrace_append hprefix tailTrace_1408472
  have hstable : (prefixWord ++ tailWord_1408472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408472).length < 2 ^ (prefixWord ++ tailWord_1408472).sum := by decide
  have hdescent : baseEnd_1408472 < baseStart_1408472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408479 : List Nat := [1, 1, 2, 3, 3, 1, 3, 3, 2, 4]
def baseStart_1408479 : Nat := 118140960795 + 1408479 * 2 ^ 59
def prefixEnd_1408479 : Nat := 4983230072969 + 3 ^ 40 * 1408479 * 2
def baseEnd_1408479 : Nat := 241075572921366684378343

theorem tailTrace_1408479 : CollatzResearch.WordTrace tailWord_1408479 prefixEnd_1408479 241075572921366684378343 := by
  unfold tailWord_1408479
  simp only [CollatzResearch.WordTrace]
  refine ⟨51371449464328606907220491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34247632976219071271480327 51371449464328606907220491)
  ·
    refine ⟨77057174196492910360830737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51371449464328606907220491 77057174196492910360830737)
    ·
      refine ⟨57792880647369682770623053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77057174196492910360830737 57792880647369682770623053)
      ·
        refine ⟨21672330242763631038983645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57792880647369682770623053 21672330242763631038983645)
        ·
          refine ⟨8127123841036361639618867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21672330242763631038983645 8127123841036361639618867)
          ·
            refine ⟨12190685761554542459428301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8127123841036361639618867 12190685761554542459428301)
            ·
              refine ⟨4571507160582953422285613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12190685761554542459428301 4571507160582953422285613)
              ·
                refine ⟨1714315185218607533357105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4571507160582953422285613 1714315185218607533357105)
                ·
                  refine ⟨1285736388913955650017829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1714315185218607533357105 1285736388913955650017829)
                  ·
                    refine ⟨241075572921366684378343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1285736388913955650017829 241075572921366684378343)
                    ·
                      rfl

theorem cell23_1408479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 4].length) (baseStart_1408479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408479 prefixEnd_1408479 := by exact prefixLift 1408479
  have htrace : WordTrace (prefixWord ++ tailWord_1408479) baseStart_1408479 baseEnd_1408479 := by
    simpa [prefixWord, tailWord_1408479, baseEnd_1408479] using wordTrace_append hprefix tailTrace_1408479
  have hstable : (prefixWord ++ tailWord_1408479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408479).length < 2 ^ (prefixWord ++ tailWord_1408479).sum := by decide
  have hdescent : baseEnd_1408479 < baseStart_1408479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408506 : List Nat := [3, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3]
def baseStart_1408506 : Nat := 118140960795 + 1408506 * 2 ^ 59
def prefixEnd_1408506 : Nat := 4983230072969 + 3 ^ 40 * 1408506 * 2
def baseEnd_1408506 : Nat := 723240582741771447497405

theorem tailTrace_1408506 : CollatzResearch.WordTrace tailWord_1408506 prefixEnd_1408506 723240582741771447497405 := by
  unfold tailWord_1408506
  simp only [CollatzResearch.WordTrace]
  refine ⟨12843108558807697629613343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34248289490153860345635581 12843108558807697629613343)
  ·
    refine ⟨19264662838211546444420015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12843108558807697629613343 19264662838211546444420015)
    ·
      refine ⟨28896994257317319666630023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19264662838211546444420015 28896994257317319666630023)
      ·
        refine ⟨43345491385975979499945035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28896994257317319666630023 43345491385975979499945035)
        ·
          refine ⟨65018237078963969249917553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43345491385975979499945035 65018237078963969249917553)
          ·
            refine ⟨48763677809222976937438165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65018237078963969249917553 48763677809222976937438165)
            ·
              refine ⟨1142898698653663521971207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 48763677809222976937438165 1142898698653663521971207)
              ·
                refine ⟨1714348047980495282956811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1142898698653663521971207 1714348047980495282956811)
                ·
                  refine ⟨2571522071970742924435217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1714348047980495282956811 2571522071970742924435217)
                  ·
                    refine ⟨1928641553978057193326413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2571522071970742924435217 1928641553978057193326413)
                    ·
                      refine ⟨723240582741771447497405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1928641553978057193326413 723240582741771447497405)
                      ·
                        rfl

theorem cell23_1408506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3].length) (baseStart_1408506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408506 prefixEnd_1408506 := by exact prefixLift 1408506
  have htrace : WordTrace (prefixWord ++ tailWord_1408506) baseStart_1408506 baseEnd_1408506 := by
    simpa [prefixWord, tailWord_1408506, baseEnd_1408506] using wordTrace_append hprefix tailTrace_1408506
  have hstable : (prefixWord ++ tailWord_1408506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408506).length < 2 ^ (prefixWord ++ tailWord_1408506).sum := by decide
  have hdescent : baseEnd_1408506 < baseStart_1408506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408520 : List Nat := [2, 1, 3, 2, 1, 1, 6, 2, 1, 2, 2]
def baseStart_1408520 : Nat := 118140960795 + 1408520 * 2 ^ 59
def prefixEnd_1408520 : Nat := 4983230072969 + 3 ^ 40 * 1408520 * 2
def baseEnd_1408520 : Nat := 723247771470934392722341

theorem tailTrace_1408520 : CollatzResearch.WordTrace tailWord_1408520 prefixEnd_1408520 723247771470934392722341 := by
  unfold tailWord_1408520
  simp only [CollatzResearch.WordTrace]
  refine ⟨25686472428590035454731507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34248629904786713939642009 25686472428590035454731507)
  ·
    refine ⟨38529708642885053182097261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25686472428590035454731507 38529708642885053182097261)
    ·
      refine ⟨14448640741081894943286473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38529708642885053182097261 14448640741081894943286473)
      ·
        refine ⟨10836480555811421207464855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14448640741081894943286473 10836480555811421207464855)
        ·
          refine ⟨16254720833717131811197283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10836480555811421207464855 16254720833717131811197283)
          ·
            refine ⟨24382081250575697716795925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16254720833717131811197283 24382081250575697716795925)
            ·
              refine ⟨1142910058620735830474809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24382081250575697716795925 1142910058620735830474809)
              ·
                refine ⟨857182543965551872856107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1142910058620735830474809 857182543965551872856107)
                ·
                  refine ⟨1285773815948327809284161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 857182543965551872856107 1285773815948327809284161)
                  ·
                    refine ⟨964330361961245856963121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1285773815948327809284161 964330361961245856963121)
                    ·
                      refine ⟨723247771470934392722341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 964330361961245856963121 723247771470934392722341)
                      ·
                        rfl

theorem cell23_1408520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_1408520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408520 prefixEnd_1408520 := by exact prefixLift 1408520
  have htrace : WordTrace (prefixWord ++ tailWord_1408520) baseStart_1408520 baseEnd_1408520 := by
    simpa [prefixWord, tailWord_1408520, baseEnd_1408520] using wordTrace_append hprefix tailTrace_1408520
  have hstable : (prefixWord ++ tailWord_1408520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408520).length < 2 ^ (prefixWord ++ tailWord_1408520).sum := by decide
  have hdescent : baseEnd_1408520 < baseStart_1408520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408522 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 2, 7]
def baseStart_1408522 : Nat := 118140960795 + 1408522 * 2 ^ 59
def prefixEnd_1408522 : Nat := 4983230072969 + 3 ^ 40 * 1408522 * 2
def baseEnd_1408522 : Nat := 241082932810747794965777

theorem tailTrace_1408522 : CollatzResearch.WordTrace tailWord_1408522 prefixEnd_1408522 241082932810747794965777 := by
  unfold tailWord_1408522
  simp only [CollatzResearch.WordTrace]
  refine ⟨12843254450793206312758955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34248678535448550167357213 12843254450793206312758955)
  ·
    refine ⟨19264881676189809469138433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12843254450793206312758955 19264881676189809469138433)
    ·
      refine ⟨14448661257142357101853825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19264881676189809469138433 14448661257142357101853825)
      ·
        refine ⟨10836495942856767826390369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14448661257142357101853825 10836495942856767826390369)
        ·
          refine ⟨8127371957142575869792777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10836495942856767826390369 8127371957142575869792777)
          ·
            refine ⟨6095528967856931902344583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8127371957142575869792777 6095528967856931902344583)
            ·
              refine ⟨9143293451785397853516875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6095528967856931902344583 9143293451785397853516875)
              ·
                refine ⟨13714940177678096780275313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9143293451785397853516875 13714940177678096780275313)
                ·
                  refine ⟨10286205133258572585206485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13714940177678096780275313 10286205133258572585206485)
                  ·
                    refine ⟨241082932810747794965777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10286205133258572585206485 241082932810747794965777)
                    ·
                      rfl

theorem cell23_1408522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_1408522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408522 prefixEnd_1408522 := by exact prefixLift 1408522
  have htrace : WordTrace (prefixWord ++ tailWord_1408522) baseStart_1408522 baseEnd_1408522 := by
    simpa [prefixWord, tailWord_1408522, baseEnd_1408522] using wordTrace_append hprefix tailTrace_1408522
  have hstable : (prefixWord ++ tailWord_1408522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408522).length < 2 ^ (prefixWord ++ tailWord_1408522).sum := by decide
  have hdescent : baseEnd_1408522 < baseStart_1408522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408526 : List Nat := [4, 1, 1, 2, 5, 1, 1, 8]
def baseStart_1408526 : Nat := 118140960795 + 1408526 * 2 ^ 59
def prefixEnd_1408526 : Nat := 4983230072969 + 3 ^ 40 * 1408526 * 2
def baseEnd_1408526 : Nat := 26787068605735606268419

theorem tailTrace_1408526 : CollatzResearch.WordTrace tailWord_1408526 prefixEnd_1408526 26787068605735606268419 := by
  unfold tailWord_1408526
  simp only [CollatzResearch.WordTrace]
  refine ⟨6421645461894791741772679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34248775796772222622787621 6421645461894791741772679)
  ·
    refine ⟨9632468192842187612659019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6421645461894791741772679 9632468192842187612659019)
    ·
      refine ⟨14448702289263281418988529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9632468192842187612659019 14448702289263281418988529)
      ·
        refine ⟨10836526716947461064241397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14448702289263281418988529 10836526716947461064241397)
        ·
          refine ⟨1015924379713824474772631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10836526716947461064241397 1015924379713824474772631)
          ·
            refine ⟨1523886569570736712158947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1015924379713824474772631 1523886569570736712158947)
            ·
              refine ⟨2285829854356105068238421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1523886569570736712158947 2285829854356105068238421)
              ·
                refine ⟨26787068605735606268419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2285829854356105068238421 26787068605735606268419)
                ·
                  rfl

theorem cell23_1408526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 8].length) (baseStart_1408526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408526 prefixEnd_1408526 := by exact prefixLift 1408526
  have htrace : WordTrace (prefixWord ++ tailWord_1408526) baseStart_1408526 baseEnd_1408526 := by
    simpa [prefixWord, tailWord_1408526, baseEnd_1408526] using wordTrace_append hprefix tailTrace_1408526
  have hstable : (prefixWord ++ tailWord_1408526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408526).length < 2 ^ (prefixWord ++ tailWord_1408526).sum := by decide
  have hdescent : baseEnd_1408526 < baseStart_1408526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408529 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 5, 3, 2]
def baseStart_1408529 : Nat := 118140960795 + 1408529 * 2 ^ 59
def prefixEnd_1408529 : Nat := 4983230072969 + 3 ^ 40 * 1408529 * 2
def baseEnd_1408529 : Nat := 723252392796824857509799

theorem tailTrace_1408529 : CollatzResearch.WordTrace tailWord_1408529 prefixEnd_1408529 723252392796824857509799 := by
  unfold tailWord_1408529
  simp only [CollatzResearch.WordTrace]
  refine ⟨51373273114147465446540641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34248848742764976964360427 51373273114147465446540641)
  ·
    refine ⟨38529954835610599084905481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51373273114147465446540641 38529954835610599084905481)
    ·
      refine ⟨28897466126707949313679111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38529954835610599084905481 28897466126707949313679111)
      ·
        refine ⟨43346199190061923970518667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28897466126707949313679111 43346199190061923970518667)
        ·
          refine ⟨65019298785092885955778001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43346199190061923970518667 65019298785092885955778001)
          ·
            refine ⟨48764474088819664466833501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65019298785092885955778001 48764474088819664466833501)
            ·
              refine ⟨18286677783307374175062563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48764474088819664466833501 18286677783307374175062563)
              ·
                refine ⟨27430016674961061262593845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18286677783307374175062563 27430016674961061262593845)
                ·
                  refine ⟨2571564063277599493368173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27430016674961061262593845 2571564063277599493368173)
                  ·
                    refine ⟨964336523729099810013065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2571564063277599493368173 964336523729099810013065)
                    ·
                      refine ⟨723252392796824857509799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 964336523729099810013065 723252392796824857509799)
                      ·
                        rfl

theorem cell23_1408529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 3, 2].length) (baseStart_1408529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408529 prefixEnd_1408529 := by exact prefixLift 1408529
  have htrace : WordTrace (prefixWord ++ tailWord_1408529) baseStart_1408529 baseEnd_1408529 := by
    simpa [prefixWord, tailWord_1408529, baseEnd_1408529] using wordTrace_append hprefix tailTrace_1408529
  have hstable : (prefixWord ++ tailWord_1408529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408529).length < 2 ^ (prefixWord ++ tailWord_1408529).sum := by decide
  have hdescent : baseEnd_1408529 < baseStart_1408529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408536 : List Nat := [2, 1, 2, 3, 4, 1, 2, 1, 1, 3, 3]
def baseStart_1408536 : Nat := 118140960795 + 1408536 * 2 ^ 59
def prefixEnd_1408536 : Nat := 4983230072969 + 3 ^ 40 * 1408536 * 2
def baseEnd_1408536 : Nat := 723255987161406330122267

theorem tailTrace_1408536 : CollatzResearch.WordTrace tailWord_1408536 prefixEnd_1408536 723255987161406330122267 := by
  unfold tailWord_1408536
  simp only [CollatzResearch.WordTrace]
  refine ⟨25686764212561052821022731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34249018950081403761363641 25686764212561052821022731)
  ·
    refine ⟨38530146318841579231534097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25686764212561052821022731 38530146318841579231534097)
    ·
      refine ⟨28897609739131184423650573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38530146318841579231534097 28897609739131184423650573)
      ·
        refine ⟨10836603652174194158868965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28897609739131184423650573 10836603652174194158868965)
        ·
          refine ⟨2031863184782661404787931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10836603652174194158868965 2031863184782661404787931)
          ·
            refine ⟨3047794777173992107181897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2031863184782661404787931 3047794777173992107181897)
            ·
              refine ⟨2285846082880494080386423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3047794777173992107181897 2285846082880494080386423)
              ·
                refine ⟨3428769124320741120579635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2285846082880494080386423 3428769124320741120579635)
                ·
                  refine ⟨5143153686481111680869453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3428769124320741120579635 5143153686481111680869453)
                  ·
                    refine ⟨1928682632430416880326045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5143153686481111680869453 1928682632430416880326045)
                    ·
                      refine ⟨723255987161406330122267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1928682632430416880326045 723255987161406330122267)
                      ·
                        rfl

theorem cell23_1408536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_1408536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408536 prefixEnd_1408536 := by exact prefixLift 1408536
  have htrace : WordTrace (prefixWord ++ tailWord_1408536) baseStart_1408536 baseEnd_1408536 := by
    simpa [prefixWord, tailWord_1408536, baseEnd_1408536] using wordTrace_append hprefix tailTrace_1408536
  have hstable : (prefixWord ++ tailWord_1408536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408536).length < 2 ^ (prefixWord ++ tailWord_1408536).sum := by decide
  have hdescent : baseEnd_1408536 < baseStart_1408536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408546 : List Nat := [3, 3, 1, 1, 1, 1, 4, 1, 3, 3, 2]
def baseStart_1408546 : Nat := 118140960795 + 1408546 * 2 ^ 59
def prefixEnd_1408546 : Nat := 4983230072969 + 3 ^ 40 * 1408546 * 2
def baseEnd_1408546 : Nat := 723261121967951290997221

theorem tailTrace_1408546 : CollatzResearch.WordTrace tailWord_1408546 prefixEnd_1408546 723261121967951290997221 := by
  unfold tailWord_1408546
  simp only [CollatzResearch.WordTrace]
  refine ⟨12843473288771469337477373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34249262103390584899939661 12843473288771469337477373)
  ·
    refine ⟨4816302483289301001554015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12843473288771469337477373 4816302483289301001554015)
    ·
      refine ⟨7224453724933951502331023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4816302483289301001554015 7224453724933951502331023)
      ·
        refine ⟨10836680587400927253496535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7224453724933951502331023 10836680587400927253496535)
        ·
          refine ⟨16255020881101390880244803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10836680587400927253496535 16255020881101390880244803)
          ·
            refine ⟨24382531321652086320367205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16255020881101390880244803 24382531321652086320367205)
            ·
              refine ⟨4571724622809766185068851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24382531321652086320367205 4571724622809766185068851)
              ·
                refine ⟨6857586934214649277603277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4571724622809766185068851 6857586934214649277603277)
                ·
                  refine ⟨2571595100330493479101229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6857586934214649277603277 2571595100330493479101229)
                  ·
                    refine ⟨964348162623935054662961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2571595100330493479101229 964348162623935054662961)
                    ·
                      refine ⟨723261121967951290997221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 964348162623935054662961 723261121967951290997221)
                      ·
                        rfl

theorem cell23_1408546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_1408546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408546 prefixEnd_1408546 := by exact prefixLift 1408546
  have htrace : WordTrace (prefixWord ++ tailWord_1408546) baseStart_1408546 baseEnd_1408546 := by
    simpa [prefixWord, tailWord_1408546, baseEnd_1408546] using wordTrace_append hprefix tailTrace_1408546
  have hstable : (prefixWord ++ tailWord_1408546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408546).length < 2 ^ (prefixWord ++ tailWord_1408546).sum := by decide
  have hdescent : baseEnd_1408546 < baseStart_1408546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408562 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5]
def baseStart_1408562 : Nat := 118140960795 + 1408562 * 2 ^ 59
def prefixEnd_1408562 : Nat := 4983230072969 + 3 ^ 40 * 1408562 * 2
def baseEnd_1408562 : Nat := 723269337658423228397147

theorem tailTrace_1408562 : CollatzResearch.WordTrace tailWord_1408562 prefixEnd_1408562 723269337658423228397147 := by
  unfold tailWord_1408562
  simp only [CollatzResearch.WordTrace]
  refine ⟨12843619180756978020622985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34249651148685274721661293 12843619180756978020622985)
  ·
    refine ⟨9632714385567733515467239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12843619180756978020622985 9632714385567733515467239)
    ·
      refine ⟨14449071578351600273200859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9632714385567733515467239 14449071578351600273200859)
      ·
        refine ⟨21673607367527400409801289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14449071578351600273200859 21673607367527400409801289)
        ·
          refine ⟨16255205525645550307350967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21673607367527400409801289 16255205525645550307350967)
          ·
            refine ⟨24382808288468325461026451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16255205525645550307350967 24382808288468325461026451)
            ·
              refine ⟨36574212432702488191539677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24382808288468325461026451 36574212432702488191539677)
              ·
                refine ⟨13715329662263433071827379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36574212432702488191539677 13715329662263433071827379)
                ·
                  refine ⟨20572994493395149607741069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13715329662263433071827379 20572994493395149607741069)
                  ·
                    refine ⟨7714872935023181102902901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20572994493395149607741069 7714872935023181102902901)
                    ·
                      refine ⟨723269337658423228397147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7714872935023181102902901 723269337658423228397147)
                      ·
                        rfl

theorem cell23_1408562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_1408562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408562 prefixEnd_1408562 := by exact prefixLift 1408562
  have htrace : WordTrace (prefixWord ++ tailWord_1408562) baseStart_1408562 baseEnd_1408562 := by
    simpa [prefixWord, tailWord_1408562, baseEnd_1408562] using wordTrace_append hprefix tailTrace_1408562
  have hstable : (prefixWord ++ tailWord_1408562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408562).length < 2 ^ (prefixWord ++ tailWord_1408562).sum := by decide
  have hdescent : baseEnd_1408562 < baseStart_1408562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408563 : List Nat := [1, 1, 1, 2, 4, 3, 4, 1, 1, 3, 2]
def baseStart_1408563 : Nat := 118140960795 + 1408563 * 2 ^ 59
def prefixEnd_1408563 : Nat := 4983230072969 + 3 ^ 40 * 1408563 * 2
def baseEnd_1408563 : Nat := 723269851139077724484643

theorem tailTrace_1408563 : CollatzResearch.WordTrace tailWord_1408563 prefixEnd_1408563 723269851139077724484643 := by
  unfold tailWord_1408563
  simp only [CollatzResearch.WordTrace]
  refine ⟨51374513196024289253278343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34249675464016192835518895 51374513196024289253278343)
  ·
    refine ⟨77061769794036433879917515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51374513196024289253278343 77061769794036433879917515)
    ·
      refine ⟨115592654691054650819876273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77061769794036433879917515 115592654691054650819876273)
      ·
        refine ⟨86694491018290988114907205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115592654691054650819876273 86694491018290988114907205)
        ·
          refine ⟨16255217065929560271545101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86694491018290988114907205 16255217065929560271545101)
          ·
            refine ⟨6095706399723585101829413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16255217065929560271545101 6095706399723585101829413)
            ·
              refine ⟨1142944949948172206593015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6095706399723585101829413 1142944949948172206593015)
              ·
                refine ⟨1714417424922258309889523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1142944949948172206593015 1714417424922258309889523)
                ·
                  refine ⟨2571626137383387464834285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1714417424922258309889523 2571626137383387464834285)
                  ·
                    refine ⟨964359801518770299312857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2571626137383387464834285 964359801518770299312857)
                    ·
                      refine ⟨723269851139077724484643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 964359801518770299312857 723269851139077724484643)
                      ·
                        rfl

theorem cell23_1408563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 1, 3, 2].length) (baseStart_1408563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408563 prefixEnd_1408563 := by exact prefixLift 1408563
  have htrace : WordTrace (prefixWord ++ tailWord_1408563) baseStart_1408563 baseEnd_1408563 := by
    simpa [prefixWord, tailWord_1408563, baseEnd_1408563] using wordTrace_append hprefix tailTrace_1408563
  have hstable : (prefixWord ++ tailWord_1408563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408563).length < 2 ^ (prefixWord ++ tailWord_1408563).sum := by decide
  have hdescent : baseEnd_1408563 < baseStart_1408563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408644 : List Nat := [2, 3, 2, 1, 5, 1, 2, 1, 2, 2, 2]
def baseStart_1408644 : Nat := 118140960795 + 1408644 * 2 ^ 59
def prefixEnd_1408644 : Nat := 4983230072969 + 3 ^ 40 * 1408644 * 2
def baseEnd_1408644 : Nat := 723311443072091907571771

theorem tailTrace_1408644 : CollatzResearch.WordTrace tailWord_1408644 prefixEnd_1408644 723311443072091907571771 := by
  unfold tailWord_1408644
  simp only [CollatzResearch.WordTrace]
  refine ⟨25688733754365420043488493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34251645005820560057984657 25688733754365420043488493)
  ·
    refine ⟨9633275157887032516308185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25688733754365420043488493 9633275157887032516308185)
    ·
      refine ⟨7224956368415274387231139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9633275157887032516308185 7224956368415274387231139)
      ·
        refine ⟨10837434552622911580846709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7224956368415274387231139 10837434552622911580846709)
        ·
          refine ⟨1016009489308397960704379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10837434552622911580846709 1016009489308397960704379)
          ·
            refine ⟨1524014233962596941056569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1016009489308397960704379 1524014233962596941056569)
            ·
              refine ⟨1143010675471947705792427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1524014233962596941056569 1143010675471947705792427)
              ·
                refine ⟨1714516013207921558688641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1143010675471947705792427 1714516013207921558688641)
                ·
                  refine ⟨1285887009905941169016481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1714516013207921558688641 1285887009905941169016481)
                  ·
                    refine ⟨964415257429455876762361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1285887009905941169016481 964415257429455876762361)
                    ·
                      refine ⟨723311443072091907571771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 964415257429455876762361 723311443072091907571771)
                      ·
                        rfl

theorem cell23_1408644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_1408644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408644 prefixEnd_1408644 := by exact prefixLift 1408644
  have htrace : WordTrace (prefixWord ++ tailWord_1408644) baseStart_1408644 baseEnd_1408644 := by
    simpa [prefixWord, tailWord_1408644, baseEnd_1408644] using wordTrace_append hprefix tailTrace_1408644
  have hstable : (prefixWord ++ tailWord_1408644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408644).length < 2 ^ (prefixWord ++ tailWord_1408644).sum := by decide
  have hdescent : baseEnd_1408644 < baseStart_1408644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408710 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_1408710 : Nat := 118140960795 + 1408710 * 2 ^ 59
def prefixEnd_1408710 : Nat := 4983230072969 + 3 ^ 40 * 1408710 * 2
def baseEnd_1408710 : Nat := 241115110931762883115489

theorem tailTrace_1408710 : CollatzResearch.WordTrace tailWord_1408710 prefixEnd_1408710 241115110931762883115489 := by
  unfold tailWord_1408710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1605621085202866667464987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34253249817661155572586389 1605621085202866667464987)
  ·
    refine ⟨2408431627804300001197481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1605621085202866667464987 2408431627804300001197481)
    ·
      refine ⟨1806323720853225000898111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2408431627804300001197481 1806323720853225000898111)
      ·
        refine ⟨2709485581279837501347167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1806323720853225000898111 2709485581279837501347167)
        ·
          refine ⟨4064228371919756252020751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2709485581279837501347167 4064228371919756252020751)
          ·
            refine ⟨6096342557879634378031127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4064228371919756252020751 6096342557879634378031127)
            ·
              refine ⟨9144513836819451567046691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6096342557879634378031127 9144513836819451567046691)
              ·
                refine ⟨13716770755229177350570037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9144513836819451567046691 13716770755229177350570037)
                ·
                  refine ⟨1285947258302735376615941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13716770755229177350570037 1285947258302735376615941)
                  ·
                    refine ⟨241115110931762883115489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1285947258302735376615941 241115110931762883115489)
                    ·
                      rfl

theorem cell23_1408710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_1408710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408710 prefixEnd_1408710 := by exact prefixLift 1408710
  have htrace : WordTrace (prefixWord ++ tailWord_1408710) baseStart_1408710 baseEnd_1408710 := by
    simpa [prefixWord, tailWord_1408710, baseEnd_1408710] using wordTrace_append hprefix tailTrace_1408710
  have hstable : (prefixWord ++ tailWord_1408710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408710).length < 2 ^ (prefixWord ++ tailWord_1408710).sum := by decide
  have hdescent : baseEnd_1408710 < baseStart_1408710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408750 : List Nat := [4, 1, 2, 1, 1, 2, 1, 6, 1, 1, 3]
def baseStart_1408750 : Nat := 118140960795 + 1408750 * 2 ^ 59
def prefixEnd_1408750 : Nat := 4983230072969 + 3 ^ 40 * 1408750 * 2
def baseEnd_1408750 : Nat := 723365872021468492846283

theorem tailTrace_1408750 : CollatzResearch.WordTrace tailWord_1408750 prefixEnd_1408750 723365872021468492846283 := by
  unfold tailWord_1408750
  simp only [CollatzResearch.WordTrace]
  refine ⟨6422666705793352523791963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34254222430897880126890469 6422666705793352523791963)
  ·
    refine ⟨9634000058690028785687945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6422666705793352523791963 9634000058690028785687945)
    ·
      refine ⟨7225500044017521589265959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9634000058690028785687945 7225500044017521589265959)
      ·
        refine ⟨10838250066026282383898939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7225500044017521589265959 10838250066026282383898939)
        ·
          refine ⟨16257375099039423575848409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10838250066026282383898939 16257375099039423575848409)
          ·
            refine ⟨12193031324279567681886307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16257375099039423575848409 12193031324279567681886307)
            ·
              refine ⟨18289546986419351522829461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12193031324279567681886307 18289546986419351522829461)
              ·
                refine ⟨857322514988407102632631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18289546986419351522829461 857322514988407102632631)
                ·
                  refine ⟨1285983772482610653948947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 857322514988407102632631 1285983772482610653948947)
                  ·
                    refine ⟨1928975658723915980923421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1285983772482610653948947 1928975658723915980923421)
                    ·
                      refine ⟨723365872021468492846283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1928975658723915980923421 723365872021468492846283)
                      ·
                        rfl

theorem cell23_1408750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_1408750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408750 prefixEnd_1408750 := by exact prefixLift 1408750
  have htrace : WordTrace (prefixWord ++ tailWord_1408750) baseStart_1408750 baseEnd_1408750 := by
    simpa [prefixWord, tailWord_1408750, baseEnd_1408750] using wordTrace_append hprefix tailTrace_1408750
  have hstable : (prefixWord ++ tailWord_1408750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408750).length < 2 ^ (prefixWord ++ tailWord_1408750).sum := by decide
  have hdescent : baseEnd_1408750 < baseStart_1408750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408759 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 5]
def baseStart_1408759 : Nat := 118140960795 + 1408759 * 2 ^ 59
def prefixEnd_1408759 : Nat := 4983230072969 + 3 ^ 40 * 1408759 * 2
def baseEnd_1408759 : Nat := 723370493347358957633741

theorem tailTrace_1408759 : CollatzResearch.WordTrace tailWord_1408759 prefixEnd_1408759 723370493347358957633741 := by
  unfold tailWord_1408759
  simp only [CollatzResearch.WordTrace]
  refine ⟨51381661903314214727413331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34254441268876143151608887 51381661903314214727413331)
  ·
    refine ⟨77072492854971322091119997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51381661903314214727413331 77072492854971322091119997)
    ·
      refine ⟨28902184820614245784169999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77072492854971322091119997 28902184820614245784169999)
      ·
        refine ⟨43353277230921368676254999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28902184820614245784169999 43353277230921368676254999)
        ·
          refine ⟨65029915846382053014382499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43353277230921368676254999 65029915846382053014382499)
          ·
            refine ⟨97544873769573079521573749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65029915846382053014382499 97544873769573079521573749)
            ·
              refine ⟨9144831915897476205147539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97544873769573079521573749 9144831915897476205147539)
              ·
                refine ⟨13717247873846214307721309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9144831915897476205147539 13717247873846214307721309)
                ·
                  refine ⟨5143967952692330365395491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13717247873846214307721309 5143967952692330365395491)
                  ·
                    refine ⟨7715951929038495548093237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5143967952692330365395491 7715951929038495548093237)
                    ·
                      refine ⟨723370493347358957633741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7715951929038495548093237 723370493347358957633741)
                      ·
                        rfl

theorem cell23_1408759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_1408759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408759 prefixEnd_1408759 := by exact prefixLift 1408759
  have htrace : WordTrace (prefixWord ++ tailWord_1408759) baseStart_1408759 baseEnd_1408759 := by
    simpa [prefixWord, tailWord_1408759, baseEnd_1408759] using wordTrace_append hprefix tailTrace_1408759
  have hstable : (prefixWord ++ tailWord_1408759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408759).length < 2 ^ (prefixWord ++ tailWord_1408759).sum := by decide
  have hdescent : baseEnd_1408759 < baseStart_1408759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408816 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 1, 9, 2]
def baseStart_1408816 : Nat := 118140960795 + 1408816 * 2 ^ 59
def prefixEnd_1408816 : Nat := 4983230072969 + 3 ^ 40 * 1408816 * 2
def baseEnd_1408816 : Nat := 723399761744665234620979

theorem tailTrace_1408816 : CollatzResearch.WordTrace tailWord_1408816 prefixEnd_1408816 723399761744665234620979 := by
  unfold tailWord_1408816
  simp only [CollatzResearch.WordTrace]
  refine ⟨25691870432053856731119151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34255827242738475641492201 25691870432053856731119151)
  ·
    refine ⟨38537805648080785096678727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25691870432053856731119151 38537805648080785096678727)
    ·
      refine ⟨57806708472121177645018091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38537805648080785096678727 57806708472121177645018091)
      ·
        refine ⟨86710062708181766467527137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57806708472121177645018091 86710062708181766467527137)
        ·
          refine ⟨65032547031136324850645353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86710062708181766467527137 65032547031136324850645353)
          ·
            refine ⟨48774410273352243637984015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65032547031136324850645353 48774410273352243637984015)
            ·
              refine ⟨73161615410028365456976023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48774410273352243637984015 73161615410028365456976023)
              ·
                refine ⟨109742423115042548185464035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73161615410028365456976023 109742423115042548185464035)
                ·
                  refine ⟨164613634672563822278196053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109742423115042548185464035 164613634672563822278196053)
                  ·
                    refine ⟨964533015659553646161305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 164613634672563822278196053 964533015659553646161305)
                    ·
                      refine ⟨723399761744665234620979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 964533015659553646161305 723399761744665234620979)
                      ·
                        rfl

theorem cell23_1408816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 9, 2].length) (baseStart_1408816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408816 prefixEnd_1408816 := by exact prefixLift 1408816
  have htrace : WordTrace (prefixWord ++ tailWord_1408816) baseStart_1408816 baseEnd_1408816 := by
    simpa [prefixWord, tailWord_1408816, baseEnd_1408816] using wordTrace_append hprefix tailTrace_1408816
  have hstable : (prefixWord ++ tailWord_1408816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408816).length < 2 ^ (prefixWord ++ tailWord_1408816).sum := by decide
  have hdescent : baseEnd_1408816 < baseStart_1408816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408876 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 4]
def baseStart_1408876 : Nat := 118140960795 + 1408876 * 2 ^ 59
def prefixEnd_1408876 : Nat := 4983230072969 + 3 ^ 40 * 1408876 * 2
def baseEnd_1408876 : Nat := 723430570583934999870703

theorem tailTrace_1408876 : CollatzResearch.WordTrace tailWord_1408876 prefixEnd_1408876 723430570583934999870703 := by
  unfold tailWord_1408876
  simp only [CollatzResearch.WordTrace]
  refine ⟨25692964621945171854711241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34257286162593562472948321 25692964621945171854711241)
  ·
    refine ⟨19269723466458878891033431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25692964621945171854711241 19269723466458878891033431)
    ·
      refine ⟨28904585199688318336550147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19269723466458878891033431 28904585199688318336550147)
      ·
        refine ⟨43356877799532477504825221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28904585199688318336550147 43356877799532477504825221)
        ·
          refine ⟨8129414587412339532154729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43356877799532477504825221 8129414587412339532154729)
          ·
            refine ⟨6097060940559254649116047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8129414587412339532154729 6097060940559254649116047)
            ·
              refine ⟨9145591410838881973674071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6097060940559254649116047 9145591410838881973674071)
              ·
                refine ⟨13718387116258322960511107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9145591410838881973674071 13718387116258322960511107)
                ·
                  refine ⟨20577580674387484440766661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13718387116258322960511107 20577580674387484440766661)
                  ·
                    refine ⟨3858296376447653332643749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20577580674387484440766661 3858296376447653332643749)
                    ·
                      refine ⟨723430570583934999870703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3858296376447653332643749 723430570583934999870703)
                      ·
                        rfl

theorem cell23_1408876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_1408876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408876 prefixEnd_1408876 := by exact prefixLift 1408876
  have htrace : WordTrace (prefixWord ++ tailWord_1408876) baseStart_1408876 baseEnd_1408876 := by
    simpa [prefixWord, tailWord_1408876, baseEnd_1408876] using wordTrace_append hprefix tailTrace_1408876
  have hstable : (prefixWord ++ tailWord_1408876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408876).length < 2 ^ (prefixWord ++ tailWord_1408876).sum := by decide
  have hdescent : baseEnd_1408876 < baseStart_1408876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408896 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 3]
def baseStart_1408896 : Nat := 118140960795 + 1408896 * 2 ^ 59
def prefixEnd_1408896 : Nat := 4983230072969 + 3 ^ 40 * 1408896 * 2
def baseEnd_1408896 : Nat := 723440840197024921620611

theorem tailTrace_1408896 : CollatzResearch.WordTrace tailWord_1408896 prefixEnd_1408896 723440840197024921620611 := by
  unfold tailWord_1408896
  simp only [CollatzResearch.WordTrace]
  refine ⟨25693329351908943562575271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34257772469211924750100361 25693329351908943562575271)
  ·
    refine ⟨38539994027863415343862907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25693329351908943562575271 38539994027863415343862907)
    ·
      refine ⟨57809991041795123015794361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38539994027863415343862907 57809991041795123015794361)
      ·
        refine ⟨43357493281346342261845771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57809991041795123015794361 43357493281346342261845771)
        ·
          refine ⟨65036239922019513392768657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43357493281346342261845771 65036239922019513392768657)
          ·
            refine ⟨48777179941514635044576493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65036239922019513392768657 48777179941514635044576493)
            ·
              refine ⟨18291442478067988141716185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48777179941514635044576493 18291442478067988141716185)
              ·
                refine ⟨13718581858550991106287139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18291442478067988141716185 13718581858550991106287139)
                ·
                  refine ⟨20577872787826486659430709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13718581858550991106287139 20577872787826486659430709)
                  ·
                    refine ⟨1929175573858733124321629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20577872787826486659430709 1929175573858733124321629)
                    ·
                      refine ⟨723440840197024921620611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1929175573858733124321629 723440840197024921620611)
                      ·
                        rfl

theorem cell23_1408896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 3].length) (baseStart_1408896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408896 prefixEnd_1408896 := by exact prefixLift 1408896
  have htrace : WordTrace (prefixWord ++ tailWord_1408896) baseStart_1408896 baseEnd_1408896 := by
    simpa [prefixWord, tailWord_1408896, baseEnd_1408896] using wordTrace_append hprefix tailTrace_1408896
  have hstable : (prefixWord ++ tailWord_1408896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408896).length < 2 ^ (prefixWord ++ tailWord_1408896).sum := by decide
  have hdescent : baseEnd_1408896 < baseStart_1408896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408914 : List Nat := [3, 2, 3, 2, 1, 1, 3, 2, 2, 2, 2]
def baseStart_1408914 : Nat := 118140960795 + 1408914 * 2 ^ 59
def prefixEnd_1408914 : Nat := 4983230072969 + 3 ^ 40 * 1408914 * 2
def baseEnd_1408914 : Nat := 723450082848805851195529

theorem tailTrace_1408914 : CollatzResearch.WordTrace tailWord_1408914 prefixEnd_1408914 723450082848805851195529 := by
  unfold tailWord_1408914
  simp only [CollatzResearch.WordTrace]
  refine ⟨12846828804438169049826449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34258210145168450799537197 12846828804438169049826449)
  ·
    refine ⟨9635121603328626787369837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12846828804438169049826449 9635121603328626787369837)
    ·
      refine ⟨3613170601248235045263689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9635121603328626787369837 3613170601248235045263689)
      ·
        refine ⟨2709877950936176283947767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3613170601248235045263689 2709877950936176283947767)
        ·
          refine ⟨4064816926404264425921651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2709877950936176283947767 4064816926404264425921651)
          ·
            refine ⟨6097225389606396638882477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4064816926404264425921651 6097225389606396638882477)
            ·
              refine ⟨2286459521102398739580929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6097225389606396638882477 2286459521102398739580929)
              ·
                refine ⟨1714844640826799054685697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2286459521102398739580929 1714844640826799054685697)
                ·
                  refine ⟨1286133480620099291014273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1714844640826799054685697 1286133480620099291014273)
                  ·
                    refine ⟨964600110465074468260705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1286133480620099291014273 964600110465074468260705)
                    ·
                      refine ⟨723450082848805851195529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 964600110465074468260705 723450082848805851195529)
                      ·
                        rfl

theorem cell23_1408914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_1408914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408914 prefixEnd_1408914 := by exact prefixLift 1408914
  have htrace : WordTrace (prefixWord ++ tailWord_1408914) baseStart_1408914 baseEnd_1408914 := by
    simpa [prefixWord, tailWord_1408914, baseEnd_1408914] using wordTrace_append hprefix tailTrace_1408914
  have hstable : (prefixWord ++ tailWord_1408914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408914).length < 2 ^ (prefixWord ++ tailWord_1408914).sum := by decide
  have hdescent : baseEnd_1408914 < baseStart_1408914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408920 : List Nat := [2, 1, 2, 6, 1, 1, 2, 1, 7]
def baseStart_1408920 : Nat := 118140960795 + 1408920 * 2 ^ 59
def prefixEnd_1408920 : Nat := 4983230072969 + 3 ^ 40 * 1408920 * 2
def baseEnd_1408920 : Nat := 80383684859192536413389

theorem tailTrace_1408920 : CollatzResearch.WordTrace tailWord_1408920 prefixEnd_1408920 80383684859192536413389 := by
  unfold tailWord_1408920
  simp only [CollatzResearch.WordTrace]
  refine ⟨25693767027865469612012107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34258356037153959482682809 25693767027865469612012107)
  ·
    refine ⟨38540650541798204418018161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25693767027865469612012107 38540650541798204418018161)
    ·
      refine ⟨28905487906348653313513621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38540650541798204418018161 28905487906348653313513621)
      ·
        refine ⟨1354944745610093124070951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28905487906348653313513621 1354944745610093124070951)
        ·
          refine ⟨2032417118415139686106427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1354944745610093124070951 2032417118415139686106427)
          ·
            refine ⟨3048625677622709529159641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2032417118415139686106427 3048625677622709529159641)
            ·
              refine ⟨2286469258217032146869731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3048625677622709529159641 2286469258217032146869731)
              ·
                refine ⟨3429703887325548220304597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2286469258217032146869731 3429703887325548220304597)
                ·
                  refine ⟨80383684859192536413389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3429703887325548220304597 80383684859192536413389)
                  ·
                    rfl

theorem cell23_1408920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 7].length) (baseStart_1408920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408920 prefixEnd_1408920 := by exact prefixLift 1408920
  have htrace : WordTrace (prefixWord ++ tailWord_1408920) baseStart_1408920 baseEnd_1408920 := by
    simpa [prefixWord, tailWord_1408920, baseEnd_1408920] using wordTrace_append hprefix tailTrace_1408920
  have hstable : (prefixWord ++ tailWord_1408920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408920).length < 2 ^ (prefixWord ++ tailWord_1408920).sum := by decide
  have hdescent : baseEnd_1408920 < baseStart_1408920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408953 : List Nat := [1, 2, 1, 4, 2, 1, 2, 3, 2, 1, 4]
def baseStart_1408953 : Nat := 118140960795 + 1408953 * 2 ^ 59
def prefixEnd_1408953 : Nat := 4983230072969 + 3 ^ 40 * 1408953 * 2
def baseEnd_1408953 : Nat := 723470108594331198607849

theorem tailTrace_1408953 : CollatzResearch.WordTrace tailWord_1408953 prefixEnd_1408953 723470108594331198607849 := by
  unfold tailWord_1408953
  simp only [CollatzResearch.WordTrace]
  refine ⟨51388737664611385859975513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34259158443074257239983675 51388737664611385859975513)
  ·
    refine ⟨38541553248458539394981635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51388737664611385859975513 38541553248458539394981635)
    ·
      refine ⟨57812329872687809092472453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38541553248458539394981635 57812329872687809092472453)
      ·
        refine ⟨10839811851128964204838585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57812329872687809092472453 10839811851128964204838585)
        ·
          refine ⟨8129858888346723153628939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10839811851128964204838585 8129858888346723153628939)
          ·
            refine ⟨12194788332520084730443409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8129858888346723153628939 12194788332520084730443409)
            ·
              refine ⟨9146091249390063547832557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12194788332520084730443409 9146091249390063547832557)
              ·
                refine ⟨3429784218521273830437209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9146091249390063547832557 3429784218521273830437209)
                ·
                  refine ⟨2572338163890955372827907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3429784218521273830437209 2572338163890955372827907)
                  ·
                    refine ⟨3858507245836433059241861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2572338163890955372827907 3858507245836433059241861)
                    ·
                      refine ⟨723470108594331198607849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3858507245836433059241861 723470108594331198607849)
                      ·
                        rfl

theorem cell23_1408953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_1408953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408953 prefixEnd_1408953 := by exact prefixLift 1408953
  have htrace : WordTrace (prefixWord ++ tailWord_1408953) baseStart_1408953 baseEnd_1408953 := by
    simpa [prefixWord, tailWord_1408953, baseEnd_1408953] using wordTrace_append hprefix tailTrace_1408953
  have hstable : (prefixWord ++ tailWord_1408953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408953).length < 2 ^ (prefixWord ++ tailWord_1408953).sum := by decide
  have hdescent : baseEnd_1408953 < baseStart_1408953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408976 : List Nat := [2, 1, 1, 1, 1, 2, 6, 1, 8]
def baseStart_1408976 : Nat := 118140960795 + 1408976 * 2 ^ 59
def prefixEnd_1408976 : Nat := 4983230072969 + 3 ^ 40 * 1408976 * 2
def baseEnd_1408976 : Nat := 80386879849931623180027

theorem tailTrace_1408976 : CollatzResearch.WordTrace tailWord_1408976 prefixEnd_1408976 80386879849931623180027 := by
  unfold tailWord_1408976
  simp only [CollatzResearch.WordTrace]
  refine ⟨25694788271764030394031391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34259717695685373858708521 25694788271764030394031391)
  ·
    refine ⟨38542182407646045591047087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25694788271764030394031391 38542182407646045591047087)
    ·
      refine ⟨57813273611469068386570631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38542182407646045591047087 57813273611469068386570631)
      ·
        refine ⟨86719910417203602579855947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57813273611469068386570631 86719910417203602579855947)
        ·
          refine ⟨130079865625805403869783921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86719910417203602579855947 130079865625805403869783921)
          ·
            refine ⟨97559899219354052902337941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130079865625805403869783921 97559899219354052902337941)
            ·
              refine ⟨4573120275907221229797091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 97559899219354052902337941 4573120275907221229797091)
              ·
                refine ⟨6859680413860831844695637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4573120275907221229797091 6859680413860831844695637)
                ·
                  refine ⟨80386879849931623180027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6859680413860831844695637 80386879849931623180027)
                  ·
                    rfl

theorem cell23_1408976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 8].length) (baseStart_1408976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408976 prefixEnd_1408976 := by exact prefixLift 1408976
  have htrace : WordTrace (prefixWord ++ tailWord_1408976) baseStart_1408976 baseEnd_1408976 := by
    simpa [prefixWord, tailWord_1408976, baseEnd_1408976] using wordTrace_append hprefix tailTrace_1408976
  have hstable : (prefixWord ++ tailWord_1408976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408976).length < 2 ^ (prefixWord ++ tailWord_1408976).sum := by decide
  have hdescent : baseEnd_1408976 < baseStart_1408976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409023 : List Nat := [1, 1, 2, 2, 1, 2, 1, 7, 1, 5]
def baseStart_1409023 : Nat := 118140960795 + 1409023 * 2 ^ 59
def prefixEnd_1409023 : Nat := 4983230072969 + 3 ^ 40 * 1409023 * 2
def baseEnd_1409023 : Nat := 241168684080048641577509

theorem tailTrace_1409023 : CollatzResearch.WordTrace tailWord_1409023 prefixEnd_1409023 241168684080048641577509 := by
  unfold tailWord_1409023
  simp only [CollatzResearch.WordTrace]
  refine ⟨51391290774357787815023723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34260860516238525210015815 51391290774357787815023723)
  ·
    refine ⟨77086936161536681722535585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51391290774357787815023723 77086936161536681722535585)
    ·
      refine ⟨57815202121152511291901689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77086936161536681722535585 57815202121152511291901689)
      ·
        refine ⟨43361401590864383468926267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57815202121152511291901689 43361401590864383468926267)
        ·
          refine ⟨65042102386296575203389401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43361401590864383468926267 65042102386296575203389401)
          ·
            refine ⟨48781576789722431402542051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65042102386296575203389401 48781576789722431402542051)
            ·
              refine ⟨73172365184583647103813077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48781576789722431402542051 73172365184583647103813077)
              ·
                refine ⟨1714977309013679228995619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 73172365184583647103813077 1714977309013679228995619)
                ·
                  refine ⟨2572465963520518843493429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1714977309013679228995619 2572465963520518843493429)
                  ·
                    refine ⟨241168684080048641577509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2572465963520518843493429 241168684080048641577509)
                    ·
                      rfl

theorem cell23_1409023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 5].length) (baseStart_1409023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409023 prefixEnd_1409023 := by exact prefixLift 1409023
  have htrace : WordTrace (prefixWord ++ tailWord_1409023) baseStart_1409023 baseEnd_1409023 := by
    simpa [prefixWord, tailWord_1409023, baseEnd_1409023] using wordTrace_append hprefix tailTrace_1409023
  have hstable : (prefixWord ++ tailWord_1409023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409023).length < 2 ^ (prefixWord ++ tailWord_1409023).sum := by decide
  have hdescent : baseEnd_1409023 < baseStart_1409023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409043 : List Nat := [1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 4]
def baseStart_1409043 : Nat := 118140960795 + 1409043 * 2 ^ 59
def prefixEnd_1409043 : Nat := 4983230072969 + 3 ^ 40 * 1409043 * 2
def baseEnd_1409043 : Nat := 723516321853235846482435

theorem tailTrace_1409043 : CollatzResearch.WordTrace tailWord_1409043 prefixEnd_1409043 723516321853235846482435 := by
  unfold tailWord_1409043
  simp only [CollatzResearch.WordTrace]
  refine ⟨51392020234285331230751783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34261346822856887487167855 51392020234285331230751783)
  ·
    refine ⟨77088030351427996846127675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51392020234285331230751783 77088030351427996846127675)
    ·
      refine ⟨115632045527141995269191513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77088030351427996846127675 115632045527141995269191513)
      ·
        refine ⟨86724034145356496451893635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115632045527141995269191513 86724034145356496451893635)
        ·
          refine ⟨130086051218034744677840453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86724034145356496451893635 130086051218034744677840453)
          ·
            refine ⟨24391134603381514627095085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130086051218034744677840453 24391134603381514627095085)
            ·
              refine ⟨9146675476268067985160657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24391134603381514627095085 9146675476268067985160657)
              ·
                refine ⟨6860006607201050988870493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9146675476268067985160657 6860006607201050988870493)
                ·
                  refine ⟨2572502477700394120826435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6860006607201050988870493 2572502477700394120826435)
                  ·
                    refine ⟨3858753716550591181239653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2572502477700394120826435 3858753716550591181239653)
                    ·
                      refine ⟨723516321853235846482435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3858753716550591181239653 723516321853235846482435)
                      ·
                        rfl

theorem cell23_1409043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 4].length) (baseStart_1409043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409043 prefixEnd_1409043 := by exact prefixLift 1409043
  have htrace : WordTrace (prefixWord ++ tailWord_1409043) baseStart_1409043 baseEnd_1409043 := by
    simpa [prefixWord, tailWord_1409043, baseEnd_1409043] using wordTrace_append hprefix tailTrace_1409043
  have hstable : (prefixWord ++ tailWord_1409043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409043).length < 2 ^ (prefixWord ++ tailWord_1409043).sum := by decide
  have hdescent : baseEnd_1409043 < baseStart_1409043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409064 : List Nat := [2, 1, 5, 3, 1, 1, 1, 1, 1, 5, 2]
def baseStart_1409064 : Nat := 118140960795 + 1409064 * 2 ^ 59
def prefixEnd_1409064 : Nat := 4983230072969 + 3 ^ 40 * 1409064 * 2
def baseEnd_1409064 : Nat := 723527104946980264319839

theorem tailTrace_1409064 : CollatzResearch.WordTrace tailWord_1409064 prefixEnd_1409064 723527104946980264319839 := by
  unfold tailWord_1409064
  simp only [CollatzResearch.WordTrace]
  refine ⟨25696393083604625908633123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34261857444806167878177497 25696393083604625908633123)
  ·
    refine ⟨38544589625406938862949685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25696393083604625908633123 38544589625406938862949685)
    ·
      refine ⟨3613555277381900518401533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38544589625406938862949685 3613555277381900518401533)
      ·
        refine ⟨1355083229018212694400575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3613555277381900518401533 1355083229018212694400575)
        ·
          refine ⟨2032624843527319041600863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1355083229018212694400575 2032624843527319041600863)
          ·
            refine ⟨3048937265290978562401295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2032624843527319041600863 3048937265290978562401295)
            ·
              refine ⟨4573405897936467843601943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3048937265290978562401295 4573405897936467843601943)
              ·
                refine ⟨6860108846904701765402915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4573405897936467843601943 6860108846904701765402915)
                ·
                  refine ⟨10290163270357052648104373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6860108846904701765402915 10290163270357052648104373)
                  ·
                    refine ⟨964702806595973685759785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10290163270357052648104373 964702806595973685759785)
                    ·
                      refine ⟨723527104946980264319839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 964702806595973685759785 723527104946980264319839)
                      ·
                        rfl

theorem cell23_1409064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_1409064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409064 prefixEnd_1409064 := by exact prefixLift 1409064
  have htrace : WordTrace (prefixWord ++ tailWord_1409064) baseStart_1409064 baseEnd_1409064 := by
    simpa [prefixWord, tailWord_1409064, baseEnd_1409064] using wordTrace_append hprefix tailTrace_1409064
  have hstable : (prefixWord ++ tailWord_1409064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409064).length < 2 ^ (prefixWord ++ tailWord_1409064).sum := by decide
  have hdescent : baseEnd_1409064 < baseStart_1409064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409070 : List Nat := [4, 1, 3, 1, 1, 2, 2, 2, 1, 6]
def baseStart_1409070 : Nat := 118140960795 + 1409070 * 2 ^ 59
def prefixEnd_1409070 : Nat := 4983230072969 + 3 ^ 40 * 1409070 * 2
def baseEnd_1409070 : Nat := 241176728610302413614937

theorem tailTrace_1409070 : CollatzResearch.WordTrace tailWord_1409070 prefixEnd_1409070 241176728610302413614937 := by
  unfold tailWord_1409070
  simp only [CollatzResearch.WordTrace]
  refine ⟨6424125625648439355248083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34262003336791676561323109 6424125625648439355248083)
  ·
    refine ⟨9636188438472659032872125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6424125625648439355248083 9636188438472659032872125)
    ·
      refine ⟨3613570664427247137327047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9636188438472659032872125 3613570664427247137327047)
      ·
        refine ⟨5420355996640870705990571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3613570664427247137327047 5420355996640870705990571)
        ·
          refine ⟨8130533994961306058985857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5420355996640870705990571 8130533994961306058985857)
          ·
            refine ⟨6097900496220979544239393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8130533994961306058985857 6097900496220979544239393)
            ·
              refine ⟨4573425372165734658179545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6097900496220979544239393 4573425372165734658179545)
              ·
                refine ⟨3430069029124300993634659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4573425372165734658179545 3430069029124300993634659)
                ·
                  refine ⟨5145103543686451490451989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3430069029124300993634659 5145103543686451490451989)
                  ·
                    refine ⟨241176728610302413614937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5145103543686451490451989 241176728610302413614937)
                    ·
                      rfl

theorem cell23_1409070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_1409070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409070 prefixEnd_1409070 := by exact prefixLift 1409070
  have htrace : WordTrace (prefixWord ++ tailWord_1409070) baseStart_1409070 baseEnd_1409070 := by
    simpa [prefixWord, tailWord_1409070, baseEnd_1409070] using wordTrace_append hprefix tailTrace_1409070
  have hstable : (prefixWord ++ tailWord_1409070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409070).length < 2 ^ (prefixWord ++ tailWord_1409070).sum := by decide
  have hdescent : baseEnd_1409070 < baseStart_1409070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409077 : List Nat := [1, 3, 3, 1, 1, 1, 6, 1, 1, 1, 4]
def baseStart_1409077 : Nat := 118140960795 + 1409077 * 2 ^ 59
def prefixEnd_1409077 : Nat := 4983230072969 + 3 ^ 40 * 1409077 * 2
def baseEnd_1409077 : Nat := 723533780195488713457279

theorem tailTrace_1409077 : CollatzResearch.WordTrace tailWord_1409077 prefixEnd_1409077 723533780195488713457279 := by
  unfold tailWord_1409077
  simp only [CollatzResearch.WordTrace]
  refine ⟨51393260316162155037489485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34262173544108103358326323 51393260316162155037489485)
  ·
    refine ⟨19272472618560808139058557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51393260316162155037489485 19272472618560808139058557)
    ·
      refine ⟨7227177231960303052146959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19272472618560808139058557 7227177231960303052146959)
      ·
        refine ⟨10840765847940454578220439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7227177231960303052146959 10840765847940454578220439)
        ·
          refine ⟨16261148771910681867330659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10840765847940454578220439 16261148771910681867330659)
          ·
            refine ⟨24391723157866022800995989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16261148771910681867330659 24391723157866022800995989)
            ·
              refine ⟨1143362023024969818796687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24391723157866022800995989 1143362023024969818796687)
              ·
                refine ⟨1715043034537454728195031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1143362023024969818796687 1715043034537454728195031)
                ·
                  refine ⟨2572564551806182092292547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1715043034537454728195031 2572564551806182092292547)
                  ·
                    refine ⟨3858846827709273138438821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2572564551806182092292547 3858846827709273138438821)
                    ·
                      refine ⟨723533780195488713457279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3858846827709273138438821 723533780195488713457279)
                      ·
                        rfl

theorem cell23_1409077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_1409077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409077 prefixEnd_1409077 := by exact prefixLift 1409077
  have htrace : WordTrace (prefixWord ++ tailWord_1409077) baseStart_1409077 baseEnd_1409077 := by
    simpa [prefixWord, tailWord_1409077, baseEnd_1409077] using wordTrace_append hprefix tailTrace_1409077
  have hstable : (prefixWord ++ tailWord_1409077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409077).length < 2 ^ (prefixWord ++ tailWord_1409077).sum := by decide
  have hdescent : baseEnd_1409077 < baseStart_1409077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409117 : List Nat := [1, 4, 4, 1, 1, 1, 4, 7]
def baseStart_1409117 : Nat := 118140960795 + 1409117 * 2 ^ 59
def prefixEnd_1409117 : Nat := 4983230072969 + 3 ^ 40 * 1409117 * 2
def baseEnd_1409117 : Nat := 26798308126728465072485

theorem tailTrace_1409117 : CollatzResearch.WordTrace tailWord_1409117 prefixEnd_1409117 26798308126728465072485 := by
  unfold tailWord_1409117
  simp only [CollatzResearch.WordTrace]
  refine ⟨51394719236017241868945605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34263146157344827912630403 51394719236017241868945605)
  ·
    refine ⟨9636509856753232850427301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51394719236017241868945605 9636509856753232850427301)
    ·
      refine ⟨1806845598141231159455119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9636509856753232850427301 1806845598141231159455119)
      ·
        refine ⟨2710268397211846739182679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1806845598141231159455119 2710268397211846739182679)
        ·
          refine ⟨4065402595817770108774019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2710268397211846739182679 4065402595817770108774019)
          ·
            refine ⟨6098103893726655163161029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4065402595817770108774019 6098103893726655163161029)
            ·
              refine ⟨1143394480073747843092693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6098103893726655163161029 1143394480073747843092693)
              ·
                refine ⟨26798308126728465072485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1143394480073747843092693 26798308126728465072485)
                ·
                  rfl

theorem cell23_1409117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 7].length) (baseStart_1409117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409117 prefixEnd_1409117 := by exact prefixLift 1409117
  have htrace : WordTrace (prefixWord ++ tailWord_1409117) baseStart_1409117 baseEnd_1409117 := by
    simpa [prefixWord, tailWord_1409117, baseEnd_1409117] using wordTrace_append hprefix tailTrace_1409117
  have hstable : (prefixWord ++ tailWord_1409117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409117).length < 2 ^ (prefixWord ++ tailWord_1409117).sum := by decide
  have hdescent : baseEnd_1409117 < baseStart_1409117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409123 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 5]
def baseStart_1409123 : Nat := 118140960795 + 1409123 * 2 ^ 59
def prefixEnd_1409123 : Nat := 4983230072969 + 3 ^ 40 * 1409123 * 2
def baseEnd_1409123 : Nat := 723557400305595533482067

theorem tailTrace_1409123 : CollatzResearch.WordTrace tailWord_1409123 prefixEnd_1409123 723557400305595533482067 := by
  unfold tailWord_1409123
  simp only [CollatzResearch.WordTrace]
  refine ⟨51394938073995504893664023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34263292049330336595776015 51394938073995504893664023)
  ·
    refine ⟨77092407110993257340496035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51394938073995504893664023 77092407110993257340496035)
    ·
      refine ⟨115638610666489886010744053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77092407110993257340496035 115638610666489886010744053)
      ·
        refine ⟨10841119749983426813507255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115638610666489886010744053 10841119749983426813507255)
        ·
          refine ⟨16261679624975140220260883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10841119749983426813507255 16261679624975140220260883)
          ·
            refine ⟨24392519437462710330391325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16261679624975140220260883 24392519437462710330391325)
            ·
              refine ⟨9147194789048516373896747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24392519437462710330391325 9147194789048516373896747)
              ·
                refine ⟨13720792183572774560845121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9147194789048516373896747 13720792183572774560845121)
                ·
                  refine ⟨10290594137679580920633841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13720792183572774560845121 10290594137679580920633841)
                  ·
                    refine ⟨7717945603259685690475381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10290594137679580920633841 7717945603259685690475381)
                    ·
                      refine ⟨723557400305595533482067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7717945603259685690475381 723557400305595533482067)
                      ·
                        rfl

theorem cell23_1409123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_1409123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409123 prefixEnd_1409123 := by exact prefixLift 1409123
  have htrace : WordTrace (prefixWord ++ tailWord_1409123) baseStart_1409123 baseEnd_1409123 := by
    simpa [prefixWord, tailWord_1409123, baseEnd_1409123] using wordTrace_append hprefix tailTrace_1409123
  have hstable : (prefixWord ++ tailWord_1409123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409123).length < 2 ^ (prefixWord ++ tailWord_1409123).sum := by decide
  have hdescent : baseEnd_1409123 < baseStart_1409123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409137 : List Nat := [1, 2, 2, 2, 1, 1, 3, 5, 1, 3, 2]
def baseStart_1409137 : Nat := 118140960795 + 1409137 * 2 ^ 59
def prefixEnd_1409137 : Nat := 4983230072969 + 3 ^ 40 * 1409137 * 2
def baseEnd_1409137 : Nat := 723564589034758478707003

theorem tailTrace_1409137 : CollatzResearch.WordTrace tailWord_1409137 prefixEnd_1409137 723564589034758478707003 := by
  unfold tailWord_1409137
  simp only [CollatzResearch.WordTrace]
  refine ⟨51395448695944785284673665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34263632463963190189782443 51395448695944785284673665)
  ·
    refine ⟨38546586521958588963505249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51395448695944785284673665 38546586521958588963505249)
    ·
      refine ⟨28909939891468941722628937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38546586521958588963505249 28909939891468941722628937)
      ·
        refine ⟨21682454918601706291971703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28909939891468941722628937 21682454918601706291971703)
        ·
          refine ⟨32523682377902559437957555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21682454918601706291971703 32523682377902559437957555)
          ·
            refine ⟨48785523566853839156936333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32523682377902559437957555 48785523566853839156936333)
            ·
              refine ⟨18294571337570189683851125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48785523566853839156936333 18294571337570189683851125)
              ·
                refine ⟨1715116062897205282861043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18294571337570189683851125 1715116062897205282861043)
                ·
                  refine ⟨2572674094345807924291565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1715116062897205282861043 2572674094345807924291565)
                  ·
                    refine ⟨964752785379677971609337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2572674094345807924291565 964752785379677971609337)
                    ·
                      refine ⟨723564589034758478707003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 964752785379677971609337 723564589034758478707003)
                      ·
                        rfl

theorem cell23_1409137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 3, 2].length) (baseStart_1409137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409137 prefixEnd_1409137 := by exact prefixLift 1409137
  have htrace : WordTrace (prefixWord ++ tailWord_1409137) baseStart_1409137 baseEnd_1409137 := by
    simpa [prefixWord, tailWord_1409137, baseEnd_1409137] using wordTrace_append hprefix tailTrace_1409137
  have hstable : (prefixWord ++ tailWord_1409137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409137).length < 2 ^ (prefixWord ++ tailWord_1409137).sum := by decide
  have hdescent : baseEnd_1409137 < baseStart_1409137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409170 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_1409170 : Nat := 118140960795 + 1409170 * 2 ^ 59
def prefixEnd_1409170 : Nat := 4983230072969 + 3 ^ 40 * 1409170 * 2
def baseEnd_1409170 : Nat := 723581533896356849594351

theorem tailTrace_1409170 : CollatzResearch.WordTrace tailWord_1409170 prefixEnd_1409170 723581533896356849594351 := by
  unfold tailWord_1409170
  simp only [CollatzResearch.WordTrace]
  refine ⟨12849163076206307980156241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34264434869883487947083309 12849163076206307980156241)
  ·
    refine ⟨9636872307154730985117181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12849163076206307980156241 9636872307154730985117181)
    ·
      refine ⟨3613827115183024119418943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9636872307154730985117181 3613827115183024119418943)
      ·
        refine ⟨5420740672774536179128415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3613827115183024119418943 5420740672774536179128415)
        ·
          refine ⟨8131111009161804268692623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5420740672774536179128415 8131111009161804268692623)
          ·
            refine ⟨12196666513742706403038935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8131111009161804268692623 12196666513742706403038935)
            ·
              refine ⟨18294999770614059604558403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12196666513742706403038935 18294999770614059604558403)
              ·
                refine ⟨27442499655921089406837605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18294999770614059604558403 27442499655921089406837605)
                ·
                  refine ⟨5145468685485204263782051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27442499655921089406837605 5145468685485204263782051)
                  ·
                    refine ⟨7718203028227806395673077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5145468685485204263782051 7718203028227806395673077)
                    ·
                      refine ⟨723581533896356849594351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7718203028227806395673077 723581533896356849594351)
                      ·
                        rfl

theorem cell23_1409170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_1409170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409170 prefixEnd_1409170 := by exact prefixLift 1409170
  have htrace : WordTrace (prefixWord ++ tailWord_1409170) baseStart_1409170 baseEnd_1409170 := by
    simpa [prefixWord, tailWord_1409170, baseEnd_1409170] using wordTrace_append hprefix tailTrace_1409170
  have hstable : (prefixWord ++ tailWord_1409170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409170).length < 2 ^ (prefixWord ++ tailWord_1409170).sum := by decide
  have hdescent : baseEnd_1409170 < baseStart_1409170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409173 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 9]
def baseStart_1409173 : Nat := 118140960795 + 1409173 * 2 ^ 59
def prefixEnd_1409173 : Nat := 4983230072969 + 3 ^ 40 * 1409173 * 2
def baseEnd_1409173 : Nat := 80398119370924481984093

theorem tailTrace_1409173 : CollatzResearch.WordTrace tailWord_1409173 prefixEnd_1409173 80398119370924481984093 := by
  unfold tailWord_1409173
  simp only [CollatzResearch.WordTrace]
  refine ⟨51396761723814363432984173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34264507815876242288656115 51396761723814363432984173)
  ·
    refine ⟨19273785646430386287369065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51396761723814363432984173 19273785646430386287369065)
    ·
      refine ⟨14455339234822789715526799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19273785646430386287369065 14455339234822789715526799)
      ·
        refine ⟨21683008852234184573290199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14455339234822789715526799 21683008852234184573290199)
        ·
          refine ⟨32524513278351276859935299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21683008852234184573290199 32524513278351276859935299)
          ·
            refine ⟨48786769917526915289902949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32524513278351276859935299 48786769917526915289902949)
            ·
              refine ⟨9147519359536296616856803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48786769917526915289902949 9147519359536296616856803)
              ·
                refine ⟨13721279039304444925285205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9147519359536296616856803 13721279039304444925285205)
                ·
                  refine ⟨80398119370924481984093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13721279039304444925285205 80398119370924481984093)
                  ·
                    rfl

theorem cell23_1409173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 9].length) (baseStart_1409173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409173 prefixEnd_1409173 := by exact prefixLift 1409173
  have htrace : WordTrace (prefixWord ++ tailWord_1409173) baseStart_1409173 baseEnd_1409173 := by
    simpa [prefixWord, tailWord_1409173, baseEnd_1409173] using wordTrace_append hprefix tailTrace_1409173
  have hstable : (prefixWord ++ tailWord_1409173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409173).length < 2 ^ (prefixWord ++ tailWord_1409173).sum := by decide
  have hdescent : baseEnd_1409173 < baseStart_1409173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409203 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 3, 7]
def baseStart_1409203 : Nat := 118140960795 + 1409203 * 2 ^ 59
def prefixEnd_1409203 : Nat := 4983230072969 + 3 ^ 40 * 1409203 * 2
def baseEnd_1409203 : Nat := 241199492919318406827233

theorem tailTrace_1409203 : CollatzResearch.WordTrace tailWord_1409203 prefixEnd_1409203 241199492919318406827233 := by
  unfold tailWord_1409203
  simp only [CollatzResearch.WordTrace]
  refine ⟨51397855913705678556576263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34265237275803785704384175 51397855913705678556576263)
  ·
    refine ⟨77096783870558517834864395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51397855913705678556576263 77096783870558517834864395)
    ·
      refine ⟨115645175805837776752296593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77096783870558517834864395 115645175805837776752296593)
      ·
        refine ⟨86733881854378332564222445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115645175805837776752296593 86733881854378332564222445)
        ·
          refine ⟨32525205695391874711583417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86733881854378332564222445 32525205695391874711583417)
          ·
            refine ⟨24393904271543906033687563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32525205695391874711583417 24393904271543906033687563)
            ·
              refine ⟨36590856407315859050531345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24393904271543906033687563 36590856407315859050531345)
              ·
                refine ⟨27443142305486894287898509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36590856407315859050531345 27443142305486894287898509)
                ·
                  refine ⟨10291178364557585357961941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27443142305486894287898509 10291178364557585357961941)
                  ·
                    refine ⟨241199492919318406827233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10291178364557585357961941 241199492919318406827233)
                    ·
                      rfl

theorem cell23_1409203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 7].length) (baseStart_1409203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409203 prefixEnd_1409203 := by exact prefixLift 1409203
  have htrace : WordTrace (prefixWord ++ tailWord_1409203) baseStart_1409203 baseEnd_1409203 := by
    simpa [prefixWord, tailWord_1409203, baseEnd_1409203] using wordTrace_append hprefix tailTrace_1409203
  have hstable : (prefixWord ++ tailWord_1409203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409203).length < 2 ^ (prefixWord ++ tailWord_1409203).sum := by decide
  have hdescent : baseEnd_1409203 < baseStart_1409203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409207 : List Nat := [1, 1, 3, 1, 4, 3, 1, 4, 5]
def baseStart_1409207 : Nat := 118140960795 + 1409207 * 2 ^ 59
def prefixEnd_1409207 : Nat := 4983230072969 + 3 ^ 40 * 1409207 * 2
def baseEnd_1409207 : Nat := 80400059186730356092409

theorem tailTrace_1409207 : CollatzResearch.WordTrace tailWord_1409207 prefixEnd_1409207 80400059186730356092409 := by
  unfold tailWord_1409207
  simp only [CollatzResearch.WordTrace]
  refine ⟨51398001805691187239721875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34265334537127458159814583 51398001805691187239721875)
  ·
    refine ⟨77097002708536780859582813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51398001805691187239721875 77097002708536780859582813)
    ·
      refine ⟨28911376015701292822343555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77097002708536780859582813 28911376015701292822343555)
      ·
        refine ⟨43367064023551939233515333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28911376015701292822343555 43367064023551939233515333)
        ·
          refine ⟨8131324504415988606284125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43367064023551939233515333 8131324504415988606284125)
          ·
            refine ⟨3049246689155995727356547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8131324504415988606284125 3049246689155995727356547)
            ·
              refine ⟨4573870033733993591034821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3049246689155995727356547 4573870033733993591034821)
              ·
                refine ⟨857600631325123798319029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4573870033733993591034821 857600631325123798319029)
                ·
                  refine ⟨80400059186730356092409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 857600631325123798319029 80400059186730356092409)
                  ·
                    rfl

theorem cell23_1409207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 5].length) (baseStart_1409207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409207 prefixEnd_1409207 := by exact prefixLift 1409207
  have htrace : WordTrace (prefixWord ++ tailWord_1409207) baseStart_1409207 baseEnd_1409207 := by
    simpa [prefixWord, tailWord_1409207, baseEnd_1409207] using wordTrace_append hprefix tailTrace_1409207
  have hstable : (prefixWord ++ tailWord_1409207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409207).length < 2 ^ (prefixWord ++ tailWord_1409207).sum := by decide
  have hdescent : baseEnd_1409207 < baseStart_1409207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409218 : List Nat := [3, 5, 1, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_1409218 : Nat := 118140960795 + 1409218 * 2 ^ 59
def prefixEnd_1409218 : Nat := 4983230072969 + 3 ^ 40 * 1409218 * 2
def baseEnd_1409218 : Nat := 723606180967772661794131

theorem tailTrace_1409218 : CollatzResearch.WordTrace tailWord_1409218 prefixEnd_1409218 723606180967772661794131 := by
  unfold tailWord_1409218
  simp only [CollatzResearch.WordTrace]
  refine ⟨12849600752162834029593077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34265602005767557412248205 12849600752162834029593077)
  ·
    refine ⟨1204650070515265690274351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12849600752162834029593077 1204650070515265690274351)
    ·
      refine ⟨1806975105772898535411527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1204650070515265690274351 1806975105772898535411527)
      ·
        refine ⟨2710462658659347803117291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1806975105772898535411527 2710462658659347803117291)
        ·
          refine ⟨4065693987989021704675937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2710462658659347803117291 4065693987989021704675937)
          ·
            refine ⟨3049270490991766278506953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4065693987989021704675937 3049270490991766278506953)
            ·
              refine ⟨2286952868243824708880215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3049270490991766278506953 2286952868243824708880215)
              ·
                refine ⟨3430429302365737063320323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2286952868243824708880215 3430429302365737063320323)
                ·
                  refine ⟨5145643953548605594980485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3430429302365737063320323 5145643953548605594980485)
                  ·
                    refine ⟨964808241290363549058841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5145643953548605594980485 964808241290363549058841)
                    ·
                      refine ⟨723606180967772661794131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 964808241290363549058841 723606180967772661794131)
                      ·
                        rfl

theorem cell23_1409218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_1409218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409218 prefixEnd_1409218 := by exact prefixLift 1409218
  have htrace : WordTrace (prefixWord ++ tailWord_1409218) baseStart_1409218 baseEnd_1409218 := by
    simpa [prefixWord, tailWord_1409218, baseEnd_1409218] using wordTrace_append hprefix tailTrace_1409218
  have hstable : (prefixWord ++ tailWord_1409218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409218).length < 2 ^ (prefixWord ++ tailWord_1409218).sum := by decide
  have hdescent : baseEnd_1409218 < baseStart_1409218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409237 : List Nat := [1, 3, 2, 4, 2, 1, 1, 1, 1, 7]
def baseStart_1409237 : Nat := 118140960795 + 1409237 * 2 ^ 59
def prefixEnd_1409237 : Nat := 4983230072969 + 3 ^ 40 * 1409237 * 2
def baseEnd_1409237 : Nat := 241205312366736029152181

theorem tailTrace_1409237 : CollatzResearch.WordTrace tailWord_1409237 prefixEnd_1409237 241205312366736029152181 := by
  unfold tailWord_1409237
  simp only [CollatzResearch.WordTrace]
  refine ⟨51399095995582502363313965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34266063997055001575542643 51399095995582502363313965)
  ·
    refine ⟨19274660998343438386242737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51399095995582502363313965 19274660998343438386242737)
    ·
      refine ⟨14455995748757578789682053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19274660998343438386242737 14455995748757578789682053)
      ·
        refine ⟨2710499202892046023065385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14455995748757578789682053 2710499202892046023065385)
        ·
          refine ⟨2032874402169034517299039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2710499202892046023065385 2032874402169034517299039)
          ·
            refine ⟨3049311603253551775948559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2032874402169034517299039 3049311603253551775948559)
            ·
              refine ⟨4573967404880327663922839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3049311603253551775948559 4573967404880327663922839)
              ·
                refine ⟨6860951107320491495884259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4573967404880327663922839 6860951107320491495884259)
                ·
                  refine ⟨10291426660980737243826389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6860951107320491495884259 10291426660980737243826389)
                  ·
                    refine ⟨241205312366736029152181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10291426660980737243826389 241205312366736029152181)
                    ·
                      rfl

theorem cell23_1409237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_1409237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409237 prefixEnd_1409237 := by exact prefixLift 1409237
  have htrace : WordTrace (prefixWord ++ tailWord_1409237) baseStart_1409237 baseEnd_1409237 := by
    simpa [prefixWord, tailWord_1409237, baseEnd_1409237] using wordTrace_append hprefix tailTrace_1409237
  have hstable : (prefixWord ++ tailWord_1409237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409237).length < 2 ^ (prefixWord ++ tailWord_1409237).sum := by decide
  have hdescent : baseEnd_1409237 < baseStart_1409237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409267 : List Nat := [1, 1, 1, 2, 2, 4, 4, 1, 3, 4]
def baseStart_1409267 : Nat := 118140960795 + 1409267 * 2 ^ 59
def prefixEnd_1409267 : Nat := 4983230072969 + 3 ^ 40 * 1409267 * 2
def baseEnd_1409267 : Nat := 241210447173280990027135

theorem tailTrace_1409267 : CollatzResearch.WordTrace tailWord_1409267 prefixEnd_1409267 241210447173280990027135 := by
  unfold tailWord_1409267
  simp only [CollatzResearch.WordTrace]
  refine ⟨51400190185473817486906055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34266793456982544991270703 51400190185473817486906055)
  ·
    refine ⟨77100285278210726230359083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51400190185473817486906055 77100285278210726230359083)
    ·
      refine ⟨115650427917316089345538625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77100285278210726230359083 115650427917316089345538625)
      ·
        refine ⟨86737820937987067009153969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115650427917316089345538625 86737820937987067009153969)
        ·
          refine ⟨65053365703490300256865477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86737820937987067009153969 65053365703490300256865477)
          ·
            refine ⟨12197506069404431298162277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65053365703490300256865477 12197506069404431298162277)
            ·
              refine ⟨2287032388013330868405427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12197506069404431298162277 2287032388013330868405427)
              ·
                refine ⟨3430548582019996302608141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2287032388013330868405427 3430548582019996302608141)
                ·
                  refine ⟨1286455718257498613478053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3430548582019996302608141 1286455718257498613478053)
                  ·
                    refine ⟨241210447173280990027135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1286455718257498613478053 241210447173280990027135)
                    ·
                      rfl

theorem cell23_1409267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 4].length) (baseStart_1409267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409267 prefixEnd_1409267 := by exact prefixLift 1409267
  have htrace : WordTrace (prefixWord ++ tailWord_1409267) baseStart_1409267 baseEnd_1409267 := by
    simpa [prefixWord, tailWord_1409267, baseEnd_1409267] using wordTrace_append hprefix tailTrace_1409267
  have hstable : (prefixWord ++ tailWord_1409267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409267).length < 2 ^ (prefixWord ++ tailWord_1409267).sum := by decide
  have hdescent : baseEnd_1409267 < baseStart_1409267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409280 : List Nat := [2, 1, 1, 2, 1, 1, 4, 5, 6]
def baseStart_1409280 : Nat := 118140960795 + 1409280 * 2 ^ 59
def prefixEnd_1409280 : Nat := 4983230072969 + 3 ^ 40 * 1409280 * 2
def baseEnd_1409280 : Nat := 80404224085372379913205

theorem tailTrace_1409280 : CollatzResearch.WordTrace tailWord_1409280 prefixEnd_1409280 80404224085372379913205 := by
  unfold tailWord_1409280
  simp only [CollatzResearch.WordTrace]
  refine ⟨25700332167213360353564647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34267109556284480471419529 25700332167213360353564647)
  ·
    refine ⟨38550498250820040530346971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25700332167213360353564647 38550498250820040530346971)
    ·
      refine ⟨57825747376230060795520457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38550498250820040530346971 57825747376230060795520457)
      ·
        refine ⟨43369310532172545596640343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57825747376230060795520457 43369310532172545596640343)
        ·
          refine ⟨65053965798258818394960515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43369310532172545596640343 65053965798258818394960515)
          ·
            refine ⟨97580948697388227592440773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65053965798258818394960515 97580948697388227592440773)
            ·
              refine ⟨18296427880760292673582645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97580948697388227592440773 18296427880760292673582645)
              ·
                refine ⟨1715290113821277438148373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18296427880760292673582645 1715290113821277438148373)
                ·
                  refine ⟨80404224085372379913205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1715290113821277438148373 80404224085372379913205)
                  ·
                    rfl

theorem cell23_1409280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 6].length) (baseStart_1409280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409280 prefixEnd_1409280 := by exact prefixLift 1409280
  have htrace : WordTrace (prefixWord ++ tailWord_1409280) baseStart_1409280 baseEnd_1409280 := by
    simpa [prefixWord, tailWord_1409280, baseEnd_1409280] using wordTrace_append hprefix tailTrace_1409280
  have hstable : (prefixWord ++ tailWord_1409280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409280).length < 2 ^ (prefixWord ++ tailWord_1409280).sum := by decide
  have hdescent : baseEnd_1409280 < baseStart_1409280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409307 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 5, 1, 3]
def baseStart_1409307 : Nat := 118140960795 + 1409307 * 2 ^ 59
def prefixEnd_1409307 : Nat := 4983230072969 + 3 ^ 40 * 1409307 * 2
def baseEnd_1409307 : Nat := 723651880746022813581221

theorem tailTrace_1409307 : CollatzResearch.WordTrace tailWord_1409307 prefixEnd_1409307 723651880746022813581221 := by
  unfold tailWord_1409307
  simp only [CollatzResearch.WordTrace]
  refine ⟨51401649105328904318362175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34267766070219269545574783 51401649105328904318362175)
  ·
    refine ⟨77102473657993356477543263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51401649105328904318362175 77102473657993356477543263)
    ·
      refine ⟨115653710486990034716314895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77102473657993356477543263 115653710486990034716314895)
      ·
        refine ⟨173480565730485052074472343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115653710486990034716314895 173480565730485052074472343)
        ·
          refine ⟨260220848595727578111708515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173480565730485052074472343 260220848595727578111708515)
          ·
            refine ⟨390331272893591367167562773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260220848595727578111708515 390331272893591367167562773)
            ·
              refine ⟨18296778416887095335979505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 390331272893591367167562773 18296778416887095335979505)
              ·
                refine ⟨13722583812665321501984629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18296778416887095335979505 13722583812665321501984629)
                ·
                  refine ⟨1286492232437373890811059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13722583812665321501984629 1286492232437373890811059)
                  ·
                    refine ⟨1929738348656060836216589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1286492232437373890811059 1929738348656060836216589)
                    ·
                      refine ⟨723651880746022813581221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1929738348656060836216589 723651880746022813581221)
                      ·
                        rfl

theorem cell23_1409307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 1, 3].length) (baseStart_1409307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409307 prefixEnd_1409307 := by exact prefixLift 1409307
  have htrace : WordTrace (prefixWord ++ tailWord_1409307) baseStart_1409307 baseEnd_1409307 := by
    simpa [prefixWord, tailWord_1409307, baseEnd_1409307] using wordTrace_append hprefix tailTrace_1409307
  have hstable : (prefixWord ++ tailWord_1409307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409307).length < 2 ^ (prefixWord ++ tailWord_1409307).sum := by decide
  have hdescent : baseEnd_1409307 < baseStart_1409307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409324 : List Nat := [2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 3]
def baseStart_1409324 : Nat := 118140960795 + 1409324 * 2 ^ 59
def prefixEnd_1409324 : Nat := 4983230072969 + 3 ^ 40 * 1409324 * 2
def baseEnd_1409324 : Nat := 723660609917149247068643

theorem tailTrace_1409324 : CollatzResearch.WordTrace tailWord_1409324 prefixEnd_1409324 723660609917149247068643 := by
  unfold tailWord_1409324
  simp only [CollatzResearch.WordTrace]
  refine ⟨25701134573133658110865513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34268179430844877481154017 25701134573133658110865513)
  ·
    refine ⟨19275850929850243583149135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25701134573133658110865513 19275850929850243583149135)
    ·
      refine ⟨28913776394775365374723703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19275850929850243583149135 28913776394775365374723703)
      ·
        refine ⟨43370664592163048062085555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28913776394775365374723703 43370664592163048062085555)
        ·
          refine ⟨65055996888244572093128333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43370664592163048062085555 65055996888244572093128333)
          ·
            refine ⟨24395998833091714534923125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65055996888244572093128333 24395998833091714534923125)
            ·
              refine ⟨2287124890602348237649043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24395998833091714534923125 2287124890602348237649043)
              ·
                refine ⟨3430687335903522356473565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2287124890602348237649043 3430687335903522356473565)
                ·
                  refine ⟨1286507750963820883677587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3430687335903522356473565 1286507750963820883677587)
                  ·
                    refine ⟨1929761626445731325516381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1286507750963820883677587 1929761626445731325516381)
                    ·
                      refine ⟨723660609917149247068643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1929761626445731325516381 723660609917149247068643)
                      ·
                        rfl

theorem cell23_1409324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 3].length) (baseStart_1409324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409324 prefixEnd_1409324 := by exact prefixLift 1409324
  have htrace : WordTrace (prefixWord ++ tailWord_1409324) baseStart_1409324 baseEnd_1409324 := by
    simpa [prefixWord, tailWord_1409324, baseEnd_1409324] using wordTrace_append hprefix tailTrace_1409324
  have hstable : (prefixWord ++ tailWord_1409324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409324).length < 2 ^ (prefixWord ++ tailWord_1409324).sum := by decide
  have hdescent : baseEnd_1409324 < baseStart_1409324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409347 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 2, 6, 2]
def baseStart_1409347 : Nat := 118140960795 + 1409347 * 2 ^ 59
def prefixEnd_1409347 : Nat := 4983230072969 + 3 ^ 40 * 1409347 * 2
def baseEnd_1409347 : Nat := 723672419972202657081037

theorem tailTrace_1409347 : CollatzResearch.WordTrace tailWord_1409347 prefixEnd_1409347 723672419972202657081037 := by
  unfold tailWord_1409347
  simp only [CollatzResearch.WordTrace]
  refine ⟨51403108025183991149818295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34268738683455994099878863 51403108025183991149818295)
  ·
    refine ⟨77104662037775986724727443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51403108025183991149818295 77104662037775986724727443)
    ·
      refine ⟨115656993056663980087091165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77104662037775986724727443 115656993056663980087091165)
      ·
        refine ⟨43371372396248992532659187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115656993056663980087091165 43371372396248992532659187)
        ·
          refine ⟨65057058594373488798988781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43371372396248992532659187 65057058594373488798988781)
          ·
            refine ⟨24396396972890058299620793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65057058594373488798988781 24396396972890058299620793)
            ·
              refine ⟨18297297729667543724715595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24396396972890058299620793 18297297729667543724715595)
              ·
                refine ⟨27445946594501315587073393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18297297729667543724715595 27445946594501315587073393)
                ·
                  refine ⟨20584459945875986690305045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27445946594501315587073393 20584459945875986690305045)
                  ·
                    refine ⟨964896559962936876108049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20584459945875986690305045 964896559962936876108049)
                    ·
                      refine ⟨723672419972202657081037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 964896559962936876108049 723672419972202657081037)
                      ·
                        rfl

theorem cell23_1409347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 6, 2].length) (baseStart_1409347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409347 prefixEnd_1409347 := by exact prefixLift 1409347
  have htrace : WordTrace (prefixWord ++ tailWord_1409347) baseStart_1409347 baseEnd_1409347 := by
    simpa [prefixWord, tailWord_1409347, baseEnd_1409347] using wordTrace_append hprefix tailTrace_1409347
  have hstable : (prefixWord ++ tailWord_1409347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409347).length < 2 ^ (prefixWord ++ tailWord_1409347).sum := by decide
  have hdescent : baseEnd_1409347 < baseStart_1409347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409384 : List Nat := [2, 1, 4, 2, 2, 1, 1, 2, 3, 2, 3]
def baseStart_1409384 : Nat := 118140960795 + 1409384 * 2 ^ 59
def prefixEnd_1409384 : Nat := 4983230072969 + 3 ^ 40 * 1409384 * 2
def baseEnd_1409384 : Nat := 723691418756419012318367

theorem tailTrace_1409384 : CollatzResearch.WordTrace tailWord_1409384 prefixEnd_1409384 723691418756419012318367 := by
  unfold tailWord_1409384
  simp only [CollatzResearch.WordTrace]
  refine ⟨25702228763024973234457603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34269638350699964312610137 25702228763024973234457603)
  ·
    refine ⟨38553343144537459851686405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25702228763024973234457603 38553343144537459851686405)
    ·
      refine ⟨7228751839600773722191201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38553343144537459851686405 7228751839600773722191201)
      ·
        refine ⟨5421563879700580291643401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7228751839600773722191201 5421563879700580291643401)
        ·
          refine ⟨4066172909775435218732551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5421563879700580291643401 4066172909775435218732551)
          ·
            refine ⟨6099259364663152828098827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4066172909775435218732551 6099259364663152828098827)
            ·
              refine ⟨9148889046994729242148241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6099259364663152828098827 9148889046994729242148241)
              ·
                refine ⟨6861666785246046931611181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9148889046994729242148241 6861666785246046931611181)
                ·
                  refine ⟨2573125044467267599354193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6861666785246046931611181 2573125044467267599354193)
                  ·
                    refine ⟨1929843783350450699515645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2573125044467267599354193 1929843783350450699515645)
                    ·
                      refine ⟨723691418756419012318367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1929843783350450699515645 723691418756419012318367)
                      ·
                        rfl

theorem cell23_1409384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_1409384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409384 prefixEnd_1409384 := by exact prefixLift 1409384
  have htrace : WordTrace (prefixWord ++ tailWord_1409384) baseStart_1409384 baseEnd_1409384 := by
    simpa [prefixWord, tailWord_1409384, baseEnd_1409384] using wordTrace_append hprefix tailTrace_1409384
  have hstable : (prefixWord ++ tailWord_1409384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409384).length < 2 ^ (prefixWord ++ tailWord_1409384).sum := by decide
  have hdescent : baseEnd_1409384 < baseStart_1409384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409394 : List Nat := [3, 2, 1, 2, 1, 4, 2, 1, 1, 2, 4]
def baseStart_1409394 : Nat := 118140960795 + 1409394 * 2 ^ 59
def prefixEnd_1409394 : Nat := 4983230072969 + 3 ^ 40 * 1409394 * 2
def baseEnd_1409394 : Nat := 723696553562963973193321

theorem tailTrace_1409394 : CollatzResearch.WordTrace tailWord_1409394 prefixEnd_1409394 723696553562963973193321 := by
  unfold tailWord_1409394
  simp only [CollatzResearch.WordTrace]
  refine ⟨12851205564003429544194809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34269881504009145451186157 12851205564003429544194809)
  ·
    refine ⟨9638404173002572158146107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12851205564003429544194809 9638404173002572158146107)
    ·
      refine ⟨14457606259503858237219161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9638404173002572158146107 14457606259503858237219161)
      ·
        refine ⟨10843204694627893677914371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14457606259503858237219161 10843204694627893677914371)
        ·
          refine ⟨16264807041941840516871557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10843204694627893677914371 16264807041941840516871557)
          ·
            refine ⟨3049651320364095096913417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16264807041941840516871557 3049651320364095096913417)
            ·
              refine ⟨2287238490273071322685063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3049651320364095096913417 2287238490273071322685063)
              ·
                refine ⟨3430857735409606984027595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2287238490273071322685063 3430857735409606984027595)
                ·
                  refine ⟨5146286603114410476041393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3430857735409606984027595 5146286603114410476041393)
                  ·
                    refine ⟨3859714952335807857031045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5146286603114410476041393 3859714952335807857031045)
                    ·
                      refine ⟨723696553562963973193321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3859714952335807857031045 723696553562963973193321)
                      ·
                        rfl

theorem cell23_1409394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_1409394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409394 prefixEnd_1409394 := by exact prefixLift 1409394
  have htrace : WordTrace (prefixWord ++ tailWord_1409394) baseStart_1409394 baseEnd_1409394 := by
    simpa [prefixWord, tailWord_1409394, baseEnd_1409394] using wordTrace_append hprefix tailTrace_1409394
  have hstable : (prefixWord ++ tailWord_1409394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409394).length < 2 ^ (prefixWord ++ tailWord_1409394).sum := by decide
  have hdescent : baseEnd_1409394 < baseStart_1409394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409418 : List Nat := [3, 1, 2, 5, 1, 1, 1, 3, 1, 2, 3]
def baseStart_1409418 : Nat := 118140960795 + 1409418 * 2 ^ 59
def prefixEnd_1409418 : Nat := 4983230072969 + 3 ^ 40 * 1409418 * 2
def baseEnd_1409418 : Nat := 723708877098671879293211

theorem tailTrace_1409418 : CollatzResearch.WordTrace tailWord_1409418 prefixEnd_1409418 723708877098671879293211 := by
  unfold tailWord_1409418
  simp only [CollatzResearch.WordTrace]
  refine ⟨12851424401981692568913227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34270465071951180183768605 12851424401981692568913227)
  ·
    refine ⟨19277136602972538853369841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12851424401981692568913227 19277136602972538853369841)
    ·
      refine ⟨14457852452229404140027381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19277136602972538853369841 14457852452229404140027381)
      ·
        refine ⟨1355423667396506638127567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14457852452229404140027381 1355423667396506638127567)
        ·
          refine ⟨2033135501094759957191351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1355423667396506638127567 2033135501094759957191351)
          ·
            refine ⟨3049703251642139935787027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2033135501094759957191351 3049703251642139935787027)
            ·
              refine ⟨4574554877463209903680541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3049703251642139935787027 4574554877463209903680541)
              ·
                refine ⟨1715458079048703713880203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4574554877463209903680541 1715458079048703713880203)
                ·
                  refine ⟨2573187118573055570820305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1715458079048703713880203 2573187118573055570820305)
                  ·
                    refine ⟨1929890338929791678115229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2573187118573055570820305 1929890338929791678115229)
                    ·
                      refine ⟨723708877098671879293211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1929890338929791678115229 723708877098671879293211)
                      ·
                        rfl

theorem cell23_1409418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_1409418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409418 prefixEnd_1409418 := by exact prefixLift 1409418
  have htrace : WordTrace (prefixWord ++ tailWord_1409418) baseStart_1409418 baseEnd_1409418 := by
    simpa [prefixWord, tailWord_1409418, baseEnd_1409418] using wordTrace_append hprefix tailTrace_1409418
  have hstable : (prefixWord ++ tailWord_1409418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409418).length < 2 ^ (prefixWord ++ tailWord_1409418).sum := by decide
  have hdescent : baseEnd_1409418 < baseStart_1409418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409431 : List Nat := [1, 1, 3, 3, 1, 1, 5, 2, 2, 1, 3]
def baseStart_1409431 : Nat := 118140960795 + 1409431 * 2 ^ 59
def prefixEnd_1409431 : Nat := 4983230072969 + 3 ^ 40 * 1409431 * 2
def baseEnd_1409431 : Nat := 723715552347180328430651

theorem tailTrace_1409431 : CollatzResearch.WordTrace tailWord_1409431 prefixEnd_1409431 723715552347180328430651 := by
  unfold tailWord_1409431
  simp only [CollatzResearch.WordTrace]
  refine ⟨51406171756879673495876147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34270781171253115663917431 51406171756879673495876147)
  ·
    refine ⟨77109257635319510243814221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51406171756879673495876147 77109257635319510243814221)
    ·
      refine ⟨28915971613244816341430333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77109257635319510243814221 28915971613244816341430333)
      ·
        refine ⟨10843489354966806128036375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28915971613244816341430333 10843489354966806128036375)
        ·
          refine ⟨16265234032450209192054563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10843489354966806128036375 16265234032450209192054563)
          ·
            refine ⟨24397851048675313788081845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16265234032450209192054563 24397851048675313788081845)
            ·
              refine ⟨2287298535813310667632673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24397851048675313788081845 2287298535813310667632673)
              ·
                refine ⟨1715473901859983000724505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2287298535813310667632673 1715473901859983000724505)
                ·
                  refine ⟨1286605426394987250543379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1715473901859983000724505 1286605426394987250543379)
                  ·
                    refine ⟨1929908139592480875815069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1286605426394987250543379 1929908139592480875815069)
                    ·
                      refine ⟨723715552347180328430651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1929908139592480875815069 723715552347180328430651)
                      ·
                        rfl

theorem cell23_1409431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_1409431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409431 prefixEnd_1409431 := by exact prefixLift 1409431
  have htrace : WordTrace (prefixWord ++ tailWord_1409431) baseStart_1409431 baseEnd_1409431 := by
    simpa [prefixWord, tailWord_1409431, baseEnd_1409431] using wordTrace_append hprefix tailTrace_1409431
  have hstable : (prefixWord ++ tailWord_1409431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409431).length < 2 ^ (prefixWord ++ tailWord_1409431).sum := by decide
  have hdescent : baseEnd_1409431 < baseStart_1409431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409448 : List Nat := [2, 1, 6, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_1409448 : Nat := 118140960795 + 1409448 * 2 ^ 59
def prefixEnd_1409448 : Nat := 4983230072969 + 3 ^ 40 * 1409448 * 2
def baseEnd_1409448 : Nat := 723724281518306761918073

theorem tailTrace_1409448 : CollatzResearch.WordTrace tailWord_1409448 prefixEnd_1409448 723724281518306761918073 := by
  unfold tailWord_1409448
  simp only [CollatzResearch.WordTrace]
  refine ⟨25703395898909042699622499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34271194531878723599496665 25703395898909042699622499)
  ·
    refine ⟨38555093848363564049433749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25703395898909042699622499 38555093848363564049433749)
    ·
      refine ⟨1807270024142042064817207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38555093848363564049433749 1807270024142042064817207)
      ·
        refine ⟨2710905036213063097225811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1807270024142042064817207 2710905036213063097225811)
        ·
          refine ⟨4066357554319594645838717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2710905036213063097225811 4066357554319594645838717)
          ·
            refine ⟨1524884082869847992189519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4066357554319594645838717 1524884082869847992189519)
            ·
              refine ⟨2287326124304771988284279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1524884082869847992189519 2287326124304771988284279)
              ·
                refine ⟨3430989186457157982426419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2287326124304771988284279 3430989186457157982426419)
                ·
                  refine ⟨5146483779685736973639629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3430989186457157982426419 5146483779685736973639629)
                  ·
                    refine ⟨1929931417382151365114861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5146483779685736973639629 1929931417382151365114861)
                    ·
                      refine ⟨723724281518306761918073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1929931417382151365114861 723724281518306761918073)
                      ·
                        rfl

theorem cell23_1409448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_1409448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409448 prefixEnd_1409448 := by exact prefixLift 1409448
  have htrace : WordTrace (prefixWord ++ tailWord_1409448) baseStart_1409448 baseEnd_1409448 := by
    simpa [prefixWord, tailWord_1409448, baseEnd_1409448] using wordTrace_append hprefix tailTrace_1409448
  have hstable : (prefixWord ++ tailWord_1409448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409448).length < 2 ^ (prefixWord ++ tailWord_1409448).sum := by decide
  have hdescent : baseEnd_1409448 < baseStart_1409448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409527 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 4]
def baseStart_1409527 : Nat := 118140960795 + 1409527 * 2 ^ 59
def prefixEnd_1409527 : Nat := 4983230072969 + 3 ^ 40 * 1409527 * 2
def baseEnd_1409527 : Nat := 723764846490011952830209

theorem tailTrace_1409527 : CollatzResearch.WordTrace tailWord_1409527 prefixEnd_1409527 723764846490011952830209 := by
  unfold tailWord_1409527
  simp only [CollatzResearch.WordTrace]
  refine ⟨51409673164531881891370835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34273115443021254594247223 51409673164531881891370835)
  ·
    refine ⟨77114509746797822837056253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51409673164531881891370835 77114509746797822837056253)
    ·
      refine ⟨28917941155049183563896095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77114509746797822837056253 28917941155049183563896095)
      ·
        refine ⟨43376911732573775345844143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28917941155049183563896095 43376911732573775345844143)
        ·
          refine ⟨65065367598860663018766215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43376911732573775345844143 65065367598860663018766215)
          ·
            refine ⟨97598051398290994528149323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65065367598860663018766215 97598051398290994528149323)
            ·
              refine ⟨146397077097436491792223985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97598051398290994528149323 146397077097436491792223985)
              ·
                refine ⟨109797807823077368844167989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146397077097436491792223985 109797807823077368844167989)
                ·
                  refine ⟨10293544483413503329140749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109797807823077368844167989 10293544483413503329140749)
                  ·
                    refine ⟨3860079181280063748427781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10293544483413503329140749 3860079181280063748427781)
                    ·
                      refine ⟨723764846490011952830209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3860079181280063748427781 723764846490011952830209)
                      ·
                        rfl

theorem cell23_1409527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_1409527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409527 prefixEnd_1409527 := by exact prefixLift 1409527
  have htrace : WordTrace (prefixWord ++ tailWord_1409527) baseStart_1409527 baseEnd_1409527 := by
    simpa [prefixWord, tailWord_1409527, baseEnd_1409527] using wordTrace_append hprefix tailTrace_1409527
  have hstable : (prefixWord ++ tailWord_1409527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409527).length < 2 ^ (prefixWord ++ tailWord_1409527).sum := by decide
  have hdescent : baseEnd_1409527 < baseStart_1409527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409567 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 10]
def baseStart_1409567 : Nat := 118140960795 + 1409567 * 2 ^ 59
def prefixEnd_1409567 : Nat := 4983230072969 + 3 ^ 40 * 1409567 * 2
def baseEnd_1409567 : Nat := 80420598412910199592225

theorem tailTrace_1409567 : CollatzResearch.WordTrace tailWord_1409567 prefixEnd_1409567 80420598412910199592225 := by
  unfold tailWord_1409567
  simp only [CollatzResearch.WordTrace]
  refine ⟨51411132084386968722826955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34274088056257979148551303 51411132084386968722826955)
  ·
    refine ⟨77116698126580453084240433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51411132084386968722826955 77116698126580453084240433)
    ·
      refine ⟨57837523594935339813180325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77116698126580453084240433 57837523594935339813180325)
      ·
        refine ⟨10844535674050376214971311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57837523594935339813180325 10844535674050376214971311)
        ·
          refine ⟨16266803511075564322456967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10844535674050376214971311 16266803511075564322456967)
          ·
            refine ⟨24400205266613346483685451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16266803511075564322456967 24400205266613346483685451)
            ·
              refine ⟨36600307899920019725528177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24400205266613346483685451 36600307899920019725528177)
              ·
                refine ⟨27450230924940014794146133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36600307899920019725528177 27450230924940014794146133)
                ·
                  refine ⟨80420598412910199592225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 27450230924940014794146133 80420598412910199592225)
                  ·
                    rfl

theorem cell23_1409567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 10].length) (baseStart_1409567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409567 prefixEnd_1409567 := by exact prefixLift 1409567
  have htrace : WordTrace (prefixWord ++ tailWord_1409567) baseStart_1409567 baseEnd_1409567 := by
    simpa [prefixWord, tailWord_1409567, baseEnd_1409567] using wordTrace_append hprefix tailTrace_1409567
  have hstable : (prefixWord ++ tailWord_1409567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409567).length < 2 ^ (prefixWord ++ tailWord_1409567).sum := by decide
  have hdescent : baseEnd_1409567 < baseStart_1409567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409571 : List Nat := [1, 1, 1, 4, 4, 2, 1, 2, 3, 4]
def baseStart_1409571 : Nat := 118140960795 + 1409571 * 2 ^ 59
def prefixEnd_1409571 : Nat := 4983230072969 + 3 ^ 40 * 1409571 * 2
def baseEnd_1409571 : Nat := 241262479879603260226669

theorem tailTrace_1409571 : CollatzResearch.WordTrace tailWord_1409571 prefixEnd_1409571 241262479879603260226669 := by
  unfold tailWord_1409571
  simp only [CollatzResearch.WordTrace]
  refine ⟨51411277976372477405972567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34274185317581651603981711 51411277976372477405972567)
  ·
    refine ⟨77116916964558716108958851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51411277976372477405972567 77116916964558716108958851)
    ·
      refine ⟨115675375446838074163438277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77116916964558716108958851 115675375446838074163438277)
      ·
        refine ⟨21689132896282138905644677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115675375446838074163438277 21689132896282138905644677)
        ·
          refine ⟨4066712418052901044808377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21689132896282138905644677 4066712418052901044808377)
          ·
            refine ⟨3050034313539675783606283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4066712418052901044808377 3050034313539675783606283)
            ·
              refine ⟨4575051470309513675409425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3050034313539675783606283 4575051470309513675409425)
              ·
                refine ⟨3431288602732135256557069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4575051470309513675409425 3431288602732135256557069)
                ·
                  refine ⟨1286733226024550721208901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3431288602732135256557069 1286733226024550721208901)
                  ·
                    refine ⟨241262479879603260226669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1286733226024550721208901 241262479879603260226669)
                    ·
                      rfl

theorem cell23_1409571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 4].length) (baseStart_1409571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409571 prefixEnd_1409571 := by exact prefixLift 1409571
  have htrace : WordTrace (prefixWord ++ tailWord_1409571) baseStart_1409571 baseEnd_1409571 := by
    simpa [prefixWord, tailWord_1409571, baseEnd_1409571] using wordTrace_append hprefix tailTrace_1409571
  have hstable : (prefixWord ++ tailWord_1409571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409571).length < 2 ^ (prefixWord ++ tailWord_1409571).sum := by decide
  have hdescent : baseEnd_1409571 < baseStart_1409571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409575 : List Nat := [1, 1, 7, 2, 1, 2, 1, 1, 2, 5]
def baseStart_1409575 : Nat := 118140960795 + 1409575 * 2 ^ 59
def prefixEnd_1409575 : Nat := 4983230072969 + 3 ^ 40 * 1409575 * 2
def baseEnd_1409575 : Nat := 241263164520475921676663

theorem tailTrace_1409575 : CollatzResearch.WordTrace tailWord_1409575 prefixEnd_1409575 241263164520475921676663 := by
  unfold tailWord_1409575
  simp only [CollatzResearch.WordTrace]
  refine ⟨51411423868357986089118179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34274282578905324059412119 51411423868357986089118179)
  ·
    refine ⟨77117135802536979133677269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51411423868357986089118179 77117135802536979133677269)
    ·
      refine ⟨1807432870371960448445561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 77117135802536979133677269 1807432870371960448445561)
      ·
        refine ⟨1355574652778970336334171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1807432870371960448445561 1355574652778970336334171)
        ·
          refine ⟨2033361979168455504501257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1355574652778970336334171 2033361979168455504501257)
          ·
            refine ⟨1525021484376341628375943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2033361979168455504501257 1525021484376341628375943)
            ·
              refine ⟨2287532226564512442563915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1525021484376341628375943 2287532226564512442563915)
              ·
                refine ⟨3431298339846768663845873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2287532226564512442563915 3431298339846768663845873)
                ·
                  refine ⟨2573473754885076497884405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3431298339846768663845873 2573473754885076497884405)
                  ·
                    refine ⟨241263164520475921676663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2573473754885076497884405 241263164520475921676663)
                    ·
                      rfl

theorem cell23_1409575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_1409575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409575 prefixEnd_1409575 := by exact prefixLift 1409575
  have htrace : WordTrace (prefixWord ++ tailWord_1409575) baseStart_1409575 baseEnd_1409575 := by
    simpa [prefixWord, tailWord_1409575, baseEnd_1409575] using wordTrace_append hprefix tailTrace_1409575
  have hstable : (prefixWord ++ tailWord_1409575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409575).length < 2 ^ (prefixWord ++ tailWord_1409575).sum := by decide
  have hdescent : baseEnd_1409575 < baseStart_1409575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409578 : List Nat := [3, 1, 4, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_1409578 : Nat := 118140960795 + 1409578 * 2 ^ 59
def prefixEnd_1409578 : Nat := 4983230072969 + 3 ^ 40 * 1409578 * 2
def baseEnd_1409578 : Nat := 723791034003391253292475

theorem tailTrace_1409578 : CollatzResearch.WordTrace tailWord_1409578 prefixEnd_1409578 723791034003391253292475 := by
  unfold tailWord_1409578
  simp only [CollatzResearch.WordTrace]
  refine ⟨12852883321836779400369347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34274355524898078400984925 12852883321836779400369347)
  ·
    refine ⟨19279324982755169100554021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12852883321836779400369347 19279324982755169100554021)
    ·
      refine ⟨3614873434266594206353879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19279324982755169100554021 3614873434266594206353879)
      ·
        refine ⟨5422310151399891309530819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3614873434266594206353879 5422310151399891309530819)
        ·
          refine ⟨8133465227099836964296229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5422310151399891309530819 8133465227099836964296229)
          ·
            refine ⟨1525024730081219430805543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8133465227099836964296229 1525024730081219430805543)
            ·
              refine ⟨2287537095121829146208315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1525024730081219430805543 2287537095121829146208315)
              ·
                refine ⟨3431305642682743719312473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2287537095121829146208315 3431305642682743719312473)
                ·
                  refine ⟨2573479232012057789484355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3431305642682743719312473 2573479232012057789484355)
                  ·
                    refine ⟨3860218848018086684226533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2573479232012057789484355 3860218848018086684226533)
                    ·
                      refine ⟨723791034003391253292475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3860218848018086684226533 723791034003391253292475)
                      ·
                        rfl

theorem cell23_1409578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_1409578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409578 prefixEnd_1409578 := by exact prefixLift 1409578
  have htrace : WordTrace (prefixWord ++ tailWord_1409578) baseStart_1409578 baseEnd_1409578 := by
    simpa [prefixWord, tailWord_1409578, baseEnd_1409578] using wordTrace_append hprefix tailTrace_1409578
  have hstable : (prefixWord ++ tailWord_1409578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409578).length < 2 ^ (prefixWord ++ tailWord_1409578).sum := by decide
  have hdescent : baseEnd_1409578 < baseStart_1409578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409601 : List Nat := [1, 2, 5, 1, 1, 2, 3, 2, 6]
def baseStart_1409601 : Nat := 118140960795 + 1409601 * 2 ^ 59
def prefixEnd_1409601 : Nat := 4983230072969 + 3 ^ 40 * 1409601 * 2
def baseEnd_1409601 : Nat := 80422538228716073700541

theorem tailTrace_1409601 : CollatzResearch.WordTrace tailWord_1409601 prefixEnd_1409601 80422538228716073700541 := by
  unfold tailWord_1409601
  simp only [CollatzResearch.WordTrace]
  refine ⟨51412372166263792529564657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34274914777509195019709771 51412372166263792529564657)
  ·
    refine ⟨38559279124697844397173493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51412372166263792529564657 38559279124697844397173493)
    ·
      refine ⟨3614932417940422912235015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38559279124697844397173493 3614932417940422912235015)
      ·
        refine ⟨5422398626910634368352523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3614932417940422912235015 5422398626910634368352523)
        ·
          refine ⟨8133597940365951552528785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5422398626910634368352523 8133597940365951552528785)
          ·
            refine ⟨6100198455274463664396589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8133597940365951552528785 6100198455274463664396589)
            ·
              refine ⟨2287574420727923874148721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6100198455274463664396589 2287574420727923874148721)
              ·
                refine ⟨1715680815545942905611541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2287574420727923874148721 1715680815545942905611541)
                ·
                  refine ⟨80422538228716073700541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1715680815545942905611541 80422538228716073700541)
                  ·
                    rfl

theorem cell23_1409601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 6].length) (baseStart_1409601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409601 prefixEnd_1409601 := by exact prefixLift 1409601
  have htrace : WordTrace (prefixWord ++ tailWord_1409601) baseStart_1409601 baseEnd_1409601 := by
    simpa [prefixWord, tailWord_1409601, baseEnd_1409601] using wordTrace_append hprefix tailTrace_1409601
  have hstable : (prefixWord ++ tailWord_1409601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409601).length < 2 ^ (prefixWord ++ tailWord_1409601).sum := by decide
  have hdescent : baseEnd_1409601 < baseStart_1409601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409611 : List Nat := [1, 1, 1, 1, 3, 1, 5, 3, 3, 1, 3]
def baseStart_1409611 : Nat := 118140960795 + 1409611 * 2 ^ 59
def prefixEnd_1409611 : Nat := 4983230072969 + 3 ^ 40 * 1409611 * 2
def baseEnd_1409611 : Nat := 723807978864989624179823

theorem tailTrace_1409611 : CollatzResearch.WordTrace tailWord_1409611 prefixEnd_1409611 723807978864989624179823 := by
  unfold tailWord_1409611
  simp only [CollatzResearch.WordTrace]
  refine ⟨51412736896227564237428687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34275157930818376158285791 51412736896227564237428687)
  ·
    refine ⟨77119105344341346356143031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51412736896227564237428687 77119105344341346356143031)
    ·
      refine ⟨115678658016512019534214547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77119105344341346356143031 115678658016512019534214547)
      ·
        refine ⟨173517987024768029301321821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115678658016512019534214547 173517987024768029301321821)
        ·
          refine ⟨65069245134288010987995683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173517987024768029301321821 65069245134288010987995683)
          ·
            refine ⟨97603867701432016481993525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65069245134288010987995683 97603867701432016481993525)
            ·
              refine ⟨9150362597009251545186893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97603867701432016481993525 9150362597009251545186893)
              ·
                refine ⟨3431385973878469329445085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9150362597009251545186893 3431385973878469329445085)
                ·
                  refine ⟨1286769740204425998541907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3431385973878469329445085 1286769740204425998541907)
                  ·
                    refine ⟨1930154610306638997812861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1286769740204425998541907 1930154610306638997812861)
                    ·
                      refine ⟨723807978864989624179823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1930154610306638997812861 723807978864989624179823)
                      ·
                        rfl

theorem cell23_1409611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 1, 3].length) (baseStart_1409611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409611 prefixEnd_1409611 := by exact prefixLift 1409611
  have htrace : WordTrace (prefixWord ++ tailWord_1409611) baseStart_1409611 baseEnd_1409611 := by
    simpa [prefixWord, tailWord_1409611, baseEnd_1409611] using wordTrace_append hprefix tailTrace_1409611
  have hstable : (prefixWord ++ tailWord_1409611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409611).length < 2 ^ (prefixWord ++ tailWord_1409611).sum := by decide
  have hdescent : baseEnd_1409611 < baseStart_1409611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409614 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 5, 5]
def baseStart_1409614 : Nat := 118140960795 + 1409614 * 2 ^ 59
def prefixEnd_1409614 : Nat := 4983230072969 + 3 ^ 40 * 1409614 * 2
def baseEnd_1409614 : Nat := 241269839768984370814103

theorem tailTrace_1409614 : CollatzResearch.WordTrace tailWord_1409614 prefixEnd_1409614 241269839768984370814103 := by
  unfold tailWord_1409614
  simp only [CollatzResearch.WordTrace]
  refine ⟨6426605789402086968723487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34275230876811130499858597 6426605789402086968723487)
  ·
    refine ⟨9639908684103130453085231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6426605789402086968723487 9639908684103130453085231)
    ·
      refine ⟨14459863026154695679627847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9639908684103130453085231 14459863026154695679627847)
      ·
        refine ⟨21689794539232043519441771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14459863026154695679627847 21689794539232043519441771)
        ·
          refine ⟨32534691808848065279162657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21689794539232043519441771 32534691808848065279162657)
          ·
            refine ⟨24401018856636048959371993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32534691808848065279162657 24401018856636048959371993)
            ·
              refine ⟨18300764142477036719528995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24401018856636048959371993 18300764142477036719528995)
              ·
                refine ⟨27451146213715555079293493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18300764142477036719528995 27451146213715555079293493)
                ·
                  refine ⟨2573544957535833288683765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27451146213715555079293493 2573544957535833288683765)
                  ·
                    refine ⟨241269839768984370814103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2573544957535833288683765 241269839768984370814103)
                    ·
                      rfl

theorem cell23_1409614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_1409614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409614 prefixEnd_1409614 := by exact prefixLift 1409614
  have htrace : WordTrace (prefixWord ++ tailWord_1409614) baseStart_1409614 baseEnd_1409614 := by
    simpa [prefixWord, tailWord_1409614, baseEnd_1409614] using wordTrace_append hprefix tailTrace_1409614
  have hstable : (prefixWord ++ tailWord_1409614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409614).length < 2 ^ (prefixWord ++ tailWord_1409614).sum := by decide
  have hdescent : baseEnd_1409614 < baseStart_1409614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409621 : List Nat := [1, 3, 2, 2, 1, 1, 3, 2, 1, 5, 2]
def baseStart_1409621 : Nat := 118140960795 + 1409621 * 2 ^ 59
def prefixEnd_1409621 : Nat := 4983230072969 + 3 ^ 40 * 1409621 * 2
def baseEnd_1409621 : Nat := 723813113671534585054777

theorem tailTrace_1409621 : CollatzResearch.WordTrace tailWord_1409621 prefixEnd_1409621 723813113671534585054777 := by
  unfold tailWord_1409621
  simp only [CollatzResearch.WordTrace]
  refine ⟨51413101626191335945292717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34275401084127557296861811 51413101626191335945292717)
  ·
    refine ⟨19279913109821750979484769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51413101626191335945292717 19279913109821750979484769)
    ·
      refine ⟨14459934832366313234613577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19279913109821750979484769 14459934832366313234613577)
      ·
        refine ⟨10844951124274734925960183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14459934832366313234613577 10844951124274734925960183)
        ·
          refine ⟨16267426686412102388940275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10844951124274734925960183 16267426686412102388940275)
          ·
            refine ⟨24401140029618153583410413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16267426686412102388940275 24401140029618153583410413)
            ·
              refine ⟨9150427511106807593778905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24401140029618153583410413 9150427511106807593778905)
              ·
                refine ⟨6862820633330105695334179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9150427511106807593778905 6862820633330105695334179)
                ·
                  refine ⟨10294230949995158543001269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6862820633330105695334179 10294230949995158543001269)
                  ·
                    refine ⟨965084151562046113406369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10294230949995158543001269 965084151562046113406369)
                    ·
                      refine ⟨723813113671534585054777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 965084151562046113406369 723813113671534585054777)
                      ·
                        rfl

theorem cell23_1409621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_1409621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409621 prefixEnd_1409621 := by exact prefixLift 1409621
  have htrace : WordTrace (prefixWord ++ tailWord_1409621) baseStart_1409621 baseEnd_1409621 := by
    simpa [prefixWord, tailWord_1409621, baseEnd_1409621] using wordTrace_append hprefix tailTrace_1409621
  have hstable : (prefixWord ++ tailWord_1409621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409621).length < 2 ^ (prefixWord ++ tailWord_1409621).sum := by decide
  have hdescent : baseEnd_1409621 < baseStart_1409621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409644 : List Nat := [2, 2, 1, 1, 3, 1, 2, 4, 1, 6]
def baseStart_1409644 : Nat := 118140960795 + 1409644 * 2 ^ 59
def prefixEnd_1409644 : Nat := 4983230072969 + 3 ^ 40 * 1409644 * 2
def baseEnd_1409644 : Nat := 241274974575529331689057

theorem tailTrace_1409644 : CollatzResearch.WordTrace tailWord_1409644 prefixEnd_1409644 241274974575529331689057 := by
  unfold tailWord_1409644
  simp only [CollatzResearch.WordTrace]
  refine ⟨25706970252554005436689993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34275960336738673915586657 25706970252554005436689993)
  ·
    refine ⟨19280227689415504077517495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25706970252554005436689993 19280227689415504077517495)
    ·
      refine ⟨28920341534123256116276243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19280227689415504077517495 28920341534123256116276243)
      ·
        refine ⟨43380512301184884174414365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28920341534123256116276243 43380512301184884174414365)
        ·
          refine ⟨16267692112944331565405387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43380512301184884174414365 16267692112944331565405387)
          ·
            refine ⟨24401538169416497348108081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16267692112944331565405387 24401538169416497348108081)
            ·
              refine ⟨18301153627062373011081061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24401538169416497348108081 18301153627062373011081061)
              ·
                refine ⟨3431466305074194939577699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18301153627062373011081061 3431466305074194939577699)
                ·
                  refine ⟨5147199457611292409366549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3431466305074194939577699 5147199457611292409366549)
                  ·
                    refine ⟨241274974575529331689057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5147199457611292409366549 241274974575529331689057)
                    ·
                      rfl

theorem cell23_1409644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 6].length) (baseStart_1409644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409644 prefixEnd_1409644 := by exact prefixLift 1409644
  have htrace : WordTrace (prefixWord ++ tailWord_1409644) baseStart_1409644 baseEnd_1409644 := by
    simpa [prefixWord, tailWord_1409644, baseEnd_1409644] using wordTrace_append hprefix tailTrace_1409644
  have hstable : (prefixWord ++ tailWord_1409644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409644).length < 2 ^ (prefixWord ++ tailWord_1409644).sum := by decide
  have hdescent : baseEnd_1409644 < baseStart_1409644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409664 : List Nat := [2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 6]
def baseStart_1409664 : Nat := 118140960795 + 1409664 * 2 ^ 59
def prefixEnd_1409664 : Nat := 4983230072969 + 3 ^ 40 * 1409664 * 2
def baseEnd_1409664 : Nat := 723835193339677916817079

theorem tailTrace_1409664 : CollatzResearch.WordTrace tailWord_1409664 prefixEnd_1409664 723835193339677916817079 := by
  unfold tailWord_1409664
  simp only [CollatzResearch.WordTrace]
  refine ⟨25707334982517777144554023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34276446643357036192738697 25707334982517777144554023)
  ·
    refine ⟨38561002473776665716831035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25707334982517777144554023 38561002473776665716831035)
    ·
      refine ⟨57841503710664998575246553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38561002473776665716831035 57841503710664998575246553)
      ·
        refine ⟨43381127782998748931434915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57841503710664998575246553 43381127782998748931434915)
        ·
          refine ⟨65071691674498123397152373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43381127782998748931434915 65071691674498123397152373)
          ·
            refine ⟨6100471094484199068483035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65071691674498123397152373 6100471094484199068483035)
            ·
              refine ⟨9150706641726298602724553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6100471094484199068483035 9150706641726298602724553)
              ·
                refine ⟨6863029981294723952043415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9150706641726298602724553 6863029981294723952043415)
                ·
                  refine ⟨10294544971942085928065123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6863029981294723952043415 10294544971942085928065123)
                  ·
                    refine ⟨15441817457913128892097685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10294544971942085928065123 15441817457913128892097685)
                    ·
                      refine ⟨723835193339677916817079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15441817457913128892097685 723835193339677916817079)
                      ·
                        rfl

theorem cell23_1409664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_1409664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409664 prefixEnd_1409664 := by exact prefixLift 1409664
  have htrace : WordTrace (prefixWord ++ tailWord_1409664) baseStart_1409664 baseEnd_1409664 := by
    simpa [prefixWord, tailWord_1409664, baseEnd_1409664] using wordTrace_append hprefix tailTrace_1409664
  have hstable : (prefixWord ++ tailWord_1409664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409664).length < 2 ^ (prefixWord ++ tailWord_1409664).sum := by decide
  have hdescent : baseEnd_1409664 < baseStart_1409664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409671 : List Nat := [1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 3]
def baseStart_1409671 : Nat := 118140960795 + 1409671 * 2 ^ 59
def prefixEnd_1409671 : Nat := 4983230072969 + 3 ^ 40 * 1409671 * 2
def baseEnd_1409671 : Nat := 723838787704259389429547

theorem tailTrace_1409671 : CollatzResearch.WordTrace tailWord_1409671 prefixEnd_1409671 723838787704259389429547 := by
  unfold tailWord_1409671
  simp only [CollatzResearch.WordTrace]
  refine ⟨51414925276010194484612867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34276616850673462989741911 51414925276010194484612867)
  ·
    refine ⟨77122387914015291726919301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51414925276010194484612867 77122387914015291726919301)
    ·
      refine ⟨14460447733877867198797369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77122387914015291726919301 14460447733877867198797369)
      ·
        refine ⟨10845335800408400399098027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14460447733877867198797369 10845335800408400399098027)
        ·
          refine ⟨16268003700612600598647041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10845335800408400399098027 16268003700612600598647041)
          ·
            refine ⟨12201002775459450448985281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16268003700612600598647041 12201002775459450448985281)
            ·
              refine ⟨9150752081594587836738961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12201002775459450448985281 9150752081594587836738961)
              ·
                refine ⟨6863064061195940877554221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9150752081594587836738961 6863064061195940877554221)
                ·
                  refine ⟨2573649022948477829082833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6863064061195940877554221 2573649022948477829082833)
                  ·
                    refine ⟨1930236767211358371812125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2573649022948477829082833 1930236767211358371812125)
                    ·
                      refine ⟨723838787704259389429547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1930236767211358371812125 723838787704259389429547)
                      ·
                        rfl

theorem cell23_1409671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_1409671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409671 prefixEnd_1409671 := by exact prefixLift 1409671
  have htrace : WordTrace (prefixWord ++ tailWord_1409671) baseStart_1409671 baseEnd_1409671 := by
    simpa [prefixWord, tailWord_1409671, baseEnd_1409671] using wordTrace_append hprefix tailTrace_1409671
  have hstable : (prefixWord ++ tailWord_1409671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409671).length < 2 ^ (prefixWord ++ tailWord_1409671).sum := by decide
  have hdescent : baseEnd_1409671 < baseStart_1409671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409678 : List Nat := [4, 1, 1, 3, 1, 1, 3, 3, 2, 4]
def baseStart_1409678 : Nat := 118140960795 + 1409678 * 2 ^ 59
def prefixEnd_1409678 : Nat := 4983230072969 + 3 ^ 40 * 1409678 * 2
def baseEnd_1409678 : Nat := 241280794022946954014005

theorem tailTrace_1409678 : CollatzResearch.WordTrace tailWord_1409678 prefixEnd_1409678 241280794022946954014005 := by
  unfold tailWord_1409678
  simp only [CollatzResearch.WordTrace]
  refine ⟨6426897573373104335014711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34276787057989889786745125 6426897573373104335014711)
  ·
    refine ⟨9640346360059656502522067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6426897573373104335014711 9640346360059656502522067)
    ·
      refine ⟨14460519540089484753783101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9640346360059656502522067 14460519540089484753783101)
      ·
        refine ⟨5422694827533556782668663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14460519540089484753783101 5422694827533556782668663)
        ·
          refine ⟨8134042241300335174002995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5422694827533556782668663 8134042241300335174002995)
          ·
            refine ⟨12201063361950502761004493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8134042241300335174002995 12201063361950502761004493)
            ·
              refine ⟨4575398760731438535376685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12201063361950502761004493 4575398760731438535376685)
              ·
                refine ⟨1715774535274289450766257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4575398760731438535376685 1715774535274289450766257)
                ·
                  refine ⟨1286830901455717088074693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1715774535274289450766257 1286830901455717088074693)
                  ·
                    refine ⟨241280794022946954014005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1286830901455717088074693 241280794022946954014005)
                    ·
                      rfl

theorem cell23_1409678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_1409678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409678 prefixEnd_1409678 := by exact prefixLift 1409678
  have htrace : WordTrace (prefixWord ++ tailWord_1409678) baseStart_1409678 baseEnd_1409678 := by
    simpa [prefixWord, tailWord_1409678, baseEnd_1409678] using wordTrace_append hprefix tailTrace_1409678
  have hstable : (prefixWord ++ tailWord_1409678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409678).length < 2 ^ (prefixWord ++ tailWord_1409678).sum := by decide
  have hdescent : baseEnd_1409678 < baseStart_1409678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409728 : List Nat := [2, 1, 1, 2, 4, 2, 1, 2, 3, 3, 2]
def baseStart_1409728 : Nat := 118140960795 + 1409728 * 2 ^ 59
def prefixEnd_1409728 : Nat := 4983230072969 + 3 ^ 40 * 1409728 * 2
def baseEnd_1409728 : Nat := 723868056101565666416785

theorem tailTrace_1409728 : CollatzResearch.WordTrace tailWord_1409728 prefixEnd_1409728 723868056101565666416785 := by
  unfold tailWord_1409728
  simp only [CollatzResearch.WordTrace]
  refine ⟨25708502118401846609718919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34278002824535795479625225 25708502118401846609718919)
  ·
    refine ⟨38562753177602769914578379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25708502118401846609718919 38562753177602769914578379)
    ·
      refine ⟨57844129766404154871867569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38562753177602769914578379 57844129766404154871867569)
      ·
        refine ⟨43383097324803116153900677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57844129766404154871867569 43383097324803116153900677)
        ·
          refine ⟨8134330748400584278856377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43383097324803116153900677 8134330748400584278856377)
          ·
            refine ⟨6100748061300438209142283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8134330748400584278856377 6100748061300438209142283)
            ·
              refine ⟨9151122091950657313713425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6100748061300438209142283 9151122091950657313713425)
              ·
                refine ⟨6863341568962992985285069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9151122091950657313713425 6863341568962992985285069)
                ·
                  refine ⟨2573753088361122369481901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6863341568962992985285069 2573753088361122369481901)
                  ·
                    refine ⟨965157408135420888555713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2573753088361122369481901 965157408135420888555713)
                    ·
                      refine ⟨723868056101565666416785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 965157408135420888555713 723868056101565666416785)
                      ·
                        rfl

theorem cell23_1409728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 3, 3, 2].length) (baseStart_1409728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409728 prefixEnd_1409728 := by exact prefixLift 1409728
  have htrace : WordTrace (prefixWord ++ tailWord_1409728) baseStart_1409728 baseEnd_1409728 := by
    simpa [prefixWord, tailWord_1409728, baseEnd_1409728] using wordTrace_append hprefix tailTrace_1409728
  have hstable : (prefixWord ++ tailWord_1409728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409728).length < 2 ^ (prefixWord ++ tailWord_1409728).sum := by decide
  have hdescent : baseEnd_1409728 < baseStart_1409728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409775 : List Nat := [1, 1, 2, 1, 5, 3, 1, 1, 4, 2, 2]
def baseStart_1409775 : Nat := 118140960795 + 1409775 * 2 ^ 59
def prefixEnd_1409775 : Nat := 4983230072969 + 3 ^ 40 * 1409775 * 2
def baseEnd_1409775 : Nat := 723892189692326982529069

theorem tailTrace_1409775 : CollatzResearch.WordTrace tailWord_1409775 prefixEnd_1409775 723892189692326982529069 := by
  unfold tailWord_1409775
  simp only [CollatzResearch.WordTrace]
  refine ⟨51418718467633420246398779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34279145645088946830932519 51418718467633420246398779)
  ·
    refine ⟨77128077701450130369598169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51418718467633420246398779 77128077701450130369598169)
    ·
      refine ⟨57846058276087597777198627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77128077701450130369598169 57846058276087597777198627)
      ·
        refine ⟨86769087414131396665797941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57846058276087597777198627 86769087414131396665797941)
        ·
          refine ⟨8134601945074818437418557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86769087414131396665797941 8134601945074818437418557)
          ·
            refine ⟨3050475729403056914031959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8134601945074818437418557 3050475729403056914031959)
            ·
              refine ⟨4575713594104585371047939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3050475729403056914031959 4575713594104585371047939)
              ·
                refine ⟨6863570391156878056571909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4575713594104585371047939 6863570391156878056571909)
                ·
                  refine ⟨1286919448341914635607233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6863570391156878056571909 1286919448341914635607233)
                  ·
                    refine ⟨965189586256435976705425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1286919448341914635607233 965189586256435976705425)
                    ·
                      refine ⟨723892189692326982529069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 965189586256435976705425 723892189692326982529069)
                      ·
                        rfl

theorem cell23_1409775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 2, 2].length) (baseStart_1409775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409775 prefixEnd_1409775 := by exact prefixLift 1409775
  have htrace : WordTrace (prefixWord ++ tailWord_1409775) baseStart_1409775 baseEnd_1409775 := by
    simpa [prefixWord, tailWord_1409775, baseEnd_1409775] using wordTrace_append hprefix tailTrace_1409775
  have hstable : (prefixWord ++ tailWord_1409775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409775).length < 2 ^ (prefixWord ++ tailWord_1409775).sum := by decide
  have hdescent : baseEnd_1409775 < baseStart_1409775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409811 : List Nat := [1, 1, 1, 2, 1, 3, 4, 3, 2, 5]
def baseStart_1409811 : Nat := 118140960795 + 1409811 * 2 ^ 59
def prefixEnd_1409811 : Nat := 4983230072969 + 3 ^ 40 * 1409811 * 2
def baseEnd_1409811 : Nat := 241303558331962947226301

theorem tailTrace_1409811 : CollatzResearch.WordTrace tailWord_1409811 prefixEnd_1409811 241303558331962947226301 := by
  unfold tailWord_1409811
  simp only [CollatzResearch.WordTrace]
  refine ⟨51420031495502998394709287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34280020997001998929806191 51420031495502998394709287)
  ·
    refine ⟨77130047243254497592063931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51420031495502998394709287 77130047243254497592063931)
    ·
      refine ⟨115695070864881746388095897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77130047243254497592063931 115695070864881746388095897)
      ·
        refine ⟨86771303148661309791071923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115695070864881746388095897 86771303148661309791071923)
        ·
          refine ⟨130156954722991964686607885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86771303148661309791071923 130156954722991964686607885)
          ·
            refine ⟨48808858021121986757477957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130156954722991964686607885 48808858021121986757477957)
            ·
              refine ⟨9151660878960372517027117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48808858021121986757477957 9151660878960372517027117)
              ·
                refine ⟨3431872829610139693885169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9151660878960372517027117 3431872829610139693885169)
                ·
                  refine ⟨2573904622207604770413877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3431872829610139693885169 2573904622207604770413877)
                  ·
                    refine ⟨241303558331962947226301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2573904622207604770413877 241303558331962947226301)
                    ·
                      rfl

theorem cell23_1409811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 5].length) (baseStart_1409811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409811 prefixEnd_1409811 := by exact prefixLift 1409811
  have htrace : WordTrace (prefixWord ++ tailWord_1409811) baseStart_1409811 baseEnd_1409811 := by
    simpa [prefixWord, tailWord_1409811, baseEnd_1409811] using wordTrace_append hprefix tailTrace_1409811
  have hstable : (prefixWord ++ tailWord_1409811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409811).length < 2 ^ (prefixWord ++ tailWord_1409811).sum := by decide
  have hdescent : baseEnd_1409811 < baseStart_1409811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409838 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1409838 : Nat := 118140960795 + 1409838 * 2 ^ 59
def prefixEnd_1409838 : Nat := 4983230072969 + 3 ^ 40 * 1409838 * 2
def baseEnd_1409838 : Nat := 723924538973560236041279

theorem tailTrace_1409838 : CollatzResearch.WordTrace tailWord_1409838 prefixEnd_1409838 723924538973560236041279 := by
  unfold tailWord_1409838
  simp only [CollatzResearch.WordTrace]
  refine ⟨6427627033300647750742771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34280677510936788003961445 6427627033300647750742771)
  ·
    refine ⟨9641440549950971626114157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6427627033300647750742771 9641440549950971626114157)
    ·
      refine ⟨3615540206231614359792809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9641440549950971626114157 3615540206231614359792809)
      ·
        refine ⟨2711655154673710769844607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3615540206231614359792809 2711655154673710769844607)
        ·
          refine ⟨4067482732010566154766911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2711655154673710769844607 4067482732010566154766911)
          ·
            refine ⟨6101224098015849232150367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4067482732010566154766911 6101224098015849232150367)
            ·
              refine ⟨9151836147023773848225551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6101224098015849232150367 9151836147023773848225551)
              ·
                refine ⟨13727754220535660772338327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9151836147023773848225551 13727754220535660772338327)
                ·
                  refine ⟨20591631330803491158507491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13727754220535660772338327 20591631330803491158507491)
                  ·
                    refine ⟨30887446996205236737761237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20591631330803491158507491 30887446996205236737761237)
                    ·
                      refine ⟨723924538973560236041279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 30887446996205236737761237 723924538973560236041279)
                      ·
                        rfl

theorem cell23_1409838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1409838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409838 prefixEnd_1409838 := by exact prefixLift 1409838
  have htrace : WordTrace (prefixWord ++ tailWord_1409838) baseStart_1409838 baseEnd_1409838 := by
    simpa [prefixWord, tailWord_1409838, baseEnd_1409838] using wordTrace_append hprefix tailTrace_1409838
  have hstable : (prefixWord ++ tailWord_1409838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409838).length < 2 ^ (prefixWord ++ tailWord_1409838).sum := by decide
  have hdescent : baseEnd_1409838 < baseStart_1409838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409848 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 1, 6, 2]
def baseStart_1409848 : Nat := 118140960795 + 1409848 * 2 ^ 59
def prefixEnd_1409848 : Nat := 4983230072969 + 3 ^ 40 * 1409848 * 2
def baseEnd_1409848 : Nat := 723929673780105196916233

theorem tailTrace_1409848 : CollatzResearch.WordTrace tailWord_1409848 prefixEnd_1409848 723929673780105196916233 := by
  unfold tailWord_1409848
  simp only [CollatzResearch.WordTrace]
  refine ⟨25710690498184476856903099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34280920664245969142537465 25710690498184476856903099)
  ·
    refine ⟨38566035747276715285354649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25710690498184476856903099 38566035747276715285354649)
    ·
      refine ⟨28924526810457536464015987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38566035747276715285354649 28924526810457536464015987)
      ·
        refine ⟨43386790215686304696023981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28924526810457536464015987 43386790215686304696023981)
        ·
          refine ⟨16270046330882364261008993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43386790215686304696023981 16270046330882364261008993)
          ·
            refine ⟨12202534748161773195756745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16270046330882364261008993 12202534748161773195756745)
            ·
              refine ⟨9151901061121329896817559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12202534748161773195756745 9151901061121329896817559)
              ·
                refine ⟨13727851591681994845226339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9151901061121329896817559 13727851591681994845226339)
                ·
                  refine ⟨20591777387522992267839509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13727851591681994845226339 20591777387522992267839509)
                  ·
                    refine ⟨965239565040140262554977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20591777387522992267839509 965239565040140262554977)
                    ·
                      refine ⟨723929673780105196916233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 965239565040140262554977 723929673780105196916233)
                      ·
                        rfl

theorem cell23_1409848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 1, 6, 2].length) (baseStart_1409848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409848 prefixEnd_1409848 := by exact prefixLift 1409848
  have htrace : WordTrace (prefixWord ++ tailWord_1409848) baseStart_1409848 baseEnd_1409848 := by
    simpa [prefixWord, tailWord_1409848, baseEnd_1409848] using wordTrace_append hprefix tailTrace_1409848
  have hstable : (prefixWord ++ tailWord_1409848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409848).length < 2 ^ (prefixWord ++ tailWord_1409848).sum := by decide
  have hdescent : baseEnd_1409848 < baseStart_1409848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409888 : List Nat := [2, 1, 1, 3, 3, 1, 4, 2, 6]
def baseStart_1409888 : Nat := 118140960795 + 1409888 * 2 ^ 59
def prefixEnd_1409888 : Nat := 4983230072969 + 3 ^ 40 * 1409888 * 2
def baseEnd_1409888 : Nat := 80438912556253893379561

theorem tailTrace_1409888 : CollatzResearch.WordTrace tailWord_1409888 prefixEnd_1409888 80438912556253893379561 := by
  unfold tailWord_1409888
  simp only [CollatzResearch.WordTrace]
  refine ⟨25711419958112020272631159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34281893277482693696841545 25711419958112020272631159)
  ·
    refine ⟨38567129937168030408946739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25711419958112020272631159 38567129937168030408946739)
    ·
      refine ⟨57850694905752045613420109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38567129937168030408946739 57850694905752045613420109)
      ·
        refine ⟨21694010589657017105032541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57850694905752045613420109 21694010589657017105032541)
        ·
          refine ⟨8135253971121381414387203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21694010589657017105032541 8135253971121381414387203)
          ·
            refine ⟨12202880956682072121580805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8135253971121381414387203 12202880956682072121580805)
            ·
              refine ⟨2288040179377888522796401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12202880956682072121580805 2288040179377888522796401)
              ·
                refine ⟨1716030134533416392097301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2288040179377888522796401 1716030134533416392097301)
                ·
                  refine ⟨80438912556253893379561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1716030134533416392097301 80438912556253893379561)
                  ·
                    rfl

theorem cell23_1409888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 6].length) (baseStart_1409888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409888 prefixEnd_1409888 := by exact prefixLift 1409888
  have htrace : WordTrace (prefixWord ++ tailWord_1409888) baseStart_1409888 baseEnd_1409888 := by
    simpa [prefixWord, tailWord_1409888, baseEnd_1409888] using wordTrace_append hprefix tailTrace_1409888
  have hstable : (prefixWord ++ tailWord_1409888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409888).length < 2 ^ (prefixWord ++ tailWord_1409888).sum := by decide
  have hdescent : baseEnd_1409888 < baseStart_1409888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409892 : List Nat := [2, 3, 1, 1, 4, 2, 1, 4, 1, 4]
def baseStart_1409892 : Nat := 118140960795 + 1409892 * 2 ^ 59
def prefixEnd_1409892 : Nat := 4983230072969 + 3 ^ 40 * 1409892 * 2
def baseEnd_1409892 : Nat := 241317422309634341588677

theorem tailTrace_1409892 : CollatzResearch.WordTrace tailWord_1409892 prefixEnd_1409892 241317422309634341588677 := by
  unfold tailWord_1409892
  simp only [CollatzResearch.WordTrace]
  refine ⟨25711492904104774614203965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34281990538806366152271953 25711492904104774614203965)
  ·
    refine ⟨9641809839039290480326487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25711492904104774614203965 9641809839039290480326487)
    ·
      refine ⟨14462714758558935720489731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9641809839039290480326487 14462714758558935720489731)
      ·
        refine ⟨21694072137838403580734597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14462714758558935720489731 21694072137838403580734597)
        ·
          refine ⟨4067638525844700671387737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21694072137838403580734597 4067638525844700671387737)
          ·
            refine ⟨3050728894383525503540803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4067638525844700671387737 3050728894383525503540803)
            ·
              refine ⟨4576093341575288255311205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3050728894383525503540803 4576093341575288255311205)
              ·
                refine ⟨858017501545366547870851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4576093341575288255311205 858017501545366547870851)
                ·
                  refine ⟨1287026252318049821806277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 858017501545366547870851 1287026252318049821806277)
                  ·
                    refine ⟨241317422309634341588677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1287026252318049821806277 241317422309634341588677)
                    ·
                      rfl

theorem cell23_1409892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_1409892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409892 prefixEnd_1409892 := by exact prefixLift 1409892
  have htrace : WordTrace (prefixWord ++ tailWord_1409892) baseStart_1409892 baseEnd_1409892 := by
    simpa [prefixWord, tailWord_1409892, baseEnd_1409892] using wordTrace_append hprefix tailTrace_1409892
  have hstable : (prefixWord ++ tailWord_1409892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409892).length < 2 ^ (prefixWord ++ tailWord_1409892).sum := by decide
  have hdescent : baseEnd_1409892 < baseStart_1409892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409925 : List Nat := [1, 3, 1, 1, 3, 4, 1, 1, 1, 5, 2]
def baseStart_1409925 : Nat := 118140960795 + 1409925 * 2 ^ 59
def prefixEnd_1409925 : Nat := 4983230072969 + 3 ^ 40 * 1409925 * 2
def baseEnd_1409925 : Nat := 723969211790501395653379

theorem tailTrace_1409925 : CollatzResearch.WordTrace tailWord_1409925 prefixEnd_1409925 723969211790501395653379 := by
  unfold tailWord_1409925
  simp only [CollatzResearch.WordTrace]
  refine ⟨51424189417089995864359229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34282792944726663909572819 51424189417089995864359229)
  ·
    refine ⟨19284071031408748449134711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51424189417089995864359229 19284071031408748449134711)
    ·
      refine ⟨28926106547113122673702067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19284071031408748449134711 28926106547113122673702067)
      ·
        refine ⟨43389159820669684010553101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28926106547113122673702067 43389159820669684010553101)
        ·
          refine ⟨16270934932751131503957413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43389159820669684010553101 16270934932751131503957413)
          ·
            refine ⟨3050800299890837156992015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16270934932751131503957413 3050800299890837156992015)
            ·
              refine ⟨4576200449836255735488023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3050800299890837156992015 4576200449836255735488023)
              ·
                refine ⟨6864300674754383603232035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4576200449836255735488023 6864300674754383603232035)
                ·
                  refine ⟨10296451012131575404848053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6864300674754383603232035 10296451012131575404848053)
                  ·
                    refine ⟨965292282387335194204505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10296451012131575404848053 965292282387335194204505)
                    ·
                      refine ⟨723969211790501395653379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 965292282387335194204505 723969211790501395653379)
                      ·
                        rfl

theorem cell23_1409925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 5, 2].length) (baseStart_1409925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409925 prefixEnd_1409925 := by exact prefixLift 1409925
  have htrace : WordTrace (prefixWord ++ tailWord_1409925) baseStart_1409925 baseEnd_1409925 := by
    simpa [prefixWord, tailWord_1409925, baseEnd_1409925] using wordTrace_append hprefix tailTrace_1409925
  have hstable : (prefixWord ++ tailWord_1409925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409925).length < 2 ^ (prefixWord ++ tailWord_1409925).sum := by decide
  have hdescent : baseEnd_1409925 < baseStart_1409925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409932 : List Nat := [2, 2, 1, 2, 1, 2, 3, 5, 1, 1, 3]
def baseStart_1409932 : Nat := 118140960795 + 1409932 * 2 ^ 59
def prefixEnd_1409932 : Nat := 4983230072969 + 3 ^ 40 * 1409932 * 2
def baseEnd_1409932 : Nat := 723972806155082868265847

theorem tailTrace_1409932 : CollatzResearch.WordTrace tailWord_1409932 prefixEnd_1409932 723972806155082868265847 := by
  unfold tailWord_1409932
  simp only [CollatzResearch.WordTrace]
  refine ⟨25712222364032318029932025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34282963152043090706576033 25712222364032318029932025)
  ·
    refine ⟨19284166773024238522449019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25712222364032318029932025 19284166773024238522449019)
    ·
      refine ⟨28926250159536357783673529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19284166773024238522449019 28926250159536357783673529)
      ·
        refine ⟨21694687619652268337755147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28926250159536357783673529 21694687619652268337755147)
        ·
          refine ⟨32542031429478402506632721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21694687619652268337755147 32542031429478402506632721)
          ·
            refine ⟨24406523572108801879974541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32542031429478402506632721 24406523572108801879974541)
            ·
              refine ⟨9152446339540800704990453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24406523572108801879974541 9152446339540800704990453)
              ·
                refine ⟨858041844331950066092855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9152446339540800704990453 858041844331950066092855)
                ·
                  refine ⟨1287062766497925099139283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 858041844331950066092855 1287062766497925099139283)
                  ·
                    refine ⟨1930594149746887648708925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1287062766497925099139283 1930594149746887648708925)
                    ·
                      refine ⟨723972806155082868265847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1930594149746887648708925 723972806155082868265847)
                      ·
                        rfl

theorem cell23_1409932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 1, 1, 3].length) (baseStart_1409932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409932 prefixEnd_1409932 := by exact prefixLift 1409932
  have htrace : WordTrace (prefixWord ++ tailWord_1409932) baseStart_1409932 baseEnd_1409932 := by
    simpa [prefixWord, tailWord_1409932, baseEnd_1409932] using wordTrace_append hprefix tailTrace_1409932
  have hstable : (prefixWord ++ tailWord_1409932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409932).length < 2 ^ (prefixWord ++ tailWord_1409932).sum := by decide
  have hdescent : baseEnd_1409932 < baseStart_1409932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409942 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_1409942 : Nat := 118140960795 + 1409942 * 2 ^ 59
def prefixEnd_1409942 : Nat := 4983230072969 + 3 ^ 40 * 1409942 * 2
def baseEnd_1409942 : Nat := 723977940961627829140801

theorem tailTrace_1409942 : CollatzResearch.WordTrace tailWord_1409942 prefixEnd_1409942 723977940961627829140801 := by
  unfold tailWord_1409942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3214050591126775485483005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34283206305352271845152053 3214050591126775485483005)
  ·
    refine ⟨1205268971672540807056127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3214050591126775485483005 1205268971672540807056127)
    ·
      refine ⟨1807903457508811210584191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1205268971672540807056127 1807903457508811210584191)
      ·
        refine ⟨2711855186263216815876287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1807903457508811210584191 2711855186263216815876287)
        ·
          refine ⟨4067782779394825223814431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2711855186263216815876287 4067782779394825223814431)
          ·
            refine ⟨6101674169092237835721647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4067782779394825223814431 6101674169092237835721647)
            ·
              refine ⟨9152511253638356753582471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6101674169092237835721647 9152511253638356753582471)
              ·
                refine ⟨13728766880457535130373707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9152511253638356753582471 13728766880457535130373707)
                ·
                  refine ⟨20593150320686302695560561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13728766880457535130373707 20593150320686302695560561)
                  ·
                    refine ⟨15444862740514727021670421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20593150320686302695560561 15444862740514727021670421)
                    ·
                      refine ⟨723977940961627829140801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15444862740514727021670421 723977940961627829140801)
                      ·
                        rfl

theorem cell23_1409942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_1409942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409942 prefixEnd_1409942 := by exact prefixLift 1409942
  have htrace : WordTrace (prefixWord ++ tailWord_1409942) baseStart_1409942 baseEnd_1409942 := by
    simpa [prefixWord, tailWord_1409942, baseEnd_1409942] using wordTrace_append hprefix tailTrace_1409942
  have hstable : (prefixWord ++ tailWord_1409942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409942).length < 2 ^ (prefixWord ++ tailWord_1409942).sum := by decide
  have hdescent : baseEnd_1409942 < baseStart_1409942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409961 : List Nat := [1, 2, 1, 1, 1, 1, 6, 10]
def baseStart_1409961 : Nat := 118140960795 + 1409961 * 2 ^ 59
def prefixEnd_1409961 : Nat := 4983230072969 + 3 ^ 40 * 1409961 * 2
def baseEnd_1409961 : Nat := 26814359151631972400119

theorem tailTrace_1409961 : CollatzResearch.WordTrace tailWord_1409961 prefixEnd_1409961 26814359151631972400119 := by
  unfold tailWord_1409961
  simp only [CollatzResearch.WordTrace]
  refine ⟨51425502444959574012669737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34283668296639716008446491 51425502444959574012669737)
  ·
    refine ⟨38569126833719680509502303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51425502444959574012669737 38569126833719680509502303)
    ·
      refine ⟨57853690250579520764253455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38569126833719680509502303 57853690250579520764253455)
      ·
        refine ⟨86780535375869281146380183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57853690250579520764253455 86780535375869281146380183)
        ·
          refine ⟨130170803063803921719570275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86780535375869281146380183 130170803063803921719570275)
          ·
            refine ⟨195256204595705882579355413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130170803063803921719570275 195256204595705882579355413)
            ·
              refine ⟨9152634590423713245907285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 195256204595705882579355413 9152634590423713245907285)
              ·
                refine ⟨26814359151631972400119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9152634590423713245907285 26814359151631972400119)
                ·
                  rfl

theorem cell23_1409961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 10].length) (baseStart_1409961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409961 prefixEnd_1409961 := by exact prefixLift 1409961
  have htrace : WordTrace (prefixWord ++ tailWord_1409961) baseStart_1409961 baseEnd_1409961 := by
    simpa [prefixWord, tailWord_1409961, baseEnd_1409961] using wordTrace_append hprefix tailTrace_1409961
  have hstable : (prefixWord ++ tailWord_1409961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409961).length < 2 ^ (prefixWord ++ tailWord_1409961).sum := by decide
  have hdescent : baseEnd_1409961 < baseStart_1409961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1409975 : List Nat := [1, 1, 3, 1, 3, 1, 3, 4, 1, 2, 3]
def baseStart_1409975 : Nat := 118140960795 + 1409975 * 2 ^ 59
def prefixEnd_1409975 : Nat := 4983230072969 + 3 ^ 40 * 1409975 * 2
def baseEnd_1409975 : Nat := 723994885823226200028149

theorem tailTrace_1409975 : CollatzResearch.WordTrace tailWord_1409975 prefixEnd_1409975 723994885823226200028149 := by
  unfold tailWord_1409975
  simp only [CollatzResearch.WordTrace]
  refine ⟨51426013066908854403679379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34284008711272569602452919 51426013066908854403679379)
  ·
    refine ⟨77139019600363281605519069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51426013066908854403679379 77139019600363281605519069)
    ·
      refine ⟨28927132350136230602069651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77139019600363281605519069 28927132350136230602069651)
      ·
        refine ⟨43390698525204345903104477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28927132350136230602069651 43390698525204345903104477)
        ·
          refine ⟨16271511946951629713664179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43390698525204345903104477 16271511946951629713664179)
          ·
            refine ⟨24407267920427444570496269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16271511946951629713664179 24407267920427444570496269)
            ·
              refine ⟨9152725470160291713936101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24407267920427444570496269 9152725470160291713936101)
              ·
                refine ⟨1716136025655054696363019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9152725470160291713936101 1716136025655054696363019)
                ·
                  refine ⟨2574204038482582044544529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1716136025655054696363019 2574204038482582044544529)
                  ·
                    refine ⟨1930653028861936533408397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2574204038482582044544529 1930653028861936533408397)
                    ·
                      refine ⟨723994885823226200028149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1930653028861936533408397 723994885823226200028149)
                      ·
                        rfl

theorem cell23_1409975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 2, 3].length) (baseStart_1409975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1409975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1409975 prefixEnd_1409975 := by exact prefixLift 1409975
  have htrace : WordTrace (prefixWord ++ tailWord_1409975) baseStart_1409975 baseEnd_1409975 := by
    simpa [prefixWord, tailWord_1409975, baseEnd_1409975] using wordTrace_append hprefix tailTrace_1409975
  have hstable : (prefixWord ++ tailWord_1409975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409975).length < 2 ^ (prefixWord ++ tailWord_1409975).sum := by decide
  have hdescent : baseEnd_1409975 < baseStart_1409975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410006 : List Nat := [5, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2]
def baseStart_1410006 : Nat := 118140960795 + 1410006 * 2 ^ 59
def prefixEnd_1410006 : Nat := 4983230072969 + 3 ^ 40 * 1410006 * 2
def baseEnd_1410006 : Nat := 724010803723515578740507

theorem tailTrace_1410006 : CollatzResearch.WordTrace tailWord_1410006 prefixEnd_1410006 724010803723515578740507 := by
  unfold tailWord_1410006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3214196483112284168628617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34284762486531031132038581 3214196483112284168628617)
  ·
    refine ⟨2410647362334213126471463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3214196483112284168628617 2410647362334213126471463)
    ·
      refine ⟨3615971043501319689707195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2410647362334213126471463 3615971043501319689707195)
      ·
        refine ⟨5423956565251979534560793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3615971043501319689707195 5423956565251979534560793)
        ·
          refine ⟨4067967423938984650920595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5423956565251979534560793 4067967423938984650920595)
          ·
            refine ⟨6101951135908476976380893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4067967423938984650920595 6101951135908476976380893)
            ·
              refine ⟨2288231675965678866142835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6101951135908476976380893 2288231675965678866142835)
              ·
                refine ⟨3432347513948518299214253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2288231675965678866142835 3432347513948518299214253)
                ·
                  refine ⟨1287130317730694362205345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3432347513948518299214253 1287130317730694362205345)
                  ·
                    refine ⟨965347738298020771654009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1287130317730694362205345 965347738298020771654009)
                    ·
                      refine ⟨724010803723515578740507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 965347738298020771654009 724010803723515578740507)
                      ·
                        rfl

theorem cell23_1410006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_1410006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410006 prefixEnd_1410006 := by exact prefixLift 1410006
  have htrace : WordTrace (prefixWord ++ tailWord_1410006) baseStart_1410006 baseEnd_1410006 := by
    simpa [prefixWord, tailWord_1410006, baseEnd_1410006] using wordTrace_append hprefix tailTrace_1410006
  have hstable : (prefixWord ++ tailWord_1410006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410006).length < 2 ^ (prefixWord ++ tailWord_1410006).sum := by decide
  have hdescent : baseEnd_1410006 < baseStart_1410006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410079 : List Nat := [1, 1, 2, 4, 1, 3, 2, 3, 2, 2, 2]
def baseStart_1410079 : Nat := 118140960795 + 1410079 * 2 ^ 59
def prefixEnd_1410079 : Nat := 4983230072969 + 3 ^ 40 * 1410079 * 2
def baseEnd_1410079 : Nat := 724048287811293793127671

theorem tailTrace_1410079 : CollatzResearch.WordTrace tailWord_1410079 prefixEnd_1410079 724048287811293793127671 := by
  unfold tailWord_1410079
  simp only [CollatzResearch.WordTrace]
  refine ⟨51429806258532080165465291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34286537505688053443643527 51429806258532080165465291)
  ·
    refine ⟨77144709387798120248197937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51429806258532080165465291 77144709387798120248197937)
    ·
      refine ⟨57858532040848590186148453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77144709387798120248197937 57858532040848590186148453)
      ·
        refine ⟨10848474757659110659902835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57858532040848590186148453 10848474757659110659902835)
        ·
          refine ⟨16272712136488665989854253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10848474757659110659902835 16272712136488665989854253)
          ·
            refine ⟨6102267051183249746195345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16272712136488665989854253 6102267051183249746195345)
            ·
              refine ⟨4576700288387437309646509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6102267051183249746195345 4576700288387437309646509)
              ·
                refine ⟨1716262608145288991117441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4576700288387437309646509 1716262608145288991117441)
                ·
                  refine ⟨1287196956108966743338081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1716262608145288991117441 1287196956108966743338081)
                  ·
                    refine ⟨965397717081725057503561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1287196956108966743338081 965397717081725057503561)
                    ·
                      refine ⟨724048287811293793127671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 965397717081725057503561 724048287811293793127671)
                      ·
                        rfl

theorem cell23_1410079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_1410079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410079 prefixEnd_1410079 := by exact prefixLift 1410079
  have htrace : WordTrace (prefixWord ++ tailWord_1410079) baseStart_1410079 baseEnd_1410079 := by
    simpa [prefixWord, tailWord_1410079, baseEnd_1410079] using wordTrace_append hprefix tailTrace_1410079
  have hstable : (prefixWord ++ tailWord_1410079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410079).length < 2 ^ (prefixWord ++ tailWord_1410079).sum := by decide
  have hdescent : baseEnd_1410079 < baseStart_1410079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410113 : List Nat := [1, 2, 5, 1, 3, 2, 1, 2, 2, 2, 2]
def baseStart_1410113 : Nat := 118140960795 + 1410113 * 2 ^ 59
def prefixEnd_1410113 : Nat := 4983230072969 + 3 ^ 40 * 1410113 * 2
def baseEnd_1410113 : Nat := 724065746153546660102515

theorem tailTrace_1410113 : CollatzResearch.WordTrace tailWord_1410113 prefixEnd_1410113 724065746153546660102515 := by
  unfold tailWord_1410113
  simp only [CollatzResearch.WordTrace]
  refine ⟨51431046340408903972202993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34287364226939269314801995 51431046340408903972202993)
  ·
    refine ⟨38573284755306677979152245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51431046340408903972202993 38573284755306677979152245)
    ·
      refine ⟨3616245445810001060545523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38573284755306677979152245 3616245445810001060545523)
      ·
        refine ⟨5424368168715001590818285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3616245445810001060545523 5424368168715001590818285)
        ·
          refine ⟨2034138063268125596556857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5424368168715001590818285 2034138063268125596556857)
          ·
            refine ⟨1525603547451094197417643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2034138063268125596556857 1525603547451094197417643)
            ·
              refine ⟨2288405321176641296126465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1525603547451094197417643 2288405321176641296126465)
              ·
                refine ⟨1716303990882480972094849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2288405321176641296126465 1716303990882480972094849)
                ·
                  refine ⟨1287227993161860729071137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1716303990882480972094849 1287227993161860729071137)
                  ·
                    refine ⟨965420994871395546803353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1287227993161860729071137 965420994871395546803353)
                    ·
                      refine ⟨724065746153546660102515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 965420994871395546803353 724065746153546660102515)
                      ·
                        rfl

theorem cell23_1410113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_1410113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410113 prefixEnd_1410113 := by exact prefixLift 1410113
  have htrace : WordTrace (prefixWord ++ tailWord_1410113) baseStart_1410113 baseEnd_1410113 := by
    simpa [prefixWord, tailWord_1410113, baseEnd_1410113] using wordTrace_append hprefix tailTrace_1410113
  have hstable : (prefixWord ++ tailWord_1410113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410113).length < 2 ^ (prefixWord ++ tailWord_1410113).sum := by decide
  have hdescent : baseEnd_1410113 < baseStart_1410113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410155 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 3]
def baseStart_1410155 : Nat := 118140960795 + 1410155 * 2 ^ 59
def prefixEnd_1410155 : Nat := 4983230072969 + 3 ^ 40 * 1410155 * 2
def baseEnd_1410155 : Nat := 724087312341035495777321

theorem tailTrace_1410155 : CollatzResearch.WordTrace tailWord_1410155 prefixEnd_1410155 724087312341035495777321 := by
  unfold tailWord_1410155
  simp only [CollatzResearch.WordTrace]
  refine ⟨51432578206256745145231919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34288385470837830096821279 51432578206256745145231919)
  ·
    refine ⟨77148867309385117717847879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51432578206256745145231919 77148867309385117717847879)
    ·
      refine ⟨115723300964077676576771819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77148867309385117717847879 115723300964077676576771819)
      ·
        refine ⟨173584951446116514865157729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115723300964077676576771819 173584951446116514865157729)
        ·
          refine ⟨130188713584587386148868297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173584951446116514865157729 130188713584587386148868297)
          ·
            refine ⟨97641535188440539611651223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130188713584587386148868297 97641535188440539611651223)
            ·
              refine ⟨146462302782660809417476835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97641535188440539611651223 146462302782660809417476835)
              ·
                refine ⟨219693454173991214126215253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146462302782660809417476835 219693454173991214126215253)
                ·
                  refine ⟨2574532666101459540541585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 219693454173991214126215253 2574532666101459540541585)
                  ·
                    refine ⟨1930899499576094655406189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2574532666101459540541585 1930899499576094655406189)
                    ·
                      refine ⟨724087312341035495777321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1930899499576094655406189 724087312341035495777321)
                      ·
                        rfl

theorem cell23_1410155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 3].length) (baseStart_1410155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410155 prefixEnd_1410155 := by exact prefixLift 1410155
  have htrace : WordTrace (prefixWord ++ tailWord_1410155) baseStart_1410155 baseEnd_1410155 := by
    simpa [prefixWord, tailWord_1410155, baseEnd_1410155] using wordTrace_append hprefix tailTrace_1410155
  have hstable : (prefixWord ++ tailWord_1410155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410155).length < 2 ^ (prefixWord ++ tailWord_1410155).sum := by decide
  have hdescent : baseEnd_1410155 < baseStart_1410155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410172 : List Nat := [2, 2, 2, 1, 1, 3, 3, 2, 2, 2, 3]
def baseStart_1410172 : Nat := 118140960795 + 1410172 * 2 ^ 59
def prefixEnd_1410172 : Nat := 4983230072969 + 3 ^ 40 * 1410172 * 2
def baseEnd_1410172 : Nat := 724096041512161929264743

theorem tailTrace_1410172 : CollatzResearch.WordTrace tailWord_1410172 prefixEnd_1410172 724096041512161929264743 := by
  unfold tailWord_1410172
  simp only [CollatzResearch.WordTrace]
  refine ⟨25716599123597578524300385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34288798831463438032400513 25716599123597578524300385)
  ·
    refine ⟨19287449342698183893225289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25716599123597578524300385 19287449342698183893225289)
    ·
      refine ⟨14465587007023637919918967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19287449342698183893225289 14465587007023637919918967)
      ·
        refine ⟨21698380510535456879878451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14465587007023637919918967 21698380510535456879878451)
        ·
          refine ⟨32547570765803185319817677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21698380510535456879878451 32547570765803185319817677)
          ·
            refine ⟨12205339037176194494931629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32547570765803185319817677 12205339037176194494931629)
            ·
              refine ⟨4577002138941072935599361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12205339037176194494931629 4577002138941072935599361)
              ·
                refine ⟨3432751604205804701699521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4577002138941072935599361 3432751604205804701699521)
                ·
                  refine ⟨2574563703154353526274641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3432751604205804701699521 2574563703154353526274641)
                  ·
                    refine ⟨1930922777365765144705981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2574563703154353526274641 1930922777365765144705981)
                    ·
                      refine ⟨724096041512161929264743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1930922777365765144705981 724096041512161929264743)
                      ·
                        rfl

theorem cell23_1410172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_1410172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410172 prefixEnd_1410172 := by exact prefixLift 1410172
  have htrace : WordTrace (prefixWord ++ tailWord_1410172) baseStart_1410172 baseEnd_1410172 := by
    simpa [prefixWord, tailWord_1410172, baseEnd_1410172] using wordTrace_append hprefix tailTrace_1410172
  have hstable : (prefixWord ++ tailWord_1410172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410172).length < 2 ^ (prefixWord ++ tailWord_1410172).sum := by decide
  have hdescent : baseEnd_1410172 < baseStart_1410172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410206 : List Nat := [4, 3, 1, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_1410206 : Nat := 118140960795 + 1410206 * 2 ^ 59
def prefixEnd_1410206 : Nat := 4983230072969 + 3 ^ 40 * 1410206 * 2
def baseEnd_1410206 : Nat := 724113499854414796239587

theorem tailTrace_1410206 : CollatzResearch.WordTrace tailWord_1410206 prefixEnd_1410206 724113499854414796239587 := by
  unfold tailWord_1410206
  simp only [CollatzResearch.WordTrace]
  refine ⟨6429304791133997606917309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34289625552714653903558981 6429304791133997606917309)
  ·
    refine ⟨2410989296675249102593991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6429304791133997606917309 2410989296675249102593991)
    ·
      refine ⟨3616483945012873653890987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2410989296675249102593991 3616483945012873653890987)
      ·
        refine ⟨5424725917519310480836481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3616483945012873653890987 5424725917519310480836481)
        ·
          refine ⟨4068544438139482860627361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5424725917519310480836481 4068544438139482860627361)
          ·
            refine ⟨3051408328604612145470521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4068544438139482860627361 3051408328604612145470521)
            ·
              refine ⟨2288556246453459109102891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3051408328604612145470521 2288556246453459109102891)
              ·
                refine ⟨3432834369680188663654337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2288556246453459109102891 3432834369680188663654337)
                ·
                  refine ⟨2574625777260141497740753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3432834369680188663654337 2574625777260141497740753)
                  ·
                    refine ⟨1930969332945106123305565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2574625777260141497740753 1930969332945106123305565)
                    ·
                      refine ⟨724113499854414796239587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1930969332945106123305565 724113499854414796239587)
                      ·
                        rfl

theorem cell23_1410206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_1410206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410206 prefixEnd_1410206 := by exact prefixLift 1410206
  have htrace : WordTrace (prefixWord ++ tailWord_1410206) baseStart_1410206 baseEnd_1410206 := by
    simpa [prefixWord, tailWord_1410206, baseEnd_1410206] using wordTrace_append hprefix tailTrace_1410206
  have hstable : (prefixWord ++ tailWord_1410206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410206).length < 2 ^ (prefixWord ++ tailWord_1410206).sum := by decide
  have hdescent : baseEnd_1410206 < baseStart_1410206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410230 : List Nat := [5, 1, 3, 2, 1, 1, 1, 4, 1, 4]
def baseStart_1410230 : Nat := 118140960795 + 1410230 * 2 ^ 59
def prefixEnd_1410230 : Nat := 4983230072969 + 3 ^ 40 * 1410230 * 2
def baseEnd_1410230 : Nat := 241375274463374234113159

theorem tailTrace_1410230 : CollatzResearch.WordTrace tailWord_1410230 prefixEnd_1410230 241375274463374234113159 := by
  unfold tailWord_1410230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3214707105061564559638259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34290209120656688636141429 3214707105061564559638259)
  ·
    refine ⟨4822060657592346839457389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3214707105061564559638259 4822060657592346839457389)
    ·
      refine ⟨1808272746597130064796521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4822060657592346839457389 1808272746597130064796521)
      ·
        refine ⟨1356204559947847548597391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1808272746597130064796521 1356204559947847548597391)
        ·
          refine ⟨2034306839921771322896087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1356204559947847548597391 2034306839921771322896087)
          ·
            refine ⟨3051460259882656984344131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2034306839921771322896087 3051460259882656984344131)
            ·
              refine ⟨4577190389823985476516197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3051460259882656984344131 4577190389823985476516197)
              ·
                refine ⟨858223198091997276846787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4577190389823985476516197 858223198091997276846787)
                ·
                  refine ⟨1287334797137995915270181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 858223198091997276846787 1287334797137995915270181)
                  ·
                    refine ⟨241375274463374234113159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1287334797137995915270181 241375274463374234113159)
                    ·
                      rfl

theorem cell23_1410230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_1410230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410230 prefixEnd_1410230 := by exact prefixLift 1410230
  have htrace : WordTrace (prefixWord ++ tailWord_1410230) baseStart_1410230 baseEnd_1410230 := by
    simpa [prefixWord, tailWord_1410230, baseEnd_1410230] using wordTrace_append hprefix tailTrace_1410230
  have hstable : (prefixWord ++ tailWord_1410230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410230).length < 2 ^ (prefixWord ++ tailWord_1410230).sum := by decide
  have hdescent : baseEnd_1410230 < baseStart_1410230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410245 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 3, 1, 5]
def baseStart_1410245 : Nat := 118140960795 + 1410245 * 2 ^ 59
def prefixEnd_1410245 : Nat := 4983230072969 + 3 ^ 40 * 1410245 * 2
def baseEnd_1410245 : Nat := 724133525599940143651907

theorem tailTrace_1410245 : CollatzResearch.WordTrace tailWord_1410245 prefixEnd_1410245 724133525599940143651907 := by
  unfold tailWord_1410245
  simp only [CollatzResearch.WordTrace]
  refine ⟨51435860775930690516008189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34290573850620460344005459 51435860775930690516008189)
  ·
    refine ⟨19288447790974008943503071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51435860775930690516008189 19288447790974008943503071)
    ·
      refine ⟨28932671686461013415254607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19288447790974008943503071 28932671686461013415254607)
      ·
        refine ⟨43399007529691520122881911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28932671686461013415254607 43399007529691520122881911)
        ·
          refine ⟨65098511294537280184322867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43399007529691520122881911 65098511294537280184322867)
          ·
            refine ⟨97647766941805920276484301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65098511294537280184322867 97647766941805920276484301)
            ·
              refine ⟨36617912603177220103681613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97647766941805920276484301 36617912603177220103681613)
              ·
                refine ⟨13731717226191457538880605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36617912603177220103681613 13731717226191457538880605)
                ·
                  refine ⟨5149393959821796577080227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13731717226191457538880605 5149393959821796577080227)
                  ·
                    refine ⟨7724090939732694865620341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5149393959821796577080227 7724090939732694865620341)
                    ·
                      refine ⟨724133525599940143651907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7724090939732694865620341 724133525599940143651907)
                      ·
                        rfl

theorem cell23_1410245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_1410245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410245 prefixEnd_1410245 := by exact prefixLift 1410245
  have htrace : WordTrace (prefixWord ++ tailWord_1410245) baseStart_1410245 baseEnd_1410245 := by
    simpa [prefixWord, tailWord_1410245, baseEnd_1410245] using wordTrace_append hprefix tailTrace_1410245
  have hstable : (prefixWord ++ tailWord_1410245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410245).length < 2 ^ (prefixWord ++ tailWord_1410245).sum := by decide
  have hdescent : baseEnd_1410245 < baseStart_1410245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410259 : List Nat := [1, 1, 1, 2, 1, 1, 1, 8, 3, 2, 2]
def baseStart_1410259 : Nat := 118140960795 + 1410259 * 2 ^ 59
def prefixEnd_1410259 : Nat := 4983230072969 + 3 ^ 40 * 1410259 * 2
def baseEnd_1410259 : Nat := 724140714329103088876843

theorem tailTrace_1410259 : CollatzResearch.WordTrace tailWord_1410259 prefixEnd_1410259 724140714329103088876843 := by
  unfold tailWord_1410259
  simp only [CollatzResearch.WordTrace]
  refine ⟨51436371397879970907017831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34290914265253313938011887 51436371397879970907017831)
  ·
    refine ⟨77154557096819956360526747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51436371397879970907017831 77154557096819956360526747)
    ·
      refine ⟨115731835645229934540790121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77154557096819956360526747 115731835645229934540790121)
      ·
        refine ⟨86798876733922450905592591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115731835645229934540790121 86798876733922450905592591)
        ·
          refine ⟨130198315100883676358388887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86798876733922450905592591 130198315100883676358388887)
          ·
            refine ⟨195297472651325514537583331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130198315100883676358388887 195297472651325514537583331)
            ·
              refine ⟨292946208976988271806374997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195297472651325514537583331 292946208976988271806374997)
              ·
                refine ⟨3432963386449081310230957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 292946208976988271806374997 3432963386449081310230957)
                ·
                  refine ⟨1287361269918405491336609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3432963386449081310230957 1287361269918405491336609)
                  ·
                    refine ⟨965520952438804118502457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1287361269918405491336609 965520952438804118502457)
                    ·
                      refine ⟨724140714329103088876843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 965520952438804118502457 724140714329103088876843)
                      ·
                        rfl

theorem cell23_1410259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 2, 2].length) (baseStart_1410259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410259 prefixEnd_1410259 := by exact prefixLift 1410259
  have htrace : WordTrace (prefixWord ++ tailWord_1410259) baseStart_1410259 baseEnd_1410259 := by
    simpa [prefixWord, tailWord_1410259, baseEnd_1410259] using wordTrace_append hprefix tailTrace_1410259
  have hstable : (prefixWord ++ tailWord_1410259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410259).length < 2 ^ (prefixWord ++ tailWord_1410259).sum := by decide
  have hdescent : baseEnd_1410259 < baseStart_1410259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410272 : List Nat := [2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 4]
def baseStart_1410272 : Nat := 118140960795 + 1410272 * 2 ^ 59
def prefixEnd_1410272 : Nat := 4983230072969 + 3 ^ 40 * 1410272 * 2
def baseEnd_1410272 : Nat := 724147389577611538014283

theorem tailTrace_1410272 : CollatzResearch.WordTrace tailWord_1410272 prefixEnd_1410272 724147389577611538014283 := by
  unfold tailWord_1410272
  simp only [CollatzResearch.WordTrace]
  refine ⟨25718422773416437063620535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34291230364555249418160713 25718422773416437063620535)
  ·
    refine ⟨38577634160124655595430803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25718422773416437063620535 38577634160124655595430803)
    ·
      refine ⟨57866451240186983393146205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38577634160124655595430803 57866451240186983393146205)
      ·
        refine ⟨21699919215070118772429827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57866451240186983393146205 21699919215070118772429827)
        ·
          refine ⟨32549878822605178158644741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21699919215070118772429827 32549878822605178158644741)
          ·
            refine ⟨6103102279238470904745889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32549878822605178158644741 6103102279238470904745889)
            ·
              refine ⟨4577326709428853178559417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6103102279238470904745889 4577326709428853178559417)
              ·
                refine ⟨3432995032071639883919563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4577326709428853178559417 3432995032071639883919563)
                ·
                  refine ⟨5149492548107459825879345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3432995032071639883919563 5149492548107459825879345)
                  ·
                    refine ⟨3862119411080594869409509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5149492548107459825879345 3862119411080594869409509)
                    ·
                      refine ⟨724147389577611538014283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3862119411080594869409509 724147389577611538014283)
                      ·
                        rfl

theorem cell23_1410272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_1410272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410272 prefixEnd_1410272 := by exact prefixLift 1410272
  have htrace : WordTrace (prefixWord ++ tailWord_1410272) baseStart_1410272 baseEnd_1410272 := by
    simpa [prefixWord, tailWord_1410272, baseEnd_1410272] using wordTrace_append hprefix tailTrace_1410272
  have hstable : (prefixWord ++ tailWord_1410272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410272).length < 2 ^ (prefixWord ++ tailWord_1410272).sum := by decide
  have hdescent : baseEnd_1410272 < baseStart_1410272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410352 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 3]
def baseStart_1410352 : Nat := 118140960795 + 1410352 * 2 ^ 59
def prefixEnd_1410352 : Nat := 4983230072969 + 3 ^ 40 * 1410352 * 2
def baseEnd_1410352 : Nat := 724188468029971225013915

theorem tailTrace_1410352 : CollatzResearch.WordTrace tailWord_1410352 prefixEnd_1410352 724188468029971225013915 := by
  unfold tailWord_1410352
  simp only [CollatzResearch.WordTrace]
  refine ⟨25719881693271523895076655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34293175591028698526768873 25719881693271523895076655)
  ·
    refine ⟨38579822539907285842614983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25719881693271523895076655 38579822539907285842614983)
    ·
      refine ⟨57869733809860928763922475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38579822539907285842614983 57869733809860928763922475)
      ·
        refine ⟨86804600714791393145883713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57869733809860928763922475 86804600714791393145883713)
        ·
          refine ⟨65103450536093544859412785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86804600714791393145883713 65103450536093544859412785)
          ·
            refine ⟨48827587902070158644559589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65103450536093544859412785 48827587902070158644559589)
            ·
              refine ⟨9155172731638154745854923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48827587902070158644559589 9155172731638154745854923)
              ·
                refine ⟨13732759097457232118782385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9155172731638154745854923 13732759097457232118782385)
                ·
                  refine ⟨10299569323092924089086789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13732759097457232118782385 10299569323092924089086789)
                  ·
                    refine ⟨1931169248079923266703773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10299569323092924089086789 1931169248079923266703773)
                    ·
                      refine ⟨724188468029971225013915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1931169248079923266703773 724188468029971225013915)
                      ·
                        rfl

theorem cell23_1410352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 3].length) (baseStart_1410352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410352 prefixEnd_1410352 := by exact prefixLift 1410352
  have htrace : WordTrace (prefixWord ++ tailWord_1410352) baseStart_1410352 baseEnd_1410352 := by
    simpa [prefixWord, tailWord_1410352, baseEnd_1410352] using wordTrace_append hprefix tailTrace_1410352
  have hstable : (prefixWord ++ tailWord_1410352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410352).length < 2 ^ (prefixWord ++ tailWord_1410352).sum := by decide
  have hdescent : baseEnd_1410352 < baseStart_1410352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410362 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4]
def baseStart_1410362 : Nat := 118140960795 + 1410362 * 2 ^ 59
def prefixEnd_1410362 : Nat := 4983230072969 + 3 ^ 40 * 1410362 * 2
def baseEnd_1410362 : Nat := 724193602836516185888869

theorem tailTrace_1410362 : CollatzResearch.WordTrace tailWord_1410362 prefixEnd_1410362 724193602836516185888869 := by
  unfold tailWord_1410362
  simp only [CollatzResearch.WordTrace]
  refine ⟨12860032029126704874504335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34293418744337879665344893 12860032029126704874504335)
  ·
    refine ⟨19290048043690057311756503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12860032029126704874504335 19290048043690057311756503)
    ·
      refine ⟨28935072065535085967634755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19290048043690057311756503 28935072065535085967634755)
      ·
        refine ⟨43402608098302628951452133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28935072065535085967634755 43402608098302628951452133)
        ·
          refine ⟨8137989018431742928397275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43402608098302628951452133 8137989018431742928397275)
          ·
            refine ⟨12206983527647614392595913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8137989018431742928397275 12206983527647614392595913)
            ·
              refine ⟨9155237645735710794446935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12206983527647614392595913 9155237645735710794446935)
              ·
                refine ⟨13732856468603566191670403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9155237645735710794446935 13732856468603566191670403)
                ·
                  refine ⟨20599284702905349287505605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13732856468603566191670403 20599284702905349287505605)
                  ·
                    refine ⟨3862365881794752991407301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20599284702905349287505605 3862365881794752991407301)
                    ·
                      refine ⟨724193602836516185888869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3862365881794752991407301 724193602836516185888869)
                      ·
                        rfl

theorem cell23_1410362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_1410362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410362 prefixEnd_1410362 := by exact prefixLift 1410362
  have htrace : WordTrace (prefixWord ++ tailWord_1410362) baseStart_1410362 baseEnd_1410362 := by
    simpa [prefixWord, tailWord_1410362, baseEnd_1410362] using wordTrace_append hprefix tailTrace_1410362
  have hstable : (prefixWord ++ tailWord_1410362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410362).length < 2 ^ (prefixWord ++ tailWord_1410362).sum := by decide
  have hdescent : baseEnd_1410362 < baseStart_1410362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410366 : List Nat := [4, 2, 1, 2, 1, 1, 2, 3, 1, 4, 2]
def baseStart_1410366 : Nat := 118140960795 + 1410366 * 2 ^ 59
def prefixEnd_1410366 : Nat := 4983230072969 + 3 ^ 40 * 1410366 * 2
def baseEnd_1410366 : Nat := 724195656759134170238851

theorem tailTrace_1410366 : CollatzResearch.WordTrace tailWord_1410366 prefixEnd_1410366 724195656759134170238851 := by
  unfold tailWord_1410366
  simp only [CollatzResearch.WordTrace]
  refine ⟨6430034251061541022645369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34293516005661552120775301 6430034251061541022645369)
  ·
    refine ⟨4822525688296155766984027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6430034251061541022645369 4822525688296155766984027)
    ·
      refine ⟨7233788532444233650476041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4822525688296155766984027 7233788532444233650476041)
      ·
        refine ⟨5425341399333175237857031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7233788532444233650476041 5425341399333175237857031)
        ·
          refine ⟨8138012098999762856785547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5425341399333175237857031 8138012098999762856785547)
          ·
            refine ⟨12207018148499644285178321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8138012098999762856785547 12207018148499644285178321)
            ·
              refine ⟨9155263611374733213883741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12207018148499644285178321 9155263611374733213883741)
              ·
                refine ⟨3433223854265524955206403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9155263611374733213883741 3433223854265524955206403)
                ·
                  refine ⟨5149835781398287432809605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3433223854265524955206403 5149835781398287432809605)
                  ·
                    refine ⟨965594209012178893651801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5149835781398287432809605 965594209012178893651801)
                    ·
                      refine ⟨724195656759134170238851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 965594209012178893651801 724195656759134170238851)
                      ·
                        rfl

theorem cell23_1410366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_1410366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410366 prefixEnd_1410366 := by exact prefixLift 1410366
  have htrace : WordTrace (prefixWord ++ tailWord_1410366) baseStart_1410366 baseEnd_1410366 := by
    simpa [prefixWord, tailWord_1410366, baseEnd_1410366] using wordTrace_append hprefix tailTrace_1410366
  have hstable : (prefixWord ++ tailWord_1410366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410366).length < 2 ^ (prefixWord ++ tailWord_1410366).sum := by decide
  have hdescent : baseEnd_1410366 < baseStart_1410366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410369 : List Nat := [1, 2, 5, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_1410369 : Nat := 118140960795 + 1410369 * 2 ^ 59
def prefixEnd_1410369 : Nat := 4983230072969 + 3 ^ 40 * 1410369 * 2
def baseEnd_1410369 : Nat := 724197197201097658501337

theorem tailTrace_1410369 : CollatzResearch.WordTrace tailWord_1410369 prefixEnd_1410369 724197197201097658501337 := by
  unfold tailWord_1410369
  simp only [CollatzResearch.WordTrace]
  refine ⟨51440383427481459693522161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34293588951654306462348107 51440383427481459693522161)
  ·
    refine ⟨38580287570611094770141621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51440383427481459693522161 38580287570611094770141621)
    ·
      refine ⟨3616901959744790134700777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38580287570611094770141621 3616901959744790134700777)
      ·
        refine ⟨2712676469808592601025583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3616901959744790134700777 2712676469808592601025583)
        ·
          refine ⟨4069014704712888901538375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2712676469808592601025583 4069014704712888901538375)
          ·
            refine ⟨6103522057069333352307563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4069014704712888901538375 6103522057069333352307563)
            ·
              refine ⟨9155283085604000028461345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6103522057069333352307563 9155283085604000028461345)
              ·
                refine ⟨6866462314203000021346009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9155283085604000028461345 6866462314203000021346009)
                ·
                  refine ⟨5149846735652250016009507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6866462314203000021346009 5149846735652250016009507)
                  ·
                    refine ⟨7724770103478375024014261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5149846735652250016009507 7724770103478375024014261)
                    ·
                      refine ⟨724197197201097658501337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7724770103478375024014261 724197197201097658501337)
                      ·
                        rfl

theorem cell23_1410369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_1410369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410369 prefixEnd_1410369 := by exact prefixLift 1410369
  have htrace : WordTrace (prefixWord ++ tailWord_1410369) baseStart_1410369 baseEnd_1410369 := by
    simpa [prefixWord, tailWord_1410369, baseEnd_1410369] using wordTrace_append hprefix tailTrace_1410369
  have hstable : (prefixWord ++ tailWord_1410369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410369).length < 2 ^ (prefixWord ++ tailWord_1410369).sum := by decide
  have hdescent : baseEnd_1410369 < baseStart_1410369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410436 : List Nat := [2, 3, 2, 1, 1, 5, 1, 1, 2, 5]
def baseStart_1410436 : Nat := 118140960795 + 1410436 * 2 ^ 59
def prefixEnd_1410436 : Nat := 4983230072969 + 3 ^ 40 * 1410436 * 2
def baseEnd_1410436 : Nat := 241410533468316298787843

theorem tailTrace_1410436 : CollatzResearch.WordTrace tailWord_1410436 prefixEnd_1410436 241410533468316298787843 := by
  unfold tailWord_1410436
  simp only [CollatzResearch.WordTrace]
  refine ⟨25721413559119365068105581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34295218078825820090807441 25721413559119365068105581)
  ·
    refine ⟨9645530084669761900539593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25721413559119365068105581 9645530084669761900539593)
    ·
      refine ⟨7234147563502321425404695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9645530084669761900539593 7234147563502321425404695)
      ·
        refine ⟨10851221345253482138107043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7234147563502321425404695 10851221345253482138107043)
        ·
          refine ⟨16276832017880223207160565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10851221345253482138107043 16276832017880223207160565)
          ·
            refine ⟨1525953001676270925671303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16276832017880223207160565 1525953001676270925671303)
            ·
              refine ⟨2288929502514406388506955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1525953001676270925671303 2288929502514406388506955)
              ·
                refine ⟨3433394253771609582760433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2288929502514406388506955 3433394253771609582760433)
                ·
                  refine ⟨2575045690328707187070325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3433394253771609582760433 2575045690328707187070325)
                  ·
                    refine ⟨241410533468316298787843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2575045690328707187070325 241410533468316298787843)
                    ·
                      rfl

theorem cell23_1410436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_1410436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410436 prefixEnd_1410436 := by exact prefixLift 1410436
  have htrace : WordTrace (prefixWord ++ tailWord_1410436) baseStart_1410436 baseEnd_1410436 := by
    simpa [prefixWord, tailWord_1410436, baseEnd_1410436] using wordTrace_append hprefix tailTrace_1410436
  have hstable : (prefixWord ++ tailWord_1410436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410436).length < 2 ^ (prefixWord ++ tailWord_1410436).sum := by decide
  have hdescent : baseEnd_1410436 < baseStart_1410436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410439 : List Nat := [1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 4]
def baseStart_1410439 : Nat := 118140960795 + 1410439 * 2 ^ 59
def prefixEnd_1410439 : Nat := 4983230072969 + 3 ^ 40 * 1410439 * 2
def baseEnd_1410439 : Nat := 724233140846912384626015

theorem tailTrace_1410439 : CollatzResearch.WordTrace tailWord_1410439 prefixEnd_1410439 724233140846912384626015 := by
  unfold tailWord_1410439
  simp only [CollatzResearch.WordTrace]
  refine ⟨51442936537227861648570371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34295291024818574432380247 51442936537227861648570371)
  ·
    refine ⟨77164404805841792472855557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51442936537227861648570371 77164404805841792472855557)
    ·
      refine ⟨14468325901095336088660417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77164404805841792472855557 14468325901095336088660417)
      ·
        refine ⟨10851244425821502066495313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14468325901095336088660417 10851244425821502066495313)
        ·
          refine ⟨8138433319366126549871485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10851244425821502066495313 8138433319366126549871485)
          ·
            refine ⟨3051912494762297456201807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8138433319366126549871485 3051912494762297456201807)
            ·
              refine ⟨4577868742143446184302711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3051912494762297456201807 4577868742143446184302711)
              ·
                refine ⟨6866803113215169276454067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4577868742143446184302711 6866803113215169276454067)
                ·
                  refine ⟨10300204669822753914681101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6866803113215169276454067 10300204669822753914681101)
                  ·
                    refine ⟨3862576751183532718005413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10300204669822753914681101 3862576751183532718005413)
                    ·
                      refine ⟨724233140846912384626015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3862576751183532718005413 724233140846912384626015)
                      ·
                        rfl

theorem cell23_1410439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_1410439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410439 prefixEnd_1410439 := by exact prefixLift 1410439
  have htrace : WordTrace (prefixWord ++ tailWord_1410439) baseStart_1410439 baseEnd_1410439 := by
    simpa [prefixWord, tailWord_1410439, baseEnd_1410439] using wordTrace_append hprefix tailTrace_1410439
  have hstable : (prefixWord ++ tailWord_1410439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410439).length < 2 ^ (prefixWord ++ tailWord_1410439).sum := by decide
  have hdescent : baseEnd_1410439 < baseStart_1410439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410466 : List Nat := [3, 3, 1, 2, 1, 2, 1, 3, 3, 4]
def baseStart_1410466 : Nat := 118140960795 + 1410466 * 2 ^ 59
def prefixEnd_1410466 : Nat := 4983230072969 + 3 ^ 40 * 1410466 * 2
def baseEnd_1410466 : Nat := 241415668274861259662797

theorem tailTrace_1410466 : CollatzResearch.WordTrace tailWord_1410466 prefixEnd_1410466 241415668274861259662797 := by
  unfold tailWord_1410466
  simp only [CollatzResearch.WordTrace]
  refine ⟨12860980327032511314950813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34295947538753363506535501 12860980327032511314950813)
  ·
    refine ⟨4822867622637191743106555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12860980327032511314950813 4822867622637191743106555)
    ·
      refine ⟨7234301433955787614659833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4822867622637191743106555 7234301433955787614659833)
      ·
        refine ⟨5425726075466840710994875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7234301433955787614659833 5425726075466840710994875)
        ·
          refine ⟨8138589113200261066492313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5425726075466840710994875 8138589113200261066492313)
          ·
            refine ⟨6103941834900195799869235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8138589113200261066492313 6103941834900195799869235)
            ·
              refine ⟨9155912752350293699803853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6103941834900195799869235 9155912752350293699803853)
              ·
                refine ⟨3433467282131360137426445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9155912752350293699803853 3433467282131360137426445)
                ·
                  refine ⟨1287550230799260051534917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3433467282131360137426445 1287550230799260051534917)
                  ·
                    refine ⟨241415668274861259662797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1287550230799260051534917 241415668274861259662797)
                    ·
                      rfl

theorem cell23_1410466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_1410466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410466 prefixEnd_1410466 := by exact prefixLift 1410466
  have htrace : WordTrace (prefixWord ++ tailWord_1410466) baseStart_1410466 baseEnd_1410466 := by
    simpa [prefixWord, tailWord_1410466, baseEnd_1410466] using wordTrace_append hprefix tailTrace_1410466
  have hstable : (prefixWord ++ tailWord_1410466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410466).length < 2 ^ (prefixWord ++ tailWord_1410466).sum := by decide
  have hdescent : baseEnd_1410466 < baseStart_1410466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410500 : List Nat := [2, 3, 3, 2, 1, 1, 3, 3, 1, 4]
def baseStart_1410500 : Nat := 118140960795 + 1410500 * 2 ^ 59
def prefixEnd_1410500 : Nat := 4983230072969 + 3 ^ 40 * 1410500 * 2
def baseEnd_1410500 : Nat := 241421487722278881987745

theorem tailTrace_1410500 : CollatzResearch.WordTrace tailWord_1410500 prefixEnd_1410500 241421487722278881987745 := by
  unfold tailWord_1410500
  simp only [CollatzResearch.WordTrace]
  refine ⟨25722580695003434533270477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34296774260004579377693969 25722580695003434533270477)
  ·
    refine ⟨9645967760626287949976429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25722580695003434533270477 9645967760626287949976429)
    ·
      refine ⟨3617237910234857981241161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9645967760626287949976429 3617237910234857981241161)
      ·
        refine ⟨2712928432676143485930871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3617237910234857981241161 2712928432676143485930871)
        ·
          refine ⟨4069392649014215228896307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2712928432676143485930871 4069392649014215228896307)
          ·
            refine ⟨6104088973521322843344461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4069392649014215228896307 6104088973521322843344461)
            ·
              refine ⟨2289033365070496066254173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6104088973521322843344461 2289033365070496066254173)
              ·
                refine ⟨858387511901436024845315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2289033365070496066254173 858387511901436024845315)
                ·
                  refine ⟨1287581267852154037267973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 858387511901436024845315 1287581267852154037267973)
                  ·
                    refine ⟨241421487722278881987745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1287581267852154037267973 241421487722278881987745)
                    ·
                      rfl

theorem cell23_1410500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_1410500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410500 prefixEnd_1410500 := by exact prefixLift 1410500
  have htrace : WordTrace (prefixWord ++ tailWord_1410500) baseStart_1410500 baseEnd_1410500 := by
    simpa [prefixWord, tailWord_1410500, baseEnd_1410500] using wordTrace_append hprefix tailTrace_1410500
  have hstable : (prefixWord ++ tailWord_1410500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410500).length < 2 ^ (prefixWord ++ tailWord_1410500).sum := by decide
  have hdescent : baseEnd_1410500 < baseStart_1410500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410539 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 6, 4]
def baseStart_1410539 : Nat := 118140960795 + 1410539 * 2 ^ 59
def prefixEnd_1410539 : Nat := 4983230072969 + 3 ^ 40 * 1410539 * 2
def baseEnd_1410539 : Nat := 241428162970787331125185

theorem tailTrace_1410539 : CollatzResearch.WordTrace tailWord_1410539 prefixEnd_1410539 241428162970787331125185 := by
  unfold tailWord_1410539
  simp only [CollatzResearch.WordTrace]
  refine ⟨51446583836865578727210671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34297722557910385818140447 51446583836865578727210671)
  ·
    refine ⟨77169875755298368090816007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51446583836865578727210671 77169875755298368090816007)
    ·
      refine ⟨115754813632947552136224011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77169875755298368090816007 115754813632947552136224011)
      ·
        refine ⟨173632220449421328204336017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115754813632947552136224011 173632220449421328204336017)
        ·
          refine ⟨130224165337065996153252013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173632220449421328204336017 130224165337065996153252013)
          ·
            refine ⟨48834062001399748557469505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130224165337065996153252013 48834062001399748557469505)
            ·
              refine ⟨36625546501049811418102129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48834062001399748557469505 36625546501049811418102129)
              ·
                refine ⟨27469159875787358563576597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36625546501049811418102129 27469159875787358563576597)
                ·
                  refine ⟨1287616869177532432667653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27469159875787358563576597 1287616869177532432667653)
                  ·
                    refine ⟨241428162970787331125185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1287616869177532432667653 241428162970787331125185)
                    ·
                      rfl

theorem cell23_1410539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 4].length) (baseStart_1410539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410539 prefixEnd_1410539 := by exact prefixLift 1410539
  have htrace : WordTrace (prefixWord ++ tailWord_1410539) baseStart_1410539 baseEnd_1410539 := by
    simpa [prefixWord, tailWord_1410539, baseEnd_1410539] using wordTrace_append hprefix tailTrace_1410539
  have hstable : (prefixWord ++ tailWord_1410539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410539).length < 2 ^ (prefixWord ++ tailWord_1410539).sum := by decide
  have hdescent : baseEnd_1410539 < baseStart_1410539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410550 : List Nat := [5, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2]
def baseStart_1410550 : Nat := 118140960795 + 1410550 * 2 ^ 59
def prefixEnd_1410550 : Nat := 4983230072969 + 3 ^ 40 * 1410550 * 2
def baseEnd_1410550 : Nat := 724290137199561450338005

theorem tailTrace_1410550 : CollatzResearch.WordTrace tailWord_1410550 prefixEnd_1410550 724290137199561450338005 := by
  unfold tailWord_1410550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3215436564989107975366319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34297990026550485070574069 3215436564989107975366319)
  ·
    refine ⟨4823154847483661963049479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3215436564989107975366319 4823154847483661963049479)
    ·
      refine ⟨7234732271225492944574219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4823154847483661963049479 7234732271225492944574219)
      ·
        refine ⟨10852098406838239416861329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7234732271225492944574219 10852098406838239416861329)
        ·
          refine ⟨8139073805128679562645997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10852098406838239416861329 8139073805128679562645997)
          ·
            refine ⟨3052152676923254835992249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8139073805128679562645997 3052152676923254835992249)
            ·
              refine ⟨2289114507692441126994187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3052152676923254835992249 2289114507692441126994187)
              ·
                refine ⟨3433671761538661690491281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2289114507692441126994187 3433671761538661690491281)
                ·
                  refine ⟨2575253821153996267868461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3433671761538661690491281 2575253821153996267868461)
                  ·
                    refine ⟨965720182932748600450673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2575253821153996267868461 965720182932748600450673)
                    ·
                      refine ⟨724290137199561450338005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 965720182932748600450673 724290137199561450338005)
                      ·
                        rfl

theorem cell23_1410550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_1410550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410550 prefixEnd_1410550 := by exact prefixLift 1410550
  have htrace : WordTrace (prefixWord ++ tailWord_1410550) baseStart_1410550 baseEnd_1410550 := by
    simpa [prefixWord, tailWord_1410550, baseEnd_1410550] using wordTrace_append hprefix tailTrace_1410550
  have hstable : (prefixWord ++ tailWord_1410550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410550).length < 2 ^ (prefixWord ++ tailWord_1410550).sum := by decide
  have hdescent : baseEnd_1410550 < baseStart_1410550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410574 : List Nat := [4, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3]
def baseStart_1410574 : Nat := 118140960795 + 1410574 * 2 ^ 59
def prefixEnd_1410574 : Nat := 4983230072969 + 3 ^ 40 * 1410574 * 2
def baseEnd_1410574 : Nat := 724302460735269356437895

theorem tailTrace_1410574 : CollatzResearch.WordTrace tailWord_1410574 prefixEnd_1410574 724302460735269356437895 := by
  unfold tailWord_1410574
  simp only [CollatzResearch.WordTrace]
  refine ⟨6430982548967347463091847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34298573594492519803156517 6430982548967347463091847)
  ·
    refine ⟨9646473823451021194637771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6430982548967347463091847 9646473823451021194637771)
    ·
      refine ⟨14469710735176531791956657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9646473823451021194637771 14469710735176531791956657)
      ·
        refine ⟨10852283051382398843967493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14469710735176531791956657 10852283051382398843967493)
        ·
          refine ⟨2034803072134199783243905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10852283051382398843967493 2034803072134199783243905)
          ·
            refine ⟨1526102304100649837432929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2034803072134199783243905 1526102304100649837432929)
            ·
              refine ⟨1144576728075487378074697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1526102304100649837432929 1144576728075487378074697)
              ·
                refine ⟨858432546056615533556023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1144576728075487378074697 858432546056615533556023)
                ·
                  refine ⟨1287648819084923300334035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 858432546056615533556023 1287648819084923300334035)
                  ·
                    refine ⟨1931473228627384950501053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1287648819084923300334035 1931473228627384950501053)
                    ·
                      refine ⟨724302460735269356437895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1931473228627384950501053 724302460735269356437895)
                      ·
                        rfl

theorem cell23_1410574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_1410574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410574 prefixEnd_1410574 := by exact prefixLift 1410574
  have htrace : WordTrace (prefixWord ++ tailWord_1410574) baseStart_1410574 baseEnd_1410574 := by
    simpa [prefixWord, tailWord_1410574, baseEnd_1410574] using wordTrace_append hprefix tailTrace_1410574
  have hstable : (prefixWord ++ tailWord_1410574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410574).length < 2 ^ (prefixWord ++ tailWord_1410574).sum := by decide
  have hdescent : baseEnd_1410574 < baseStart_1410574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410609 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 2, 2, 5]
def baseStart_1410609 : Nat := 118140960795 + 1410609 * 2 ^ 59
def prefixEnd_1410609 : Nat := 4983230072969 + 3 ^ 40 * 1410609 * 2
def baseEnd_1410609 : Nat := 724320432558176719500233

theorem tailTrace_1410609 : CollatzResearch.WordTrace tailWord_1410609 prefixEnd_1410609 724320432558176719500233 := by
  unfold tailWord_1410609
  simp only [CollatzResearch.WordTrace]
  refine ⟨51449136946611980682258881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34299424631074653788172587 51449136946611980682258881)
  ·
    refine ⟨38586852709958985511694161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51449136946611980682258881 38586852709958985511694161)
    ·
      refine ⟨28940139532469239133770621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38586852709958985511694161 28940139532469239133770621)
      ·
        refine ⟨10852552324675964675163983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28940139532469239133770621 10852552324675964675163983)
        ·
          refine ⟨16278828487013947012745975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10852552324675964675163983 16278828487013947012745975)
          ·
            refine ⟨24418242730520920519118963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16278828487013947012745975 24418242730520920519118963)
            ·
              refine ⟨36627364095781380778678445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24418242730520920519118963 36627364095781380778678445)
              ·
                refine ⟨13735261535918017792004417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36627364095781380778678445 13735261535918017792004417)
                ·
                  refine ⟨10301446151938513344003313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13735261535918017792004417 10301446151938513344003313)
                  ·
                    refine ⟨7726084613953885008002485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10301446151938513344003313 7726084613953885008002485)
                    ·
                      refine ⟨724320432558176719500233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7726084613953885008002485 724320432558176719500233)
                      ·
                        rfl

theorem cell23_1410609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_1410609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410609 prefixEnd_1410609 := by exact prefixLift 1410609
  have htrace : WordTrace (prefixWord ++ tailWord_1410609) baseStart_1410609 baseEnd_1410609 := by
    simpa [prefixWord, tailWord_1410609, baseEnd_1410609] using wordTrace_append hprefix tailTrace_1410609
  have hstable : (prefixWord ++ tailWord_1410609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410609).length < 2 ^ (prefixWord ++ tailWord_1410609).sum := by decide
  have hdescent : baseEnd_1410609 < baseStart_1410609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410614 : List Nat := [5, 1, 2, 1, 4, 1, 2, 1, 1, 1, 4]
def baseStart_1410614 : Nat := 118140960795 + 1410614 * 2 ^ 59
def prefixEnd_1410614 : Nat := 4983230072969 + 3 ^ 40 * 1410614 * 2
def baseEnd_1410614 : Nat := 724322999961449199937711

theorem tailTrace_1410614 : CollatzResearch.WordTrace tailWord_1410614 prefixEnd_1410614 724322999961449199937711 := by
  unfold tailWord_1410614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3215582456974616658511931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34299546207729244357460597 3215582456974616658511931)
  ·
    refine ⟨4823373685461924987767897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3215582456974616658511931 4823373685461924987767897)
    ·
      refine ⟨3617530264096443740825923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4823373685461924987767897 3617530264096443740825923)
      ·
        refine ⟨5426295396144665611238885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3617530264096443740825923 5426295396144665611238885)
        ·
          refine ⟨1017430386777124802107291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5426295396144665611238885 1017430386777124802107291)
          ·
            refine ⟨1526145580165687203160937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1017430386777124802107291 1526145580165687203160937)
            ·
              refine ⟨1144609185124265402370703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1526145580165687203160937 1144609185124265402370703)
              ·
                refine ⟨1716913777686398103556055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1144609185124265402370703 1716913777686398103556055)
                ·
                  refine ⟨2575370666529597155334083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1716913777686398103556055 2575370666529597155334083)
                  ·
                    refine ⟨3863055999794395733001125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2575370666529597155334083 3863055999794395733001125)
                    ·
                      refine ⟨724322999961449199937711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3863055999794395733001125 724322999961449199937711)
                      ·
                        rfl

theorem cell23_1410614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_1410614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410614 prefixEnd_1410614 := by exact prefixLift 1410614
  have htrace : WordTrace (prefixWord ++ tailWord_1410614) baseStart_1410614 baseEnd_1410614 := by
    simpa [prefixWord, tailWord_1410614, baseEnd_1410614] using wordTrace_append hprefix tailTrace_1410614
  have hstable : (prefixWord ++ tailWord_1410614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410614).length < 2 ^ (prefixWord ++ tailWord_1410614).sum := by decide
  have hdescent : baseEnd_1410614 < baseStart_1410614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410629 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 4, 6]
def baseStart_1410629 : Nat := 118140960795 + 1410629 * 2 ^ 59
def prefixEnd_1410629 : Nat := 4983230072969 + 3 ^ 40 * 1410629 * 2
def baseEnd_1410629 : Nat := 241443567390422213750047

theorem tailTrace_1410629 : CollatzResearch.WordTrace tailWord_1410629 prefixEnd_1410629 241443567390422213750047 := by
  unfold tailWord_1410629
  simp only [CollatzResearch.WordTrace]
  refine ⟨51449866406539524097986941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34299910937693016065324627 51449866406539524097986941)
  ·
    refine ⟨19293699902452321536745103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51449866406539524097986941 19293699902452321536745103)
    ·
      refine ⟨28940549853678482305117655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19293699902452321536745103 28940549853678482305117655)
      ·
        refine ⟨43410824780517723457676483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28940549853678482305117655 43410824780517723457676483)
        ·
          refine ⟨65116237170776585186514725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43410824780517723457676483 65116237170776585186514725)
          ·
            refine ⟨12209294469520609722471511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65116237170776585186514725 12209294469520609722471511)
            ·
              refine ⟨18313941704280914583707267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12209294469520609722471511 18313941704280914583707267)
              ·
                refine ⟨27470912556421371875560901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18313941704280914583707267 27470912556421371875560901)
                ·
                  refine ⟨5150796104329007226667669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27470912556421371875560901 5150796104329007226667669)
                  ·
                    refine ⟨241443567390422213750047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5150796104329007226667669 241443567390422213750047)
                    ·
                      rfl

theorem cell23_1410629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_1410629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410629 prefixEnd_1410629 := by exact prefixLift 1410629
  have htrace : WordTrace (prefixWord ++ tailWord_1410629) baseStart_1410629 baseEnd_1410629 := by
    simpa [prefixWord, tailWord_1410629, baseEnd_1410629] using wordTrace_append hprefix tailTrace_1410629
  have hstable : (prefixWord ++ tailWord_1410629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410629).length < 2 ^ (prefixWord ++ tailWord_1410629).sum := by decide
  have hdescent : baseEnd_1410629 < baseStart_1410629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410639 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 5]
def baseStart_1410639 : Nat := 118140960795 + 1410639 * 2 ^ 59
def prefixEnd_1410639 : Nat := 4983230072969 + 3 ^ 40 * 1410639 * 2
def baseEnd_1410639 : Nat := 724335836977811602125095

theorem tailTrace_1410639 : CollatzResearch.WordTrace tailWord_1410639 prefixEnd_1410639 724335836977811602125095 := by
  unfold tailWord_1410639
  simp only [CollatzResearch.WordTrace]
  refine ⟨51450231136503295805850971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34300154091002197203900647 51450231136503295805850971)
  ·
    refine ⟨77175346704754943708776457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51450231136503295805850971 77175346704754943708776457)
    ·
      refine ⟨57881510028566207781582343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77175346704754943708776457 57881510028566207781582343)
      ·
        refine ⟨86822265042849311672373515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57881510028566207781582343 86822265042849311672373515)
        ·
          refine ⟨130233397564273967508560273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86822265042849311672373515 130233397564273967508560273)
          ·
            refine ⟨97675048173205475631420205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130233397564273967508560273 97675048173205475631420205)
            ·
              refine ⟨36628143064952053361782577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97675048173205475631420205 36628143064952053361782577)
              ·
                refine ⟨27471107298714040021336933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36628143064952053361782577 27471107298714040021336933)
                ·
                  refine ⟨5150832618508882504000675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27471107298714040021336933 5150832618508882504000675)
                  ·
                    refine ⟨7726248927763323756001013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5150832618508882504000675 7726248927763323756001013)
                    ·
                      refine ⟨724335836977811602125095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7726248927763323756001013 724335836977811602125095)
                      ·
                        rfl

theorem cell23_1410639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 5].length) (baseStart_1410639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410639 prefixEnd_1410639 := by exact prefixLift 1410639
  have htrace : WordTrace (prefixWord ++ tailWord_1410639) baseStart_1410639 baseEnd_1410639 := by
    simpa [prefixWord, tailWord_1410639, baseEnd_1410639] using wordTrace_append hprefix tailTrace_1410639
  have hstable : (prefixWord ++ tailWord_1410639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410639).length < 2 ^ (prefixWord ++ tailWord_1410639).sum := by decide
  have hdescent : baseEnd_1410639 < baseStart_1410639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410743 : List Nat := [1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 4]
def baseStart_1410743 : Nat := 118140960795 + 1410743 * 2 ^ 59
def prefixEnd_1410743 : Nat := 4983230072969 + 3 ^ 40 * 1410743 * 2
def baseEnd_1410743 : Nat := 724389238965879195224617

theorem tailTrace_1410743 : CollatzResearch.WordTrace tailWord_1410743 prefixEnd_1410743 724389238965879195224617 := by
  unfold tailWord_1410743
  simp only [CollatzResearch.WordTrace]
  refine ⟨51454024328126521567636883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34302682885417681045091255 51454024328126521567636883)
  ·
    refine ⟨77181036492189782351455325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51454024328126521567636883 77181036492189782351455325)
    ·
      refine ⟨28942888684571168381795747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77181036492189782351455325 28942888684571168381795747)
      ·
        refine ⟨43414333026856752572693621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28942888684571168381795747 43414333026856752572693621)
        ·
          refine ⟨4070093721267820553690027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43414333026856752572693621 4070093721267820553690027)
          ·
            refine ⟨6105140581901730830535041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4070093721267820553690027 6105140581901730830535041)
            ·
              refine ⟨4578855436426298122901281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6105140581901730830535041 4578855436426298122901281)
              ·
                refine ⟨3434141577319723592175961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4578855436426298122901281 3434141577319723592175961)
                ·
                  refine ⟨2575606182989792694131971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3434141577319723592175961 2575606182989792694131971)
                  ·
                    refine ⟨3863409274484689041197957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2575606182989792694131971 3863409274484689041197957)
                    ·
                      refine ⟨724389238965879195224617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3863409274484689041197957 724389238965879195224617)
                      ·
                        rfl

theorem cell23_1410743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_1410743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410743 prefixEnd_1410743 := by exact prefixLift 1410743
  have htrace : WordTrace (prefixWord ++ tailWord_1410743) baseStart_1410743 baseEnd_1410743 := by
    simpa [prefixWord, tailWord_1410743, baseEnd_1410743] using wordTrace_append hprefix tailTrace_1410743
  have hstable : (prefixWord ++ tailWord_1410743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410743).length < 2 ^ (prefixWord ++ tailWord_1410743).sum := by decide
  have hdescent : baseEnd_1410743 < baseStart_1410743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410754 : List Nat := [3, 5, 1, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_1410754 : Nat := 118140960795 + 1410754 * 2 ^ 59
def prefixEnd_1410754 : Nat := 4983230072969 + 3 ^ 40 * 1410754 * 2
def baseEnd_1410754 : Nat := 724394887253078652187067

theorem tailTrace_1410754 : CollatzResearch.WordTrace tailWord_1410754 prefixEnd_1410754 724394887253078652187067 := by
  unfold tailWord_1410754
  simp only [CollatzResearch.WordTrace]
  refine ⟨12863606382771667611571829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34302950354057780297524877 12863606382771667611571829)
  ·
    refine ⟨1205963098384843838584859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12863606382771667611571829 1205963098384843838584859)
    ·
      refine ⟨1808944647577265757877289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1205963098384843838584859 1808944647577265757877289)
      ·
        refine ⟨1356708485682949318407967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1808944647577265757877289 1356708485682949318407967)
        ·
          refine ⟨2035062728524423977611951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1356708485682949318407967 2035062728524423977611951)
          ·
            refine ⟨3052594092786635966417927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2035062728524423977611951 3052594092786635966417927)
            ·
              refine ⟨4578891139179953949626891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3052594092786635966417927 4578891139179953949626891)
              ·
                refine ⟨6868336708769930924440337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4578891139179953949626891 6868336708769930924440337)
                ·
                  refine ⟨5151252531577448193330253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6868336708769930924440337 5151252531577448193330253)
                  ·
                    refine ⟨1931719699341543072498845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5151252531577448193330253 1931719699341543072498845)
                    ·
                      refine ⟨724394887253078652187067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1931719699341543072498845 724394887253078652187067)
                      ·
                        rfl

theorem cell23_1410754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_1410754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410754 prefixEnd_1410754 := by exact prefixLift 1410754
  have htrace : WordTrace (prefixWord ++ tailWord_1410754) baseStart_1410754 baseEnd_1410754 := by
    simpa [prefixWord, tailWord_1410754, baseEnd_1410754] using wordTrace_append hprefix tailTrace_1410754
  have hstable : (prefixWord ++ tailWord_1410754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410754).length < 2 ^ (prefixWord ++ tailWord_1410754).sum := by decide
  have hdescent : baseEnd_1410754 < baseStart_1410754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410770 : List Nat := [3, 2, 2, 2, 2, 2, 1, 2, 3, 4]
def baseStart_1410770 : Nat := 118140960795 + 1410770 * 2 ^ 59
def prefixEnd_1410770 : Nat := 4983230072969 + 3 ^ 40 * 1410770 * 2
def baseEnd_1410770 : Nat := 241467700981183529862331

theorem tailTrace_1410770 : CollatzResearch.WordTrace tailWord_1410770 prefixEnd_1410770 241467700981183529862331 := by
  unfold tailWord_1410770
  simp only [CollatzResearch.WordTrace]
  refine ⟨12863752274757176294717441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34303339399352470119246509 12863752274757176294717441)
  ·
    refine ⟨9647814206067882221038081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12863752274757176294717441 9647814206067882221038081)
    ·
      refine ⟨7235860654550911665778561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9647814206067882221038081 7235860654550911665778561)
      ·
        refine ⟨5426895490913183749333921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7235860654550911665778561 5426895490913183749333921)
        ·
          refine ⟨4070171618184887812000441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5426895490913183749333921 4070171618184887812000441)
          ·
            refine ⟨3052628713638665859000331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4070171618184887812000441 3052628713638665859000331)
            ·
              refine ⟨4578943070457998788500497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3052628713638665859000331 4578943070457998788500497)
              ·
                refine ⟨3434207302843499091375373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4578943070457998788500497 3434207302843499091375373)
                ·
                  refine ⟨1287827738566312159265765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3434207302843499091375373 1287827738566312159265765)
                  ·
                    refine ⟨241467700981183529862331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1287827738566312159265765 241467700981183529862331)
                    ·
                      rfl

theorem cell23_1410770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_1410770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410770 prefixEnd_1410770 := by exact prefixLift 1410770
  have htrace : WordTrace (prefixWord ++ tailWord_1410770) baseStart_1410770 baseEnd_1410770 := by
    simpa [prefixWord, tailWord_1410770, baseEnd_1410770] using wordTrace_append hprefix tailTrace_1410770
  have hstable : (prefixWord ++ tailWord_1410770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410770).length < 2 ^ (prefixWord ++ tailWord_1410770).sum := by decide
  have hdescent : baseEnd_1410770 < baseStart_1410770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410774 : List Nat := [5, 2, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_1410774 : Nat := 118140960795 + 1410774 * 2 ^ 59
def prefixEnd_1410774 : Nat := 4983230072969 + 3 ^ 40 * 1410774 * 2
def baseEnd_1410774 : Nat := 241468385622056191312325

theorem tailTrace_1410774 : CollatzResearch.WordTrace tailWord_1410774 prefixEnd_1410774 241468385622056191312325 := by
  unfold tailWord_1410774
  simp only [CollatzResearch.WordTrace]
  refine ⟨3215947186938388366375961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34303436660676142574676917 3215947186938388366375961)
  ·
    refine ⟨2411960390203791274781971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3215947186938388366375961 2411960390203791274781971)
    ·
      refine ⟨3617940585305686912172957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2411960390203791274781971 3617940585305686912172957)
      ·
        refine ⟨1356727719489632592064859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3617940585305686912172957 1356727719489632592064859)
        ·
          refine ⟨2035091579234448888097289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1356727719489632592064859 2035091579234448888097289)
          ·
            refine ⟨1526318684425836666072967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2035091579234448888097289 1526318684425836666072967)
            ·
              refine ⟨2289478026638754999109451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1526318684425836666072967 2289478026638754999109451)
              ·
                refine ⟨3434217039958132498664177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2289478026638754999109451 3434217039958132498664177)
                ·
                  refine ⟨2575662779968599373998133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3434217039958132498664177 2575662779968599373998133)
                  ·
                    refine ⟨241468385622056191312325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2575662779968599373998133 241468385622056191312325)
                    ·
                      rfl

theorem cell23_1410774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_1410774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410774 prefixEnd_1410774 := by exact prefixLift 1410774
  have htrace : WordTrace (prefixWord ++ tailWord_1410774) baseStart_1410774 baseEnd_1410774 := by
    simpa [prefixWord, tailWord_1410774, baseEnd_1410774] using wordTrace_append hprefix tailTrace_1410774
  have hstable : (prefixWord ++ tailWord_1410774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410774).length < 2 ^ (prefixWord ++ tailWord_1410774).sum := by decide
  have hdescent : baseEnd_1410774 < baseStart_1410774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410793 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 7, 1, 3]
def baseStart_1410793 : Nat := 118140960795 + 1410793 * 2 ^ 59
def prefixEnd_1410793 : Nat := 4983230072969 + 3 ^ 40 * 1410793 * 2
def baseEnd_1410793 : Nat := 724414912998603999599387

theorem tailTrace_1410793 : CollatzResearch.WordTrace tailWord_1410793 prefixEnd_1410793 724414912998603999599387 := by
  unfold tailWord_1410793
  simp only [CollatzResearch.WordTrace]
  refine ⟨51455847977945380106957033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34303898651963586737971355 51455847977945380106957033)
  ·
    refine ⟨38591885983459035080217775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51455847977945380106957033 38591885983459035080217775)
    ·
      refine ⟨57887828975188552620326663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38591885983459035080217775 57887828975188552620326663)
      ·
        refine ⟨86831743462782828930489995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57887828975188552620326663 86831743462782828930489995)
        ·
          refine ⟨130247615194174243395734993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86831743462782828930489995 130247615194174243395734993)
          ·
            refine ⟨97685711395630682546801245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130247615194174243395734993 97685711395630682546801245)
            ·
              refine ⟨36632141773361505955050467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97685711395630682546801245 36632141773361505955050467)
              ·
                refine ⟨54948212660042258932575701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36632141773361505955050467 54948212660042258932575701)
                ·
                  refine ⟨1287848734219740443732243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 54948212660042258932575701 1287848734219740443732243)
                  ·
                    refine ⟨1931773101329610665598365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1287848734219740443732243 1931773101329610665598365)
                    ·
                      refine ⟨724414912998603999599387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1931773101329610665598365 724414912998603999599387)
                      ·
                        rfl

theorem cell23_1410793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 1, 3].length) (baseStart_1410793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410793 prefixEnd_1410793 := by exact prefixLift 1410793
  have htrace : WordTrace (prefixWord ++ tailWord_1410793) baseStart_1410793 baseEnd_1410793 := by
    simpa [prefixWord, tailWord_1410793, baseEnd_1410793] using wordTrace_append hprefix tailTrace_1410793
  have hstable : (prefixWord ++ tailWord_1410793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410793).length < 2 ^ (prefixWord ++ tailWord_1410793).sum := by decide
  have hdescent : baseEnd_1410793 < baseStart_1410793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410804 : List Nat := [2, 6, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_1410804 : Nat := 118140960795 + 1410804 * 2 ^ 59
def prefixEnd_1410804 : Nat := 4983230072969 + 3 ^ 40 * 1410804 * 2
def baseEnd_1410804 : Nat := 241473520428601152187279

theorem tailTrace_1410804 : CollatzResearch.WordTrace tailWord_1410804 prefixEnd_1410804 241473520428601152187279 := by
  unfold tailWord_1410804
  simp only [CollatzResearch.WordTrace]
  refine ⟨25728124590452764492803733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34304166120603685990404977 25728124590452764492803733)
  ·
    refine ⟨1206005840177473335600175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25728124590452764492803733 1206005840177473335600175)
    ·
      refine ⟨1809008760266210003400263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1206005840177473335600175 1809008760266210003400263)
      ·
        refine ⟨2713513140399315005100395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1809008760266210003400263 2713513140399315005100395)
        ·
          refine ⟨4070269710598972507650593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2713513140399315005100395 4070269710598972507650593)
          ·
            refine ⟨3052702282949229380737945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4070269710598972507650593 3052702282949229380737945)
            ·
              refine ⟨2289526712211922035553459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3052702282949229380737945 2289526712211922035553459)
              ·
                refine ⟨3434290068317883053330189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2289526712211922035553459 3434290068317883053330189)
                ·
                  refine ⟨1287858775619206144998821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3434290068317883053330189 1287858775619206144998821)
                  ·
                    refine ⟨241473520428601152187279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1287858775619206144998821 241473520428601152187279)
                    ·
                      rfl

theorem cell23_1410804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_1410804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410804 prefixEnd_1410804 := by exact prefixLift 1410804
  have htrace : WordTrace (prefixWord ++ tailWord_1410804) baseStart_1410804 baseEnd_1410804 := by
    simpa [prefixWord, tailWord_1410804, baseEnd_1410804] using wordTrace_append hprefix tailTrace_1410804
  have hstable : (prefixWord ++ tailWord_1410804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410804).length < 2 ^ (prefixWord ++ tailWord_1410804).sum := by decide
  have hdescent : baseEnd_1410804 < baseStart_1410804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410820 : List Nat := [2, 3, 2, 2, 1, 2, 1, 2, 1, 5, 2]
def baseStart_1410820 : Nat := 118140960795 + 1410820 * 2 ^ 59
def prefixEnd_1410820 : Nat := 4983230072969 + 3 ^ 40 * 1410820 * 2
def baseEnd_1410820 : Nat := 724428776976275393961763

theorem tailTrace_1410820 : CollatzResearch.WordTrace tailWord_1410820 prefixEnd_1410820 724428776976275393961763 := by
  unfold tailWord_1410820
  simp only [CollatzResearch.WordTrace]
  refine ⟨25728416374423781859094957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34304555165898375812126609 25728416374423781859094957)
  ·
    refine ⟨9648156140408918197160609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25728416374423781859094957 9648156140408918197160609)
    ·
      refine ⟨7236117105306688647870457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9648156140408918197160609 7236117105306688647870457)
      ·
        refine ⟨5427087828980016485902843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7236117105306688647870457 5427087828980016485902843)
        ·
          refine ⟨8140631743470024728854265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5427087828980016485902843 8140631743470024728854265)
          ·
            refine ⟨6105473807602518546640699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8140631743470024728854265 6105473807602518546640699)
            ·
              refine ⟨9158210711403777819961049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6105473807602518546640699 9158210711403777819961049)
              ·
                refine ⟨6868658033552833364970787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9158210711403777819961049 6868658033552833364970787)
                ·
                  refine ⟨10302987050329250047456181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6868658033552833364970787 10302987050329250047456181)
                  ·
                    refine ⟨965905035968367191949017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10302987050329250047456181 965905035968367191949017)
                    ·
                      refine ⟨724428776976275393961763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 965905035968367191949017 724428776976275393961763)
                      ·
                        rfl

theorem cell23_1410820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_1410820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410820 prefixEnd_1410820 := by exact prefixLift 1410820
  have htrace : WordTrace (prefixWord ++ tailWord_1410820) baseStart_1410820 baseEnd_1410820 := by
    simpa [prefixWord, tailWord_1410820, baseEnd_1410820] using wordTrace_append hprefix tailTrace_1410820
  have hstable : (prefixWord ++ tailWord_1410820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410820).length < 2 ^ (prefixWord ++ tailWord_1410820).sum := by decide
  have hdescent : baseEnd_1410820 < baseStart_1410820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410833 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 1, 8, 2]
def baseStart_1410833 : Nat := 118140960795 + 1410833 * 2 ^ 59
def prefixEnd_1410833 : Nat := 4983230072969 + 3 ^ 40 * 1410833 * 2
def baseEnd_1410833 : Nat := 724435452224783843099203

theorem tailTrace_1410833 : CollatzResearch.WordTrace tailWord_1410833 prefixEnd_1410833 724435452224783843099203 := by
  unfold tailWord_1410833
  simp only [CollatzResearch.WordTrace]
  refine ⟨51457306897800466938413153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34304871265200311292275435 51457306897800466938413153)
  ·
    refine ⟨38592980173350350203809865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51457306897800466938413153 38592980173350350203809865)
    ·
      refine ⟨28944735130012762652857399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38592980173350350203809865 28944735130012762652857399)
      ·
        refine ⟨43417102695019143979286099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28944735130012762652857399 43417102695019143979286099)
        ·
          refine ⟨65125654042528715968929149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43417102695019143979286099 65125654042528715968929149)
          ·
            refine ⟨24422120265948268488348431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65125654042528715968929149 24422120265948268488348431)
            ·
              refine ⟨36633180398922402732522647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24422120265948268488348431 36633180398922402732522647)
              ·
                refine ⟨54949770598383604098783971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36633180398922402732522647 54949770598383604098783971)
                ·
                  refine ⟨82424655897575406148175957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54949770598383604098783971 82424655897575406148175957)
                  ·
                    refine ⟨965913936299711790798937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82424655897575406148175957 965913936299711790798937)
                    ·
                      refine ⟨724435452224783843099203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 965913936299711790798937 724435452224783843099203)
                      ·
                        rfl

theorem cell23_1410833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 8, 2].length) (baseStart_1410833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410833 prefixEnd_1410833 := by exact prefixLift 1410833
  have htrace : WordTrace (prefixWord ++ tailWord_1410833) baseStart_1410833 baseEnd_1410833 := by
    simpa [prefixWord, tailWord_1410833, baseEnd_1410833] using wordTrace_append hprefix tailTrace_1410833
  have hstable : (prefixWord ++ tailWord_1410833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410833).length < 2 ^ (prefixWord ++ tailWord_1410833).sum := by decide
  have hdescent : baseEnd_1410833 < baseStart_1410833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410850 : List Nat := [3, 3, 1, 1, 2, 1, 1, 5, 1, 1, 4]
def baseStart_1410850 : Nat := 118140960795 + 1410850 * 2 ^ 59
def prefixEnd_1410850 : Nat := 4983230072969 + 3 ^ 40 * 1410850 * 2
def baseEnd_1410850 : Nat := 724444181395910276586625

theorem tailTrace_1410850 : CollatzResearch.WordTrace tailWord_1410850 prefixEnd_1410850 724444181395910276586625 := by
  unfold tailWord_1410850
  simp only [CollatzResearch.WordTrace]
  refine ⟨12864481734684719710445501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34305284625825919227854669 12864481734684719710445501)
  ·
    refine ⟨4824180650506769891417063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12864481734684719710445501 4824180650506769891417063)
    ·
      refine ⟨7236270975760154837125595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4824180650506769891417063 7236270975760154837125595)
      ·
        refine ⟨10854406463640232255688393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7236270975760154837125595 10854406463640232255688393)
        ·
          refine ⟨8140804847730174191766295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10854406463640232255688393 8140804847730174191766295)
          ·
            refine ⟨12211207271595261287649443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8140804847730174191766295 12211207271595261287649443)
            ·
              refine ⟨18316810907392891931474165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12211207271595261287649443 18316810907392891931474165)
              ·
                refine ⟨1717201022568083618575703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18316810907392891931474165 1717201022568083618575703)
                ·
                  refine ⟨2575801533852125427863555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1717201022568083618575703 2575801533852125427863555)
                  ·
                    refine ⟨3863702300778188141795333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2575801533852125427863555 3863702300778188141795333)
                    ·
                      refine ⟨724444181395910276586625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3863702300778188141795333 724444181395910276586625)
                      ·
                        rfl

theorem cell23_1410850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_1410850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410850 prefixEnd_1410850 := by exact prefixLift 1410850
  have htrace : WordTrace (prefixWord ++ tailWord_1410850) baseStart_1410850 baseEnd_1410850 := by
    simpa [prefixWord, tailWord_1410850, baseEnd_1410850] using wordTrace_append hprefix tailTrace_1410850
  have hstable : (prefixWord ++ tailWord_1410850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410850).length < 2 ^ (prefixWord ++ tailWord_1410850).sum := by decide
  have hdescent : baseEnd_1410850 < baseStart_1410850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410853 : List Nat := [1, 3, 1, 2, 3, 2, 1, 3, 1, 1, 5]
def baseStart_1410853 : Nat := 118140960795 + 1410853 * 2 ^ 59
def prefixEnd_1410853 : Nat := 4983230072969 + 3 ^ 40 * 1410853 * 2
def baseEnd_1410853 : Nat := 724445721837873764849111

theorem tailTrace_1410853 : CollatzResearch.WordTrace tailWord_1410853 prefixEnd_1410853 724445721837873764849111 := by
  unfold tailWord_1410853
  simp only [CollatzResearch.WordTrace]
  refine ⟨51458036357728010354141213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34305357571818673569427475 51458036357728010354141213)
  ·
    refine ⟨19296763634148003882802955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51458036357728010354141213 19296763634148003882802955)
    ·
      refine ⟨28945145451222005824204433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19296763634148003882802955 28945145451222005824204433)
      ·
        refine ⟨21708859088416504368153325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28945145451222005824204433 21708859088416504368153325)
        ·
          refine ⟨8140822158156189138057497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21708859088416504368153325 8140822158156189138057497)
          ·
            refine ⟨6105616618617141853543123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8140822158156189138057497 6105616618617141853543123)
            ·
              refine ⟨9158424927925712780314685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6105616618617141853543123 9158424927925712780314685)
              ·
                refine ⟨3434409347972142292618007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9158424927925712780314685 3434409347972142292618007)
                ·
                  refine ⟨5151614021958213438927011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3434409347972142292618007 5151614021958213438927011)
                  ·
                    refine ⟨7727421032937320158390517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5151614021958213438927011 7727421032937320158390517)
                    ·
                      refine ⟨724445721837873764849111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7727421032937320158390517 724445721837873764849111)
                      ·
                        rfl

theorem cell23_1410853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_1410853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410853 prefixEnd_1410853 := by exact prefixLift 1410853
  have htrace : WordTrace (prefixWord ++ tailWord_1410853) baseStart_1410853 baseEnd_1410853 := by
    simpa [prefixWord, tailWord_1410853, baseEnd_1410853] using wordTrace_append hprefix tailTrace_1410853
  have hstable : (prefixWord ++ tailWord_1410853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410853).length < 2 ^ (prefixWord ++ tailWord_1410853).sum := by decide
  have hdescent : baseEnd_1410853 < baseStart_1410853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410877 : List Nat := [1, 4, 1, 4, 1, 2, 1, 3, 2, 4]
def baseStart_1410877 : Nat := 118140960795 + 1410877 * 2 ^ 59
def prefixEnd_1410877 : Nat := 4983230072969 + 3 ^ 40 * 1410877 * 2
def baseEnd_1410877 : Nat := 241486015124527223649667

theorem tailTrace_1410877 : CollatzResearch.WordTrace tailWord_1410877 prefixEnd_1410877 241486015124527223649667 := by
  unfold tailWord_1410877
  simp only [CollatzResearch.WordTrace]
  refine ⟨51458911709641062453014885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34305941139760708302009923 51458911709641062453014885)
  ·
    refine ⟨9648545945557699209940291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51458911709641062453014885 9648545945557699209940291)
    ·
      refine ⟨14472818918336548814910437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9648545945557699209940291 14472818918336548814910437)
      ·
        refine ⟨2713653547188102902795707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14472818918336548814910437 2713653547188102902795707)
        ·
          refine ⟨4070480320782154354193561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2713653547188102902795707 4070480320782154354193561)
          ·
            refine ⟨3052860240586615765645171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4070480320782154354193561 3052860240586615765645171)
            ·
              refine ⟨4579290360879923648467757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3052860240586615765645171 4579290360879923648467757)
              ·
                refine ⟨1717233885329971368175409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4579290360879923648467757 1717233885329971368175409)
                ·
                  refine ⟨1287925413997478526131557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1717233885329971368175409 1287925413997478526131557)
                  ·
                    refine ⟨241486015124527223649667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1287925413997478526131557 241486015124527223649667)
                    ·
                      rfl

theorem cell23_1410877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_1410877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410877 prefixEnd_1410877 := by exact prefixLift 1410877
  have htrace : WordTrace (prefixWord ++ tailWord_1410877) baseStart_1410877 baseEnd_1410877 := by
    simpa [prefixWord, tailWord_1410877, baseEnd_1410877] using wordTrace_append hprefix tailTrace_1410877
  have hstable : (prefixWord ++ tailWord_1410877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410877).length < 2 ^ (prefixWord ++ tailWord_1410877).sum := by decide
  have hdescent : baseEnd_1410877 < baseStart_1410877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410900 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 3, 3, 3]
def baseStart_1410900 : Nat := 118140960795 + 1410900 * 2 ^ 59
def prefixEnd_1410900 : Nat := 4983230072969 + 3 ^ 40 * 1410900 * 2
def baseEnd_1410900 : Nat := 724469855428635080961395

theorem tailTrace_1410900 : CollatzResearch.WordTrace tailWord_1410900 prefixEnd_1410900 724469855428635080961395 := by
  unfold tailWord_1410900
  simp only [CollatzResearch.WordTrace]
  refine ⟨25729875294278868690551077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34306500392371824920734769 25729875294278868690551077)
  ·
    refine ⟨4824351617677287879478327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25729875294278868690551077 4824351617677287879478327)
    ·
      refine ⟨7236527426515931819217491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4824351617677287879478327 7236527426515931819217491)
      ·
        refine ⟨10854791139773897728826237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7236527426515931819217491 10854791139773897728826237)
        ·
          refine ⟨4070546677415211648309839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10854791139773897728826237 4070546677415211648309839)
          ·
            refine ⟨6105820016122817472464759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4070546677415211648309839 6105820016122817472464759)
            ·
              refine ⟨9158730024184226208697139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6105820016122817472464759 9158730024184226208697139)
              ·
                refine ⟨13738095036276339313045709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9158730024184226208697139 13738095036276339313045709)
                ·
                  refine ⟨5151785638603627242392141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13738095036276339313045709 5151785638603627242392141)
                  ·
                    refine ⟨1931919614476360215897053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5151785638603627242392141 1931919614476360215897053)
                    ·
                      refine ⟨724469855428635080961395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1931919614476360215897053 724469855428635080961395)
                      ·
                        rfl

theorem cell23_1410900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_1410900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410900 prefixEnd_1410900 := by exact prefixLift 1410900
  have htrace : WordTrace (prefixWord ++ tailWord_1410900) baseStart_1410900 baseEnd_1410900 := by
    simpa [prefixWord, tailWord_1410900, baseEnd_1410900] using wordTrace_append hprefix tailTrace_1410900
  have hstable : (prefixWord ++ tailWord_1410900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410900).length < 2 ^ (prefixWord ++ tailWord_1410900).sum := by decide
  have hdescent : baseEnd_1410900 < baseStart_1410900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410934 : List Nat := [5, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3]
def baseStart_1410934 : Nat := 118140960795 + 1410934 * 2 ^ 59
def prefixEnd_1410934 : Nat := 4983230072969 + 3 ^ 40 * 1410934 * 2
def baseEnd_1410934 : Nat := 724487313770887947936239

theorem tailTrace_1410934 : CollatzResearch.WordTrace tailWord_1410934 prefixEnd_1410934 724487313770887947936239 := by
  unfold tailWord_1410934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3216311916902160074239991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34307327113623040791893237 3216311916902160074239991)
  ·
    refine ⟨4824467875353240111359987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3216311916902160074239991 4824467875353240111359987)
    ·
      refine ⟨7236701813029860167039981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4824467875353240111359987 7236701813029860167039981)
      ·
        refine ⟨2713763179886197562639993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7236701813029860167039981 2713763179886197562639993)
        ·
          refine ⟨2035322384914648171979995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2713763179886197562639993 2035322384914648171979995)
          ·
            refine ⟨3052983577371972257969993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2035322384914648171979995 3052983577371972257969993)
            ·
              refine ⟨2289737683028979193477495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3052983577371972257969993 2289737683028979193477495)
              ·
                refine ⟨3434606524543468790216243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2289737683028979193477495 3434606524543468790216243)
                ·
                  refine ⟨5151909786815203185324365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3434606524543468790216243 5151909786815203185324365)
                  ·
                    refine ⟨1931966170055701194496637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5151909786815203185324365 1931966170055701194496637)
                    ·
                      refine ⟨724487313770887947936239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1931966170055701194496637 724487313770887947936239)
                      ·
                        rfl

theorem cell23_1410934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_1410934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410934 prefixEnd_1410934 := by exact prefixLift 1410934
  have htrace : WordTrace (prefixWord ++ tailWord_1410934) baseStart_1410934 baseEnd_1410934 := by
    simpa [prefixWord, tailWord_1410934, baseEnd_1410934] using wordTrace_append hprefix tailTrace_1410934
  have hstable : (prefixWord ++ tailWord_1410934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410934).length < 2 ^ (prefixWord ++ tailWord_1410934).sum := by decide
  have hdescent : baseEnd_1410934 < baseStart_1410934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410943 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 3]
def baseStart_1410943 : Nat := 118140960795 + 1410943 * 2 ^ 59
def prefixEnd_1410943 : Nat := 4983230072969 + 3 ^ 40 * 1410943 * 2
def baseEnd_1410943 : Nat := 724491935096778412723697

theorem tailTrace_1410943 : CollatzResearch.WordTrace tailWord_1410943 prefixEnd_1410943 724491935096778412723697 := by
  unfold tailWord_1410943
  simp only [CollatzResearch.WordTrace]
  refine ⟨51461318927401955724917483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34307545951601303816611655 51461318927401955724917483)
  ·
    refine ⟨77191978391102933587376225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51461318927401955724917483 77191978391102933587376225)
    ·
      refine ⟨57893983793327200190532169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77191978391102933587376225 57893983793327200190532169)
      ·
        refine ⟨43420487844995400142899127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57893983793327200190532169 43420487844995400142899127)
        ·
          refine ⟨65130731767493100214348691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43420487844995400142899127 65130731767493100214348691)
          ·
            refine ⟨97696097651239650321523037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65130731767493100214348691 97696097651239650321523037)
            ·
              refine ⟨36636036619214868870571139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97696097651239650321523037 36636036619214868870571139)
              ·
                refine ⟨54954054928822303305856709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36636036619214868870571139 54954054928822303305856709)
                ·
                  refine ⟨10303885299154181869848133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54954054928822303305856709 10303885299154181869848133)
                  ·
                    refine ⟨1931978493591409100596525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10303885299154181869848133 1931978493591409100596525)
                    ·
                      refine ⟨724491935096778412723697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1931978493591409100596525 724491935096778412723697)
                      ·
                        rfl

theorem cell23_1410943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 3].length) (baseStart_1410943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410943 prefixEnd_1410943 := by exact prefixLift 1410943
  have htrace : WordTrace (prefixWord ++ tailWord_1410943) baseStart_1410943 baseEnd_1410943 := by
    simpa [prefixWord, tailWord_1410943, baseEnd_1410943] using wordTrace_append hprefix tailTrace_1410943
  have hstable : (prefixWord ++ tailWord_1410943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410943).length < 2 ^ (prefixWord ++ tailWord_1410943).sum := by decide
  have hdescent : baseEnd_1410943 < baseStart_1410943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410953 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 1, 4, 4]
def baseStart_1410953 : Nat := 118140960795 + 1410953 * 2 ^ 59
def prefixEnd_1410953 : Nat := 4983230072969 + 3 ^ 40 * 1410953 * 2
def baseEnd_1410953 : Nat := 724497069903323373598651

theorem tailTrace_1410953 : CollatzResearch.WordTrace tailWord_1410953 prefixEnd_1410953 724497069903323373598651 := by
  unfold tailWord_1410953
  simp only [CollatzResearch.WordTrace]
  refine ⟨51461683657365727432781513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34307789104910484955187675 51461683657365727432781513)
  ·
    refine ⟨38596262743024295574586135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51461683657365727432781513 38596262743024295574586135)
    ·
      refine ⟨57894394114536443361879203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38596262743024295574586135 57894394114536443361879203)
      ·
        refine ⟨86841591171804665042818805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57894394114536443361879203 86841591171804665042818805)
        ·
          refine ⟨8141399172356687347764263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86841591171804665042818805 8141399172356687347764263)
          ·
            refine ⟨12212098758535031021646395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8141399172356687347764263 12212098758535031021646395)
            ·
              refine ⟨18318148137802546532469593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12212098758535031021646395 18318148137802546532469593)
              ·
                refine ⟨13738611103351909899352195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18318148137802546532469593 13738611103351909899352195)
                ·
                  refine ⟨20607916655027864849028293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13738611103351909899352195 20607916655027864849028293)
                  ·
                    refine ⟨3863984372817724659192805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20607916655027864849028293 3863984372817724659192805)
                    ·
                      refine ⟨724497069903323373598651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3863984372817724659192805 724497069903323373598651)
                      ·
                        rfl

theorem cell23_1410953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 4, 4].length) (baseStart_1410953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410953 prefixEnd_1410953 := by exact prefixLift 1410953
  have htrace : WordTrace (prefixWord ++ tailWord_1410953) baseStart_1410953 baseEnd_1410953 := by
    simpa [prefixWord, tailWord_1410953, baseEnd_1410953] using wordTrace_append hprefix tailTrace_1410953
  have hstable : (prefixWord ++ tailWord_1410953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410953).length < 2 ^ (prefixWord ++ tailWord_1410953).sum := by decide
  have hdescent : baseEnd_1410953 < baseStart_1410953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410968 : List Nat := [2, 1, 2, 6, 2, 1, 1, 2, 2, 1, 3]
def baseStart_1410968 : Nat := 118140960795 + 1410968 * 2 ^ 59
def prefixEnd_1410968 : Nat := 4983230072969 + 3 ^ 40 * 1410968 * 2
def baseEnd_1410968 : Nat := 724504772113140814911083

theorem tailTrace_1410968 : CollatzResearch.WordTrace tailWord_1410968 prefixEnd_1410968 724504772113140814911083 := by
  unfold tailWord_1410968
  simp only [CollatzResearch.WordTrace]
  refine ⟨25731115376155692497288779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34308153834874256663051705 25731115376155692497288779)
  ·
    refine ⟨38596673064233538745933169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25731115376155692497288779 38596673064233538745933169)
    ·
      refine ⟨28947504798175154059449877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38596673064233538745933169 28947504798175154059449877)
      ·
        refine ⟨1356914287414460346536713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28947504798175154059449877 1356914287414460346536713)
        ·
          refine ⟨1017685715560845259902535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1356914287414460346536713 1017685715560845259902535)
          ·
            refine ⟨1526528573341267889853803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1017685715560845259902535 1526528573341267889853803)
            ·
              refine ⟨2289792860011901834780705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1526528573341267889853803 2289792860011901834780705)
              ·
                refine ⟨1717344645008926376085529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2289792860011901834780705 1717344645008926376085529)
                ·
                  refine ⟨1288008483756694782064147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1717344645008926376085529 1288008483756694782064147)
                  ·
                    refine ⟨1932012725635042173096221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1288008483756694782064147 1932012725635042173096221)
                    ·
                      refine ⟨724504772113140814911083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1932012725635042173096221 724504772113140814911083)
                      ·
                        rfl

theorem cell23_1410968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_1410968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410968 prefixEnd_1410968 := by exact prefixLift 1410968
  have htrace : WordTrace (prefixWord ++ tailWord_1410968) baseStart_1410968 baseEnd_1410968 := by
    simpa [prefixWord, tailWord_1410968, baseEnd_1410968] using wordTrace_append hprefix tailTrace_1410968
  have hstable : (prefixWord ++ tailWord_1410968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410968).length < 2 ^ (prefixWord ++ tailWord_1410968).sum := by decide
  have hdescent : baseEnd_1410968 < baseStart_1410968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410970 : List Nat := [3, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4]
def baseStart_1410970 : Nat := 118140960795 + 1410970 * 2 ^ 59
def prefixEnd_1410970 : Nat := 4983230072969 + 3 ^ 40 * 1410970 * 2
def baseEnd_1410970 : Nat := 724505799074449807086073

theorem tailTrace_1410970 : CollatzResearch.WordTrace tailWord_1410970 prefixEnd_1410970 724505799074449807086073 := by
  unfold tailWord_1410970
  simp only [CollatzResearch.WordTrace]
  refine ⟨12865575924576034834037591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34308202465536092890766909 12865575924576034834037591)
  ·
    refine ⟨19298363886864052251056387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12865575924576034834037591 19298363886864052251056387)
    ·
      refine ⟨28947545830296078376584581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19298363886864052251056387 28947545830296078376584581)
      ·
        refine ⟨5427664843180514695609609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28947545830296078376584581 5427664843180514695609609)
        ·
          refine ⟨4070748632385386021707207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5427664843180514695609609 4070748632385386021707207)
          ·
            refine ⟨6106122948578079032560811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4070748632385386021707207 6106122948578079032560811)
            ·
              refine ⟨9159184422867118548841217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6106122948578079032560811 9159184422867118548841217)
              ·
                refine ⟨6869388317150338911630913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9159184422867118548841217 6869388317150338911630913)
                ·
                  refine ⟨5152041237862754183723185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6869388317150338911630913 5152041237862754183723185)
                  ·
                    refine ⟨3864030928397065637792389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5152041237862754183723185 3864030928397065637792389)
                    ·
                      refine ⟨724505799074449807086073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3864030928397065637792389 724505799074449807086073)
                      ·
                        rfl

theorem cell23_1410970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_1410970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410970 prefixEnd_1410970 := by exact prefixLift 1410970
  have htrace : WordTrace (prefixWord ++ tailWord_1410970) baseStart_1410970 baseEnd_1410970 := by
    simpa [prefixWord, tailWord_1410970, baseEnd_1410970] using wordTrace_append hprefix tailTrace_1410970
  have hstable : (prefixWord ++ tailWord_1410970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410970).length < 2 ^ (prefixWord ++ tailWord_1410970).sum := by decide
  have hdescent : baseEnd_1410970 < baseStart_1410970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410980 : List Nat := [2, 3, 1, 2, 1, 4, 2, 1, 7]
def baseStart_1410980 : Nat := 118140960795 + 1410980 * 2 ^ 59
def prefixEnd_1410980 : Nat := 4983230072969 + 3 ^ 40 * 1410980 * 2
def baseEnd_1410980 : Nat := 80501214875666085329003

theorem tailTrace_1410980 : CollatzResearch.WordTrace tailWord_1410980 prefixEnd_1410980 80501214875666085329003 := by
  unfold tailWord_1410980
  simp only [CollatzResearch.WordTrace]
  refine ⟨25731334214133955522007197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34308445618845274029342929 25731334214133955522007197)
  ·
    refine ⟨9649250330300233320752699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25731334214133955522007197 9649250330300233320752699)
    ·
      refine ⟨14473875495450349981129049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9649250330300233320752699 14473875495450349981129049)
      ·
        refine ⟨10855406621587762485846787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14473875495450349981129049 10855406621587762485846787)
        ·
          refine ⟨16283109932381643728770181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10855406621587762485846787 16283109932381643728770181)
          ·
            refine ⟨3053083112321558199144409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16283109932381643728770181 3053083112321558199144409)
            ·
              refine ⟨2289812334241168649358307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3053083112321558199144409 2289812334241168649358307)
              ·
                refine ⟨3434718501361752974037461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2289812334241168649358307 3434718501361752974037461)
                ·
                  refine ⟨80501214875666085329003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3434718501361752974037461 80501214875666085329003)
                  ·
                    rfl

theorem cell23_1410980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_1410980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1410980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1410980 prefixEnd_1410980 := by exact prefixLift 1410980
  have htrace : WordTrace (prefixWord ++ tailWord_1410980) baseStart_1410980 baseEnd_1410980 := by
    simpa [prefixWord, tailWord_1410980, baseEnd_1410980] using wordTrace_append hprefix tailTrace_1410980
  have hstable : (prefixWord ++ tailWord_1410980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410980).length < 2 ^ (prefixWord ++ tailWord_1410980).sum := by decide
  have hdescent : baseEnd_1410980 < baseStart_1410980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411037 : List Nat := [1, 4, 3, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_1411037 : Nat := 118140960795 + 1411037 * 2 ^ 59
def prefixEnd_1411037 : Nat := 4983230072969 + 3 ^ 40 * 1411037 * 2
def baseEnd_1411037 : Nat := 724540202278301044948265

theorem tailTrace_1411037 : CollatzResearch.WordTrace tailWord_1411037 prefixEnd_1411037 724540202278301044948265 := by
  unfold tailWord_1411037
  simp only [CollatzResearch.WordTrace]
  refine ⟨51464747389061409778839365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34309831592707606519226243 51464747389061409778839365)
  ·
    refine ⟨9649640135449014333532381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51464747389061409778839365 9649640135449014333532381)
    ·
      refine ⟨3618615050793380375074643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9649640135449014333532381 3618615050793380375074643)
      ·
        refine ⟨5427922576190070562611965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3618615050793380375074643 5427922576190070562611965)
        ·
          refine ⟨2035470966071276460979487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5427922576190070562611965 2035470966071276460979487)
          ·
            refine ⟨3053206449106914691469231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2035470966071276460979487 3053206449106914691469231)
            ·
              refine ⟨4579809673660372037203847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3053206449106914691469231 4579809673660372037203847)
              ·
                refine ⟨6869714510490558055805771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4579809673660372037203847 6869714510490558055805771)
                ·
                  refine ⟨10304571765735837083708657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6869714510490558055805771 10304571765735837083708657)
                  ·
                    refine ⟨7728428824301877812781493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10304571765735837083708657 7728428824301877812781493)
                    ·
                      refine ⟨724540202278301044948265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7728428824301877812781493 724540202278301044948265)
                      ·
                        rfl

theorem cell23_1411037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_1411037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411037 prefixEnd_1411037 := by exact prefixLift 1411037
  have htrace : WordTrace (prefixWord ++ tailWord_1411037) baseStart_1411037 baseEnd_1411037 := by
    simpa [prefixWord, tailWord_1411037, baseEnd_1411037] using wordTrace_append hprefix tailTrace_1411037
  have hstable : (prefixWord ++ tailWord_1411037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411037).length < 2 ^ (prefixWord ++ tailWord_1411037).sum := by decide
  have hdescent : baseEnd_1411037 < baseStart_1411037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411042 : List Nat := [3, 3, 3, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_1411042 : Nat := 118140960795 + 1411042 * 2 ^ 59
def prefixEnd_1411042 : Nat := 4983230072969 + 3 ^ 40 * 1411042 * 2
def baseEnd_1411042 : Nat := 724542769681573525385743

theorem tailTrace_1411042 : CollatzResearch.WordTrace tailWord_1411042 prefixEnd_1411042 724542769681573525385743 := by
  unfold tailWord_1411042
  simp only [CollatzResearch.WordTrace]
  refine ⟨12866232438510823908192845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34309953169362197088514253 12866232438510823908192845)
  ·
    refine ⟨4824837164441558965572317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12866232438510823908192845 4824837164441558965572317)
    ·
      refine ⟨1809313936665584612089619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4824837164441558965572317 1809313936665584612089619)
      ·
        refine ⟨2713970904998376918134429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1809313936665584612089619 2713970904998376918134429)
        ·
          refine ⟨1017739089374391344300411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2713970904998376918134429 1017739089374391344300411)
          ·
            refine ⟨1526608634061587016450617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1017739089374391344300411 1526608634061587016450617)
            ·
              refine ⟨1144956475546190262337963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1526608634061587016450617 1144956475546190262337963)
              ·
                refine ⟨1717434713319285393506945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1144956475546190262337963 1717434713319285393506945)
                ·
                  refine ⟨1288076034989464045130209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1717434713319285393506945 1288076034989464045130209)
                  ·
                    refine ⟨966057026242098033847657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1288076034989464045130209 966057026242098033847657)
                    ·
                      refine ⟨724542769681573525385743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 966057026242098033847657 724542769681573525385743)
                      ·
                        rfl

theorem cell23_1411042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_1411042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411042 prefixEnd_1411042 := by exact prefixLift 1411042
  have htrace : WordTrace (prefixWord ++ tailWord_1411042) baseStart_1411042 baseEnd_1411042 := by
    simpa [prefixWord, tailWord_1411042, baseEnd_1411042] using wordTrace_append hprefix tailTrace_1411042
  have hstable : (prefixWord ++ tailWord_1411042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411042).length < 2 ^ (prefixWord ++ tailWord_1411042).sum := by decide
  have hdescent : baseEnd_1411042 < baseStart_1411042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411097 : List Nat := [1, 2, 1, 2, 1, 1, 3, 5, 3, 1, 3]
def baseStart_1411097 : Nat := 118140960795 + 1411097 * 2 ^ 59
def prefixEnd_1411097 : Nat := 4983230072969 + 3 ^ 40 * 1411097 * 2
def baseEnd_1411097 : Nat := 724571011117570810197989

theorem tailTrace_1411097 : CollatzResearch.WordTrace tailWord_1411097 prefixEnd_1411097 724571011117570810197989 := by
  unfold tailWord_1411097
  simp only [CollatzResearch.WordTrace]
  refine ⟨51466935768844040026023545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34311290512562693350682363 51466935768844040026023545)
  ·
    refine ⟨38600201826633030019517659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51466935768844040026023545 38600201826633030019517659)
    ·
      refine ⟨57900302739949545029276489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38600201826633030019517659 57900302739949545029276489)
      ·
        refine ⟨43425227054962158771957367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57900302739949545029276489 43425227054962158771957367)
        ·
          refine ⟨65137840582443238157936051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43425227054962158771957367 65137840582443238157936051)
          ·
            refine ⟨97706760873664857236904077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65137840582443238157936051 97706760873664857236904077)
            ·
              refine ⟨36640035327624321463839029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97706760873664857236904077 36640035327624321463839029)
              ·
                refine ⟨3435003311964780137234909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36640035327624321463839029 3435003311964780137234909)
                ·
                  refine ⟨1288126241986792551463091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3435003311964780137234909 1288126241986792551463091)
                  ·
                    refine ⟨1932189362980188827194637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1288126241986792551463091 1932189362980188827194637)
                    ·
                      refine ⟨724571011117570810197989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1932189362980188827194637 724571011117570810197989)
                      ·
                        rfl

theorem cell23_1411097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 1, 3].length) (baseStart_1411097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411097 prefixEnd_1411097 := by exact prefixLift 1411097
  have htrace : WordTrace (prefixWord ++ tailWord_1411097) baseStart_1411097 baseEnd_1411097 := by
    simpa [prefixWord, tailWord_1411097, baseEnd_1411097] using wordTrace_append hprefix tailTrace_1411097
  have hstable : (prefixWord ++ tailWord_1411097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411097).length < 2 ^ (prefixWord ++ tailWord_1411097).sum := by decide
  have hdescent : baseEnd_1411097 < baseStart_1411097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411107 : List Nat := [1, 1, 1, 4, 3, 1, 2, 2, 1, 5, 2]
def baseStart_1411107 : Nat := 118140960795 + 1411107 * 2 ^ 59
def prefixEnd_1411107 : Nat := 4983230072969 + 3 ^ 40 * 1411107 * 2
def baseEnd_1411107 : Nat := 724576145924115771072943

theorem tailTrace_1411107 : CollatzResearch.WordTrace tailWord_1411107 prefixEnd_1411107 724576145924115771072943 := by
  unfold tailWord_1411107
  simp only [CollatzResearch.WordTrace]
  refine ⟨51467300498807811733887575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34311533665871874489258383 51467300498807811733887575)
  ·
    refine ⟨77200950748211717600831363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51467300498807811733887575 77200950748211717600831363)
    ·
      refine ⟨115801426122317576401247045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77200950748211717600831363 115801426122317576401247045)
      ·
        refine ⟨21712767397934545575233821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115801426122317576401247045 21712767397934545575233821)
        ·
          refine ⟨8142287774225454590712683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21712767397934545575233821 8142287774225454590712683)
          ·
            refine ⟨12213431661338181886069025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8142287774225454590712683 12213431661338181886069025)
            ·
              refine ⟨9160073746003636414551769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12213431661338181886069025 9160073746003636414551769)
              ·
                refine ⟨6870055309502727310913827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9160073746003636414551769 6870055309502727310913827)
                ·
                  refine ⟨10305082964254090966370741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6870055309502727310913827 10305082964254090966370741)
                  ·
                    refine ⟨966101527898821028097257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10305082964254090966370741 966101527898821028097257)
                    ·
                      refine ⟨724576145924115771072943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 966101527898821028097257 724576145924115771072943)
                      ·
                        rfl

theorem cell23_1411107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 5, 2].length) (baseStart_1411107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411107 prefixEnd_1411107 := by exact prefixLift 1411107
  have htrace : WordTrace (prefixWord ++ tailWord_1411107) baseStart_1411107 baseEnd_1411107 := by
    simpa [prefixWord, tailWord_1411107, baseEnd_1411107] using wordTrace_append hprefix tailTrace_1411107
  have hstable : (prefixWord ++ tailWord_1411107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411107).length < 2 ^ (prefixWord ++ tailWord_1411107).sum := by decide
  have hdescent : baseEnd_1411107 < baseStart_1411107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411114 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_1411114 : Nat := 118140960795 + 1411114 * 2 ^ 59
def prefixEnd_1411114 : Nat := 4983230072969 + 3 ^ 40 * 1411114 * 2
def baseEnd_1411114 : Nat := 724579740288697243685411

theorem tailTrace_1411114 : CollatzResearch.WordTrace tailWord_1411114 prefixEnd_1411114 724579740288697243685411 := by
  unfold tailWord_1411114
  simp only [CollatzResearch.WordTrace]
  refine ⟨12866888952445612982348099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34311703873188301286261597 12866888952445612982348099)
  ·
    refine ⟨19300333428668419473522149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12866888952445612982348099 19300333428668419473522149)
    ·
      refine ⟨3618812517875328651285403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19300333428668419473522149 3618812517875328651285403)
      ·
        refine ⟨5428218776812992976928105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3618812517875328651285403 5428218776812992976928105)
        ·
          refine ⟨4071164082609744732696079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5428218776812992976928105 4071164082609744732696079)
          ·
            refine ⟨6106746123914617099044119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4071164082609744732696079 6106746123914617099044119)
            ·
              refine ⟨9160119185871925648566179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6106746123914617099044119 9160119185871925648566179)
              ·
                refine ⟨13740178778807888472849269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9160119185871925648566179 13740178778807888472849269)
                ·
                  refine ⟨1288141760513239544329619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13740178778807888472849269 1288141760513239544329619)
                  ·
                    refine ⟨1932212640769859316494429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1288141760513239544329619 1932212640769859316494429)
                    ·
                      refine ⟨724579740288697243685411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1932212640769859316494429 724579740288697243685411)
                      ·
                        rfl

theorem cell23_1411114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_1411114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411114 prefixEnd_1411114 := by exact prefixLift 1411114
  have htrace : WordTrace (prefixWord ++ tailWord_1411114) baseStart_1411114 baseEnd_1411114 := by
    simpa [prefixWord, tailWord_1411114, baseEnd_1411114] using wordTrace_append hprefix tailTrace_1411114
  have hstable : (prefixWord ++ tailWord_1411114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411114).length < 2 ^ (prefixWord ++ tailWord_1411114).sum := by decide
  have hdescent : baseEnd_1411114 < baseStart_1411114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411157 : List Nat := [1, 3, 2, 2, 1, 4, 1, 2, 1, 1, 5]
def baseStart_1411157 : Nat := 118140960795 + 1411157 * 2 ^ 59
def prefixEnd_1411157 : Nat := 4983230072969 + 3 ^ 40 * 1411157 * 2
def baseEnd_1411157 : Nat := 724601819956840575447713

theorem tailTrace_1411157 : CollatzResearch.WordTrace tailWord_1411157 prefixEnd_1411157 724601819956840575447713 := by
  unfold tailWord_1411157
  simp only [CollatzResearch.WordTrace]
  refine ⟨51469124148626670273207725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34312749432417780182138483 51469124148626670273207725)
  ·
    refine ⟨19300921555735001352452897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51469124148626670273207725 19300921555735001352452897)
    ·
      refine ⟨14475691166801251014339673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19300921555735001352452897 14475691166801251014339673)
      ·
        refine ⟨10856768375100938260754755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14475691166801251014339673 10856768375100938260754755)
        ·
          refine ⟨16285152562651407391132133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10856768375100938260754755 16285152562651407391132133)
          ·
            refine ⟨3053466105497138885837275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16285152562651407391132133 3053466105497138885837275)
            ·
              refine ⟨4580199158245708328755913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3053466105497138885837275 4580199158245708328755913)
              ·
                refine ⟨3435149368684281246566935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4580199158245708328755913 3435149368684281246566935)
                ·
                  refine ⟨5152724053026421869850403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3435149368684281246566935 5152724053026421869850403)
                  ·
                    refine ⟨7729086079539632804775605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5152724053026421869850403 7729086079539632804775605)
                    ·
                      refine ⟨724601819956840575447713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7729086079539632804775605 724601819956840575447713)
                      ·
                        rfl

theorem cell23_1411157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_1411157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411157 prefixEnd_1411157 := by exact prefixLift 1411157
  have htrace : WordTrace (prefixWord ++ tailWord_1411157) baseStart_1411157 baseEnd_1411157 := by
    simpa [prefixWord, tailWord_1411157, baseEnd_1411157] using wordTrace_append hprefix tailTrace_1411157
  have hstable : (prefixWord ++ tailWord_1411157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411157).length < 2 ^ (prefixWord ++ tailWord_1411157).sum := by decide
  have hdescent : baseEnd_1411157 < baseStart_1411157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411164 : List Nat := [2, 2, 4, 1, 1, 4, 1, 1, 1, 6]
def baseStart_1411164 : Nat := 118140960795 + 1411164 * 2 ^ 59
def prefixEnd_1411164 : Nat := 4983230072969 + 3 ^ 40 * 1411164 * 2
def baseEnd_1411164 : Nat := 241535138107140682686727

theorem tailTrace_1411164 : CollatzResearch.WordTrace tailWord_1411164 prefixEnd_1411164 241535138107140682686727 := by
  unfold tailWord_1411164
  simp only [CollatzResearch.WordTrace]
  refine ⟨25734689729800655234356273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34312919639734206979141697 25734689729800655234356273)
  ·
    refine ⟨19301017297350491425767205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25734689729800655234356273 19301017297350491425767205)
    ·
      refine ⟨3618940743253217142331351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19301017297350491425767205 3618940743253217142331351)
      ·
        refine ⟨5428411114879825713497027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3618940743253217142331351 5428411114879825713497027)
        ·
          refine ⟨8142616672319738570245541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5428411114879825713497027 8142616672319738570245541)
          ·
            refine ⟨1526740626059950981921039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8142616672319738570245541 1526740626059950981921039)
            ·
              refine ⟨2290110939089926472881559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1526740626059950981921039 2290110939089926472881559)
              ·
                refine ⟨3435166408634889709322339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2290110939089926472881559 3435166408634889709322339)
                ·
                  refine ⟨5152749612952334563983509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3435166408634889709322339 5152749612952334563983509)
                  ·
                    refine ⟨241535138107140682686727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5152749612952334563983509 241535138107140682686727)
                    ·
                      rfl

theorem cell23_1411164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_1411164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411164 prefixEnd_1411164 := by exact prefixLift 1411164
  have htrace : WordTrace (prefixWord ++ tailWord_1411164) baseStart_1411164 baseEnd_1411164 := by
    simpa [prefixWord, tailWord_1411164, baseEnd_1411164] using wordTrace_append hprefix tailTrace_1411164
  have hstable : (prefixWord ++ tailWord_1411164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411164).length < 2 ^ (prefixWord ++ tailWord_1411164).sum := by decide
  have hdescent : baseEnd_1411164 < baseStart_1411164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411200 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 5]
def baseStart_1411200 : Nat := 118140960795 + 1411200 * 2 ^ 59
def prefixEnd_1411200 : Nat := 4983230072969 + 3 ^ 40 * 1411200 * 2
def baseEnd_1411200 : Nat := 724623899624983907210015

theorem tailTrace_1411200 : CollatzResearch.WordTrace tailWord_1411200 prefixEnd_1411200 724623899624983907210015 := by
  unfold tailWord_1411200
  simp only [CollatzResearch.WordTrace]
  refine ⟨25735346243735444308511527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34313794991647259078015369 25735346243735444308511527)
  ·
    refine ⟨38603019365603166462767291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25735346243735444308511527 38603019365603166462767291)
    ·
      refine ⟨57904529048404749694150937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38603019365603166462767291 57904529048404749694150937)
      ·
        refine ⟨43428396786303562270613203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57904529048404749694150937 43428396786303562270613203)
        ·
          refine ⟨65142595179455343405919805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43428396786303562270613203 65142595179455343405919805)
          ·
            refine ⟨24428473192295753777219927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65142595179455343405919805 24428473192295753777219927)
            ·
              refine ⟨36642709788443630665829891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24428473192295753777219927 36642709788443630665829891)
              ·
                refine ⟨54964064682665445998744837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36642709788443630665829891 54964064682665445998744837)
                ·
                  refine ⟨10305762127999771124764657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54964064682665445998744837 10305762127999771124764657)
                  ·
                    refine ⟨7729321595999828343573493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10305762127999771124764657 7729321595999828343573493)
                    ·
                      refine ⟨724623899624983907210015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7729321595999828343573493 724623899624983907210015)
                      ·
                        rfl

theorem cell23_1411200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_1411200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411200 prefixEnd_1411200 := by exact prefixLift 1411200
  have htrace : WordTrace (prefixWord ++ tailWord_1411200) baseStart_1411200 baseEnd_1411200 := by
    simpa [prefixWord, tailWord_1411200, baseEnd_1411200] using wordTrace_append hprefix tailTrace_1411200
  have hstable : (prefixWord ++ tailWord_1411200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411200).length < 2 ^ (prefixWord ++ tailWord_1411200).sum := by decide
  have hdescent : baseEnd_1411200 < baseStart_1411200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411204 : List Nat := [2, 3, 2, 1, 2, 1, 1, 3, 4, 1, 3]
def baseStart_1411204 : Nat := 118140960795 + 1411204 * 2 ^ 59
def prefixEnd_1411204 : Nat := 4983230072969 + 3 ^ 40 * 1411204 * 2
def baseEnd_1411204 : Nat := 724625953547601891559997

theorem tailTrace_1411204 : CollatzResearch.WordTrace tailWord_1411204 prefixEnd_1411204 724625953547601891559997 := by
  unfold tailWord_1411204
  simp only [CollatzResearch.WordTrace]
  refine ⟨25735419189728198650084333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34313892252970931533445777 25735419189728198650084333)
  ·
    refine ⟨9650782196148074493781625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25735419189728198650084333 9650782196148074493781625)
    ·
      refine ⟨7238086647111055870336219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9650782196148074493781625 7238086647111055870336219)
      ·
        refine ⟨10857129970666583805504329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7238086647111055870336219 10857129970666583805504329)
        ·
          refine ⟨8142847477999937854128247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10857129970666583805504329 8142847477999937854128247)
          ·
            refine ⟨12214271216999906781192371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8142847477999937854128247 12214271216999906781192371)
            ·
              refine ⟨18321406825499860171788557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12214271216999906781192371 18321406825499860171788557)
              ·
                refine ⟨6870527559562447564420709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18321406825499860171788557 6870527559562447564420709)
                ·
                  refine ⟨1288223917417958918328883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6870527559562447564420709 1288223917417958918328883)
                  ·
                    refine ⟨1932335876126938377493325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1288223917417958918328883 1932335876126938377493325)
                    ·
                      refine ⟨724625953547601891559997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1932335876126938377493325 724625953547601891559997)
                      ·
                        rfl

theorem cell23_1411204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_1411204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411204 prefixEnd_1411204 := by exact prefixLift 1411204
  have htrace : WordTrace (prefixWord ++ tailWord_1411204) baseStart_1411204 baseEnd_1411204 := by
    simpa [prefixWord, tailWord_1411204, baseEnd_1411204] using wordTrace_append hprefix tailTrace_1411204
  have hstable : (prefixWord ++ tailWord_1411204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411204).length < 2 ^ (prefixWord ++ tailWord_1411204).sum := by decide
  have hdescent : baseEnd_1411204 < baseStart_1411204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411205 : List Nat := [1, 3, 1, 1, 5, 2, 3, 2, 1, 2, 2]
def baseStart_1411205 : Nat := 118140960795 + 1411205 * 2 ^ 59
def prefixEnd_1411205 : Nat := 4983230072969 + 3 ^ 40 * 1411205 * 2
def baseEnd_1411205 : Nat := 724626467028256387647493

theorem tailTrace_1411205 : CollatzResearch.WordTrace tailWord_1411205 prefixEnd_1411205 724626467028256387647493 := by
  unfold tailWord_1411205
  simp only [CollatzResearch.WordTrace]
  refine ⟨51470874852452774470955069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34313916568301849647303379 51470874852452774470955069)
  ·
    refine ⟨19301578069669790426608151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51470874852452774470955069 19301578069669790426608151)
    ·
      refine ⟨28952367104504685639912227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19301578069669790426608151 28952367104504685639912227)
      ·
        refine ⟨43428550656757028459868341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28952367104504685639912227 43428550656757028459868341)
        ·
          refine ⟨4071426624070971418112657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43428550656757028459868341 4071426624070971418112657)
          ·
            refine ⟨3053569968053228563584493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4071426624070971418112657 3053569968053228563584493)
            ·
              refine ⟨1145088738019960711344185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3053569968053228563584493 1145088738019960711344185)
              ·
                refine ⟨858816553514970533508139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1145088738019960711344185 858816553514970533508139)
                ·
                  refine ⟨1288224830272455800262209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 858816553514970533508139 1288224830272455800262209)
                  ·
                    refine ⟨966168622704341850196657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1288224830272455800262209 966168622704341850196657)
                    ·
                      refine ⟨724626467028256387647493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 966168622704341850196657 724626467028256387647493)
                      ·
                        rfl

theorem cell23_1411205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 1, 2, 2].length) (baseStart_1411205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411205 prefixEnd_1411205 := by exact prefixLift 1411205
  have htrace : WordTrace (prefixWord ++ tailWord_1411205) baseStart_1411205 baseEnd_1411205 := by
    simpa [prefixWord, tailWord_1411205, baseEnd_1411205] using wordTrace_append hprefix tailTrace_1411205
  have hstable : (prefixWord ++ tailWord_1411205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411205).length < 2 ^ (prefixWord ++ tailWord_1411205).sum := by decide
  have hdescent : baseEnd_1411205 < baseStart_1411205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411231 : List Nat := [1, 1, 2, 6, 1, 2, 1, 1, 3, 3, 2]
def baseStart_1411231 : Nat := 118140960795 + 1411231 * 2 ^ 59
def prefixEnd_1411231 : Nat := 4983230072969 + 3 ^ 40 * 1411231 * 2
def baseEnd_1411231 : Nat := 724639817525273285922373

theorem tailTrace_1411231 : CollatzResearch.WordTrace tailWord_1411231 prefixEnd_1411231 724639817525273285922373 := by
  unfold tailWord_1411231
  simp only [CollatzResearch.WordTrace]
  refine ⟨51471823150358580911401547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34314548766905720607601031 51471823150358580911401547)
  ·
    refine ⟨77207734725537871367102321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51471823150358580911401547 77207734725537871367102321)
    ·
      refine ⟨57905801044153403525326741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77207734725537871367102321 57905801044153403525326741)
      ·
        refine ⟨2714334423944690790249691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 57905801044153403525326741 2714334423944690790249691)
        ·
          refine ⟨4071501635917036185374537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2714334423944690790249691 4071501635917036185374537)
          ·
            refine ⟨3053626226937777139030903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4071501635917036185374537 3053626226937777139030903)
            ·
              refine ⟨4580439340406665708546355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3053626226937777139030903 4580439340406665708546355)
              ·
                refine ⟨6870659010609998562819533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4580439340406665708546355 6870659010609998562819533)
                ·
                  refine ⟨2576497128978749461057325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6870659010609998562819533 2576497128978749461057325)
                  ·
                    refine ⟨966186423367031047896497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2576497128978749461057325 966186423367031047896497)
                    ·
                      refine ⟨724639817525273285922373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 966186423367031047896497 724639817525273285922373)
                      ·
                        rfl

theorem cell23_1411231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_1411231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411231 prefixEnd_1411231 := by exact prefixLift 1411231
  have htrace : WordTrace (prefixWord ++ tailWord_1411231) baseStart_1411231 baseEnd_1411231 := by
    simpa [prefixWord, tailWord_1411231, baseEnd_1411231] using wordTrace_append hprefix tailTrace_1411231
  have hstable : (prefixWord ++ tailWord_1411231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411231).length < 2 ^ (prefixWord ++ tailWord_1411231).sum := by decide
  have hdescent : baseEnd_1411231 < baseStart_1411231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411257 : List Nat := [1, 2, 1, 4, 1, 2, 2, 2, 2, 2, 4]
def baseStart_1411257 : Nat := 118140960795 + 1411257 * 2 ^ 59
def prefixEnd_1411257 : Nat := 4983230072969 + 3 ^ 40 * 1411257 * 2
def baseEnd_1411257 : Nat := 724653168022290184197253

theorem tailTrace_1411257 : CollatzResearch.WordTrace tailWord_1411257 prefixEnd_1411257 724653168022290184197253 := by
  unfold tailWord_1411257
  simp only [CollatzResearch.WordTrace]
  refine ⟨51472771448264387351848025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34315180965509591567898683 51472771448264387351848025)
  ·
    refine ⟨38604578586198290513886019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51472771448264387351848025 38604578586198290513886019)
    ·
      refine ⟨57906867879297435770829029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38604578586198290513886019 57906867879297435770829029)
      ·
        refine ⟨10857537727368269207030443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57906867879297435770829029 10857537727368269207030443)
        ·
          refine ⟨16286306591052403810545665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10857537727368269207030443 16286306591052403810545665)
          ·
            refine ⟨12214729943289302857909249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16286306591052403810545665 12214729943289302857909249)
            ·
              refine ⟨9161047457466977143431937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12214729943289302857909249 9161047457466977143431937)
              ·
                refine ⟨6870785593100232857573953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9161047457466977143431937 6870785593100232857573953)
                ·
                  refine ⟨5153089194825174643180465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6870785593100232857573953 5153089194825174643180465)
                  ·
                    refine ⟨3864816896118880982385349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5153089194825174643180465 3864816896118880982385349)
                    ·
                      refine ⟨724653168022290184197253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3864816896118880982385349 724653168022290184197253)
                      ·
                        rfl

theorem cell23_1411257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_1411257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411257 prefixEnd_1411257 := by exact prefixLift 1411257
  have htrace : WordTrace (prefixWord ++ tailWord_1411257) baseStart_1411257 baseEnd_1411257 := by
    simpa [prefixWord, tailWord_1411257, baseEnd_1411257] using wordTrace_append hprefix tailTrace_1411257
  have hstable : (prefixWord ++ tailWord_1411257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411257).length < 2 ^ (prefixWord ++ tailWord_1411257).sum := by decide
  have hdescent : baseEnd_1411257 < baseStart_1411257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411278 : List Nat := [4, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2]
def baseStart_1411278 : Nat := 118140960795 + 1411278 * 2 ^ 59
def prefixEnd_1411278 : Nat := 4983230072969 + 3 ^ 40 * 1411278 * 2
def baseEnd_1411278 : Nat := 724663951116034602034657

theorem tailTrace_1411278 : CollatzResearch.WordTrace tailWord_1411278 prefixEnd_1411278 724663951116034602034657 := by
  unfold tailWord_1411278
  simp only [CollatzResearch.WordTrace]
  refine ⟨6434192172648538492295311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34315691587458871958908325 6434192172648538492295311)
  ·
    refine ⟨9651288258972807738442967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6434192172648538492295311 9651288258972807738442967)
    ·
      refine ⟨14476932388459211607664451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9651288258972807738442967 14476932388459211607664451)
      ·
        refine ⟨21715398582688817411496677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14476932388459211607664451 21715398582688817411496677)
        ·
          refine ⟨4071637234254153264655627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21715398582688817411496677 4071637234254153264655627)
          ·
            refine ⟨6107455851381229896983441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4071637234254153264655627 6107455851381229896983441)
            ·
              refine ⟨4580591888535922422737581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6107455851381229896983441 4580591888535922422737581)
              ·
                refine ⟨1717721958200970908526593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4580591888535922422737581 1717721958200970908526593)
                ·
                  refine ⟨1288291468650728181394945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1717721958200970908526593 1288291468650728181394945)
                  ·
                    refine ⟨966218601488046136046209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1288291468650728181394945 966218601488046136046209)
                    ·
                      refine ⟨724663951116034602034657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 966218601488046136046209 724663951116034602034657)
                      ·
                        rfl

theorem cell23_1411278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2].length) (baseStart_1411278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411278 prefixEnd_1411278 := by exact prefixLift 1411278
  have htrace : WordTrace (prefixWord ++ tailWord_1411278) baseStart_1411278 baseEnd_1411278 := by
    simpa [prefixWord, tailWord_1411278, baseEnd_1411278] using wordTrace_append hprefix tailTrace_1411278
  have hstable : (prefixWord ++ tailWord_1411278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411278).length < 2 ^ (prefixWord ++ tailWord_1411278).sum := by decide
  have hdescent : baseEnd_1411278 < baseStart_1411278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411297 : List Nat := [1, 2, 3, 1, 3, 1, 3, 1, 1, 7]
def baseStart_1411297 : Nat := 118140960795 + 1411297 * 2 ^ 59
def prefixEnd_1411297 : Nat := 4983230072969 + 3 ^ 40 * 1411297 * 2
def baseEnd_1411297 : Nat := 241557902416156675899023

theorem tailTrace_1411297 : CollatzResearch.WordTrace tailWord_1411297 prefixEnd_1411297 241557902416156675899023 := by
  unfold tailWord_1411297
  simp only [CollatzResearch.WordTrace]
  refine ⟨51474230368119474183304145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34316153578746316122202763 51474230368119474183304145)
  ·
    refine ⟨38605672776089605637478109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51474230368119474183304145 38605672776089605637478109)
    ·
      refine ⟨14477127291033602114054291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38605672776089605637478109 14477127291033602114054291)
      ·
        refine ⟨21715690936550403171081437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14477127291033602114054291 21715690936550403171081437)
        ·
          refine ⟨8143384101206401189155539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21715690936550403171081437 8143384101206401189155539)
          ·
            refine ⟨12215076151809601783733309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8143384101206401189155539 12215076151809601783733309)
            ·
              refine ⟨4580653556928600668899991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12215076151809601783733309 4580653556928600668899991)
              ·
                refine ⟨6870980335392901003349987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4580653556928600668899991 6870980335392901003349987)
                ·
                  refine ⟨10306470503089351505024981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6870980335392901003349987 10306470503089351505024981)
                  ·
                    refine ⟨241557902416156675899023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10306470503089351505024981 241557902416156675899023)
                    ·
                      rfl

theorem cell23_1411297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_1411297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411297 prefixEnd_1411297 := by exact prefixLift 1411297
  have htrace : WordTrace (prefixWord ++ tailWord_1411297) baseStart_1411297 baseEnd_1411297 := by
    simpa [prefixWord, tailWord_1411297, baseEnd_1411297] using wordTrace_append hprefix tailTrace_1411297
  have hstable : (prefixWord ++ tailWord_1411297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411297).length < 2 ^ (prefixWord ++ tailWord_1411297).sum := by decide
  have hdescent : baseEnd_1411297 < baseStart_1411297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411301 : List Nat := [1, 3, 1, 4, 2, 2, 2, 3, 5]
def baseStart_1411301 : Nat := 118140960795 + 1411301 * 2 ^ 59
def prefixEnd_1411301 : Nat := 4983230072969 + 3 ^ 40 * 1411301 * 2
def baseEnd_1411301 : Nat := 80519529019009779116339

theorem tailTrace_1411301 : CollatzResearch.WordTrace tailWord_1411301 prefixEnd_1411301 80519529019009779116339 := by
  unfold tailWord_1411301
  simp only [CollatzResearch.WordTrace]
  refine ⟨51474376260104982866449757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34316250840069988577633171 51474376260104982866449757)
  ·
    refine ⟨19302891097539368574918659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51474376260104982866449757 19302891097539368574918659)
    ·
      refine ⟨28954336646309052862377989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19302891097539368574918659 28954336646309052862377989)
      ·
        refine ⟨5428938121182947411695873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28954336646309052862377989 5428938121182947411695873)
        ·
          refine ⟨4071703590887210558771905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5428938121182947411695873 4071703590887210558771905)
          ·
            refine ⟨3053777693165407919078929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4071703590887210558771905 3053777693165407919078929)
            ·
              refine ⟨2290333269874055939309197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3053777693165407919078929 2290333269874055939309197)
              ·
                refine ⟨858874976202770977240949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2290333269874055939309197 858874976202770977240949)
                ·
                  refine ⟨80519529019009779116339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 858874976202770977240949 80519529019009779116339)
                  ·
                    rfl

theorem cell23_1411301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 5].length) (baseStart_1411301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411301 prefixEnd_1411301 := by exact prefixLift 1411301
  have htrace : WordTrace (prefixWord ++ tailWord_1411301) baseStart_1411301 baseEnd_1411301 := by
    simpa [prefixWord, tailWord_1411301, baseEnd_1411301] using wordTrace_append hprefix tailTrace_1411301
  have hstable : (prefixWord ++ tailWord_1411301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411301).length < 2 ^ (prefixWord ++ tailWord_1411301).sum := by decide
  have hdescent : baseEnd_1411301 < baseStart_1411301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411378 : List Nat := [3, 2, 1, 1, 5, 2, 1, 1, 3, 4]
def baseStart_1411378 : Nat := 118140960795 + 1411378 * 2 ^ 59
def prefixEnd_1411378 : Nat := 4983230072969 + 3 ^ 40 * 1411378 * 2
def baseEnd_1411378 : Nat := 241571766393828070261399

theorem tailTrace_1411378 : CollatzResearch.WordTrace tailWord_1411378 prefixEnd_1411378 241571766393828070261399 := by
  unfold tailWord_1411378
  simp only [CollatzResearch.WordTrace]
  refine ⟨12869296170206506254250697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34318123120550683344668525 12869296170206506254250697)
  ·
    refine ⟨9651972127654879690688023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12869296170206506254250697 9651972127654879690688023)
    ·
      refine ⟨14477958191482319536032035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9651972127654879690688023 14477958191482319536032035)
      ·
        refine ⟨21716937287223479304048053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14477958191482319536032035 21716937287223479304048053)
        ·
          refine ⟨2035962870677201184754505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21716937287223479304048053 2035962870677201184754505)
          ·
            refine ⟨1526972153007900888565879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2035962870677201184754505 1526972153007900888565879)
            ·
              refine ⟨2290458229511851332848819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1526972153007900888565879 2290458229511851332848819)
              ·
                refine ⟨3435687344267776999273229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2290458229511851332848819 3435687344267776999273229)
                ·
                  refine ⟨1288382754100416374727461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3435687344267776999273229 1288382754100416374727461)
                  ·
                    refine ⟨241571766393828070261399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1288382754100416374727461 241571766393828070261399)
                    ·
                      rfl

theorem cell23_1411378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_1411378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411378 prefixEnd_1411378 := by exact prefixLift 1411378
  have htrace : WordTrace (prefixWord ++ tailWord_1411378) baseStart_1411378 baseEnd_1411378 := by
    simpa [prefixWord, tailWord_1411378, baseEnd_1411378] using wordTrace_append hprefix tailTrace_1411378
  have hstable : (prefixWord ++ tailWord_1411378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411378).length < 2 ^ (prefixWord ++ tailWord_1411378).sum := by decide
  have hdescent : baseEnd_1411378 < baseStart_1411378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411404 : List Nat := [2, 2, 1, 3, 2, 1, 3, 1, 3, 5]
def baseStart_1411404 : Nat := 118140960795 + 1411404 * 2 ^ 59
def prefixEnd_1411404 : Nat := 4983230072969 + 3 ^ 40 * 1411404 * 2
def baseEnd_1411404 : Nat := 241576216559500369686359

theorem tailTrace_1411404 : CollatzResearch.WordTrace tailWord_1411404 prefixEnd_1411404 241576216559500369686359 := by
  unfold tailWord_1411404
  simp only [CollatzResearch.WordTrace]
  refine ⟨25739066489365915728724633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34318755319154554304966177 25739066489365915728724633)
  ·
    refine ⟨19304299867024436796543475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25739066489365915728724633 19304299867024436796543475)
    ·
      refine ⟨28956449800536655194815213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19304299867024436796543475 28956449800536655194815213)
      ·
        refine ⟨10858668675201245698055705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28956449800536655194815213 10858668675201245698055705)
        ·
          refine ⟨8144001506400934273541779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10858668675201245698055705 8144001506400934273541779)
          ·
            refine ⟨12216002259601401410312669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8144001506400934273541779 12216002259601401410312669)
            ·
              refine ⟨4581000847350525528867251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12216002259601401410312669 4581000847350525528867251)
              ·
                refine ⟨6871501271025788293300877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4581000847350525528867251 6871501271025788293300877)
                ·
                  refine ⟨2576812976634670609987829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6871501271025788293300877 2576812976634670609987829)
                  ·
                    refine ⟨241576216559500369686359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2576812976634670609987829 241576216559500369686359)
                    ·
                      rfl

theorem cell23_1411404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 3, 5].length) (baseStart_1411404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411404 prefixEnd_1411404 := by exact prefixLift 1411404
  have htrace : WordTrace (prefixWord ++ tailWord_1411404) baseStart_1411404 baseEnd_1411404 := by
    simpa [prefixWord, tailWord_1411404, baseEnd_1411404] using wordTrace_append hprefix tailTrace_1411404
  have hstable : (prefixWord ++ tailWord_1411404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411404).length < 2 ^ (prefixWord ++ tailWord_1411404).sum := by decide
  have hdescent : baseEnd_1411404 < baseStart_1411404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411418 : List Nat := [3, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3]
def baseStart_1411418 : Nat := 118140960795 + 1411418 * 2 ^ 59
def prefixEnd_1411418 : Nat := 4983230072969 + 3 ^ 40 * 1411418 * 2
def baseEnd_1411418 : Nat := 724735838407664054284013

theorem tailTrace_1411418 : CollatzResearch.WordTrace tailWord_1411418 prefixEnd_1411418 724735838407664054284013 := by
  unfold tailWord_1411418
  simp only [CollatzResearch.WordTrace]
  refine ⟨12869660900170277962114727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34319095733787407898972605 12869660900170277962114727)
  ·
    refine ⟨19304491350255416943172091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12869660900170277962114727 19304491350255416943172091)
    ·
      refine ⟨28956737025383125414758137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19304491350255416943172091 28956737025383125414758137)
      ·
        refine ⟨21717552769037344061068603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28956737025383125414758137 21717552769037344061068603)
        ·
          refine ⟨32576329153556016091602905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21717552769037344061068603 32576329153556016091602905)
          ·
            refine ⟨24432246865167012068702179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32576329153556016091602905 24432246865167012068702179)
            ·
              refine ⟨36648370297750518103053269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24432246865167012068702179 36648370297750518103053269)
              ·
                refine ⟨858946178853527768040311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 36648370297750518103053269 858946178853527768040311)
                ·
                  refine ⟨1288419268280291652060467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 858946178853527768040311 1288419268280291652060467)
                  ·
                    refine ⟨1932628902420437478090701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1288419268280291652060467 1932628902420437478090701)
                    ·
                      refine ⟨724735838407664054284013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1932628902420437478090701 724735838407664054284013)
                      ·
                        rfl

theorem cell23_1411418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3].length) (baseStart_1411418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411418 prefixEnd_1411418 := by exact prefixLift 1411418
  have htrace : WordTrace (prefixWord ++ tailWord_1411418) baseStart_1411418 baseEnd_1411418 := by
    simpa [prefixWord, tailWord_1411418, baseEnd_1411418] using wordTrace_append hprefix tailTrace_1411418
  have hstable : (prefixWord ++ tailWord_1411418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411418).length < 2 ^ (prefixWord ++ tailWord_1411418).sum := by decide
  have hdescent : baseEnd_1411418 < baseStart_1411418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411447 : List Nat := [1, 1, 3, 1, 1, 2, 2, 12]
def baseStart_1411447 : Nat := 118140960795 + 1411447 * 2 ^ 59
def prefixEnd_1411447 : Nat := 4983230072969 + 3 ^ 40 * 1411447 * 2
def baseEnd_1411447 : Nat := 26842619605431275585977

theorem tailTrace_1411447 : CollatzResearch.WordTrace tailWord_1411447 prefixEnd_1411447 26842619605431275585977 := by
  unfold tailWord_1411447
  simp only [CollatzResearch.WordTrace]
  refine ⟨51479701317576049801264595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34319800878384033200843063 51479701317576049801264595)
  ·
    refine ⟨77219551976364074701896893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51479701317576049801264595 77219551976364074701896893)
    ·
      refine ⟨28957331991136528013211335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77219551976364074701896893 28957331991136528013211335)
      ·
        refine ⟨43435997986704792019817003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28957331991136528013211335 43435997986704792019817003)
        ·
          refine ⟨65153996980057188029725505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43435997986704792019817003 65153996980057188029725505)
          ·
            refine ⟨48865497735042891022294129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65153996980057188029725505 48865497735042891022294129)
            ·
              refine ⟨36649123301282168266720597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48865497735042891022294129 36649123301282168266720597)
              ·
                refine ⟨26842619605431275585977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 36649123301282168266720597 26842619605431275585977)
                ·
                  rfl

theorem cell23_1411447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 12].length) (baseStart_1411447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411447 prefixEnd_1411447 := by exact prefixLift 1411447
  have htrace : WordTrace (prefixWord ++ tailWord_1411447) baseStart_1411447 baseEnd_1411447 := by
    simpa [prefixWord, tailWord_1411447, baseEnd_1411447] using wordTrace_append hprefix tailTrace_1411447
  have hstable : (prefixWord ++ tailWord_1411447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411447).length < 2 ^ (prefixWord ++ tailWord_1411447).sum := by decide
  have hdescent : baseEnd_1411447 < baseStart_1411447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411451 : List Nat := [1, 1, 1, 1, 1, 7, 2, 3, 2, 4]
def baseStart_1411451 : Nat := 118140960795 + 1411451 * 2 ^ 59
def prefixEnd_1411451 : Nat := 4983230072969 + 3 ^ 40 * 1411451 * 2
def baseEnd_1411451 : Nat := 241584261089754141723787

theorem tailTrace_1411451 : CollatzResearch.WordTrace tailWord_1411451 prefixEnd_1411451 241584261089754141723787 := by
  unfold tailWord_1411451
  simp only [CollatzResearch.WordTrace]
  refine ⟨51479847209561558484410207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34319898139707705656273471 51479847209561558484410207)
  ·
    refine ⟨77219770814342337726615311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51479847209561558484410207 77219770814342337726615311)
    ·
      refine ⟨115829656221513506589922967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77219770814342337726615311 115829656221513506589922967)
      ·
        refine ⟨173744484332270259884884451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115829656221513506589922967 173744484332270259884884451)
        ·
          refine ⟨260616726498405389827326677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173744484332270259884884451 260616726498405389827326677)
          ·
            refine ⟨6108204527306376324077969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 260616726498405389827326677 6108204527306376324077969)
            ·
              refine ⟨4581153395479782243058477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6108204527306376324077969 4581153395479782243058477)
              ·
                refine ⟨1717932523304918341146929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4581153395479782243058477 1717932523304918341146929)
                ·
                  refine ⟨1288449392478688755860197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1717932523304918341146929 1288449392478688755860197)
                  ·
                    refine ⟨241584261089754141723787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1288449392478688755860197 241584261089754141723787)
                    ·
                      rfl

theorem cell23_1411451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 4].length) (baseStart_1411451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411451 prefixEnd_1411451 := by exact prefixLift 1411451
  have htrace : WordTrace (prefixWord ++ tailWord_1411451) baseStart_1411451 baseEnd_1411451 := by
    simpa [prefixWord, tailWord_1411451, baseEnd_1411451] using wordTrace_append hprefix tailTrace_1411451
  have hstable : (prefixWord ++ tailWord_1411451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411451).length < 2 ^ (prefixWord ++ tailWord_1411451).sum := by decide
  have hdescent : baseEnd_1411451 < baseStart_1411451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411461 : List Nat := [1, 3, 1, 1, 3, 1, 1, 6, 1, 2, 3]
def baseStart_1411461 : Nat := 118140960795 + 1411461 * 2 ^ 59
def prefixEnd_1411461 : Nat := 4983230072969 + 3 ^ 40 * 1411461 * 2
def baseEnd_1411461 : Nat := 724757918075807386046315

theorem tailTrace_1411461 : CollatzResearch.WordTrace tailWord_1411461 prefixEnd_1411461 724757918075807386046315 := by
  unfold tailWord_1411461
  simp only [CollatzResearch.WordTrace]
  refine ⟨51480211939525330192274237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34320141293016886794849491 51480211939525330192274237)
  ·
    refine ⟨19305079477321998822102839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51480211939525330192274237 19305079477321998822102839)
    ·
      refine ⟨28957619215982998233154259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19305079477321998822102839 28957619215982998233154259)
      ·
        refine ⟨43436428823974497349731389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28957619215982998233154259 43436428823974497349731389)
        ·
          refine ⟨16288660808990436506149271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43436428823974497349731389 16288660808990436506149271)
          ·
            refine ⟨24432991213485654759223907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16288660808990436506149271 24432991213485654759223907)
            ·
              refine ⟨36649486820228482138835861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24432991213485654759223907 36649486820228482138835861)
              ·
                refine ⟨1717944694698210100257931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36649486820228482138835861 1717944694698210100257931)
                ·
                  refine ⟨2576917042047315150386897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1717944694698210100257931 2576917042047315150386897)
                  ·
                    refine ⟨1932687781535486362790173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2576917042047315150386897 1932687781535486362790173)
                    ·
                      refine ⟨724757918075807386046315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1932687781535486362790173 724757918075807386046315)
                      ·
                        rfl

theorem cell23_1411461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 2, 3].length) (baseStart_1411461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411461 prefixEnd_1411461 := by exact prefixLift 1411461
  have htrace : WordTrace (prefixWord ++ tailWord_1411461) baseStart_1411461 baseEnd_1411461 := by
    simpa [prefixWord, tailWord_1411461, baseEnd_1411461] using wordTrace_append hprefix tailTrace_1411461
  have hstable : (prefixWord ++ tailWord_1411461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411461).length < 2 ^ (prefixWord ++ tailWord_1411461).sum := by decide
  have hdescent : baseEnd_1411461 < baseStart_1411461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411485 : List Nat := [1, 4, 2, 1, 4, 2, 1, 2, 2, 4]
def baseStart_1411485 : Nat := 118140960795 + 1411485 * 2 ^ 59
def prefixEnd_1411485 : Nat := 4983230072969 + 3 ^ 40 * 1411485 * 2
def baseEnd_1411485 : Nat := 241590080537171764048735

theorem tailTrace_1411485 : CollatzResearch.WordTrace tailWord_1411485 prefixEnd_1411485 241590080537171764048735 := by
  unfold tailWord_1411485
  simp only [CollatzResearch.WordTrace]
  refine ⟨51481087291438382291147909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34320724860958921527431939 51481087291438382291147909)
  ·
    refine ⟨9652703867144696679590233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51481087291438382291147909 9652703867144696679590233)
    ·
      refine ⟨7239527900358522509692675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9652703867144696679590233 7239527900358522509692675)
      ·
        refine ⟨10859291850537783764539013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7239527900358522509692675 10859291850537783764539013)
        ·
          refine ⟨2036117221975834455851065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10859291850537783764539013 2036117221975834455851065)
          ·
            refine ⟨1527087916481875841888299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2036117221975834455851065 1527087916481875841888299)
            ·
              refine ⟨2290631874722813762832449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1527087916481875841888299 2290631874722813762832449)
              ·
                refine ⟨1717973906042110322124337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2290631874722813762832449 1717973906042110322124337)
                ·
                  refine ⟨1288480429531582741593253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1717973906042110322124337 1288480429531582741593253)
                  ·
                    refine ⟨241590080537171764048735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1288480429531582741593253 241590080537171764048735)
                    ·
                      rfl

theorem cell23_1411485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_1411485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411485 prefixEnd_1411485 := by exact prefixLift 1411485
  have htrace : WordTrace (prefixWord ++ tailWord_1411485) baseStart_1411485 baseEnd_1411485 := by
    simpa [prefixWord, tailWord_1411485, baseEnd_1411485] using wordTrace_append hprefix tailTrace_1411485
  have hstable : (prefixWord ++ tailWord_1411485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411485).length < 2 ^ (prefixWord ++ tailWord_1411485).sum := by decide
  have hdescent : baseEnd_1411485 < baseStart_1411485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411514 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4]
def baseStart_1411514 : Nat := 118140960795 + 1411514 * 2 ^ 59
def prefixEnd_1411514 : Nat := 4983230072969 + 3 ^ 40 * 1411514 * 2
def baseEnd_1411514 : Nat := 724785132550495678683571

theorem tailTrace_1411514 : CollatzResearch.WordTrace tailWord_1411514 prefixEnd_1411514 724785132550495678683571 := by
  unfold tailWord_1411514
  simp only [CollatzResearch.WordTrace]
  refine ⟨12870536252083330060988399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34321430005555546829302397 12870536252083330060988399)
  ·
    refine ⟨19305804378124995091482599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12870536252083330060988399 19305804378124995091482599)
    ·
      refine ⟨28958706567187492637223899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19305804378124995091482599 28958706567187492637223899)
      ·
        refine ⟨43438059850781238955835849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28958706567187492637223899 43438059850781238955835849)
        ·
          refine ⟨32578544888085929216876887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43438059850781238955835849 32578544888085929216876887)
          ·
            refine ⟨48867817332128893825315331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32578544888085929216876887 48867817332128893825315331)
            ·
              refine ⟨73301725998193340737972997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48867817332128893825315331 73301725998193340737972997)
              ·
                refine ⟨13744073624661251388369937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73301725998193340737972997 13744073624661251388369937)
                ·
                  refine ⟨10308055218495938541277453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13744073624661251388369937 10308055218495938541277453)
                  ·
                    refine ⟨3865520706935976952979045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10308055218495938541277453 3865520706935976952979045)
                    ·
                      refine ⟨724785132550495678683571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3865520706935976952979045 724785132550495678683571)
                      ·
                        rfl

theorem cell23_1411514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_1411514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411514 prefixEnd_1411514 := by exact prefixLift 1411514
  have htrace : WordTrace (prefixWord ++ tailWord_1411514) baseStart_1411514 baseEnd_1411514 := by
    simpa [prefixWord, tailWord_1411514, baseEnd_1411514] using wordTrace_append hprefix tailTrace_1411514
  have hstable : (prefixWord ++ tailWord_1411514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411514).length < 2 ^ (prefixWord ++ tailWord_1411514).sum := by decide
  have hdescent : baseEnd_1411514 < baseStart_1411514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411518 : List Nat := [4, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2]
def baseStart_1411518 : Nat := 118140960795 + 1411518 * 2 ^ 59
def prefixEnd_1411518 : Nat := 4983230072969 + 3 ^ 40 * 1411518 * 2
def baseEnd_1411518 : Nat := 724787186473113663033553

theorem tailTrace_1411518 : CollatzResearch.WordTrace tailWord_1411518 prefixEnd_1411518 724787186473113663033553 := by
  unfold tailWord_1411518
  simp only [CollatzResearch.WordTrace]
  refine ⟨6435286362539853615887401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34321527266879219284732805 6435286362539853615887401)
  ·
    refine ⟨4826464771904890211915551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6435286362539853615887401 4826464771904890211915551)
    ·
      refine ⟨7239697157857335317873327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4826464771904890211915551 7239697157857335317873327)
      ·
        refine ⟨10859545736786002976809991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7239697157857335317873327 10859545736786002976809991)
        ·
          refine ⟨16289318605179004465214987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10859545736786002976809991 16289318605179004465214987)
          ·
            refine ⟨24433977907768506697822481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16289318605179004465214987 24433977907768506697822481)
            ·
              refine ⟨18325483430826380023366861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24433977907768506697822481 18325483430826380023366861)
              ·
                refine ⟨6872056286559892508762573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18325483430826380023366861 6872056286559892508762573)
                ·
                  refine ⟨2577021107459959690785965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6872056286559892508762573 2577021107459959690785965)
                  ·
                    refine ⟨966382915297484884044737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2577021107459959690785965 966382915297484884044737)
                    ·
                      refine ⟨724787186473113663033553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 966382915297484884044737 724787186473113663033553)
                      ·
                        rfl

theorem cell23_1411518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_1411518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411518 prefixEnd_1411518 := by exact prefixLift 1411518
  have htrace : WordTrace (prefixWord ++ tailWord_1411518) baseStart_1411518 baseEnd_1411518 := by
    simpa [prefixWord, tailWord_1411518, baseEnd_1411518] using wordTrace_append hprefix tailTrace_1411518
  have hstable : (prefixWord ++ tailWord_1411518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411518).length < 2 ^ (prefixWord ++ tailWord_1411518).sum := by decide
  have hdescent : baseEnd_1411518 < baseStart_1411518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411531 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 3, 4, 2]
def baseStart_1411531 : Nat := 118140960795 + 1411531 * 2 ^ 59
def prefixEnd_1411531 : Nat := 4983230072969 + 3 ^ 40 * 1411531 * 2
def baseEnd_1411531 : Nat := 724793861721622112170993

theorem tailTrace_1411531 : CollatzResearch.WordTrace tailWord_1411531 prefixEnd_1411531 724793861721622112170993 := by
  unfold tailWord_1411531
  simp only [CollatzResearch.WordTrace]
  refine ⟨51482765049271732147322447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34321843366181154764881631 51482765049271732147322447)
  ·
    refine ⟨77224147573907598220983671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51482765049271732147322447 77224147573907598220983671)
    ·
      refine ⟨115836221360861397331475507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77224147573907598220983671 115836221360861397331475507)
      ·
        refine ⟨173754332041292095997213261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115836221360861397331475507 173754332041292095997213261)
        ·
          refine ⟨65157874515484535998954973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173754332041292095997213261 65157874515484535998954973)
          ·
            refine ⟨24434202943306700999608115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65157874515484535998954973 24434202943306700999608115)
            ·
              refine ⟨36651304414960051499412173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24434202943306700999608115 36651304414960051499412173)
              ·
                refine ⟨13744239155610019312279565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36651304414960051499412173 13744239155610019312279565)
                ·
                  refine ⟨5154089683353757242104837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13744239155610019312279565 5154089683353757242104837)
                  ·
                    refine ⟨966391815628829482894657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5154089683353757242104837 966391815628829482894657)
                    ·
                      refine ⟨724793861721622112170993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 966391815628829482894657 724793861721622112170993)
                      ·
                        rfl

theorem cell23_1411531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 4, 2].length) (baseStart_1411531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411531 prefixEnd_1411531 := by exact prefixLift 1411531
  have htrace : WordTrace (prefixWord ++ tailWord_1411531) baseStart_1411531 baseEnd_1411531 := by
    simpa [prefixWord, tailWord_1411531, baseEnd_1411531] using wordTrace_append hprefix tailTrace_1411531
  have hstable : (prefixWord ++ tailWord_1411531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411531).length < 2 ^ (prefixWord ++ tailWord_1411531).sum := by decide
  have hdescent : baseEnd_1411531 < baseStart_1411531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411608 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 2, 5, 2]
def baseStart_1411608 : Nat := 118140960795 + 1411608 * 2 ^ 59
def prefixEnd_1411608 : Nat := 4983230072969 + 3 ^ 40 * 1411608 * 2
def baseEnd_1411608 : Nat := 724833399732018310908139

theorem tailTrace_1411608 : CollatzResearch.WordTrace tailWord_1411608 prefixEnd_1411608 724833399732018310908139 := by
  unfold tailWord_1411608
  simp only [CollatzResearch.WordTrace]
  refine ⟨25742786734996387148937739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34323715646661849531916985 25742786734996387148937739)
  ·
    refine ⟨38614180102494580723406609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25742786734996387148937739 38614180102494580723406609)
    ·
      refine ⟨28960635076870935542554957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38614180102494580723406609 28960635076870935542554957)
      ·
        refine ⟨10860238153826600828458109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28960635076870935542554957 10860238153826600828458109)
        ·
          refine ⟨4072589307684975310671791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10860238153826600828458109 4072589307684975310671791)
          ·
            refine ⟨6108883961527462966007687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4072589307684975310671791 6108883961527462966007687)
            ·
              refine ⟨9163325942291194449011531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6108883961527462966007687 9163325942291194449011531)
              ·
                refine ⟨13744988913436791673517297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9163325942291194449011531 13744988913436791673517297)
                ·
                  refine ⟨10308741685077593755137973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13744988913436791673517297 10308741685077593755137973)
                  ·
                    refine ⟨966444532976024414544185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10308741685077593755137973 966444532976024414544185)
                    ·
                      refine ⟨724833399732018310908139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 966444532976024414544185 724833399732018310908139)
                      ·
                        rfl

theorem cell23_1411608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_1411608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411608 prefixEnd_1411608 := by exact prefixLift 1411608
  have htrace : WordTrace (prefixWord ++ tailWord_1411608) baseStart_1411608 baseEnd_1411608 := by
    simpa [prefixWord, tailWord_1411608, baseEnd_1411608] using wordTrace_append hprefix tailTrace_1411608
  have hstable : (prefixWord ++ tailWord_1411608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411608).length < 2 ^ (prefixWord ++ tailWord_1411608).sum := by decide
  have hdescent : baseEnd_1411608 < baseStart_1411608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411621 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 4, 1, 4]
def baseStart_1411621 : Nat := 118140960795 + 1411621 * 2 ^ 59
def prefixEnd_1411621 : Nat := 4983230072969 + 3 ^ 40 * 1411621 * 2
def baseEnd_1411621 : Nat := 724840074980526760045579

theorem tailTrace_1411621 : CollatzResearch.WordTrace tailWord_1411621 prefixEnd_1411621 724840074980526760045579 := by
  unfold tailWord_1411621
  simp only [CollatzResearch.WordTrace]
  refine ⟨51486047618945677518098717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34324031745963785012065811 51486047618945677518098717)
  ·
    refine ⟨19307267857104629069287019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51486047618945677518098717 19307267857104629069287019)
    ·
      refine ⟨28960901785656943603930529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19307267857104629069287019 28960901785656943603930529)
      ·
        refine ⟨21720676339242707702947897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28960901785656943603930529 21720676339242707702947897)
        ·
          refine ⟨16290507254432030777210923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21720676339242707702947897 16290507254432030777210923)
          ·
            refine ⟨24435760881648046165816385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16290507254432030777210923 24435760881648046165816385)
            ·
              refine ⟨18326820661236034624362289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24435760881648046165816385 18326820661236034624362289)
              ·
                refine ⟨13745115495927025968271717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18326820661236034624362289 13745115495927025968271717)
                ·
                  refine ⟨2577209155486317369050947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13745115495927025968271717 2577209155486317369050947)
                  ·
                    refine ⟨3865813733229476053576421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2577209155486317369050947 3865813733229476053576421)
                    ·
                      refine ⟨724840074980526760045579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3865813733229476053576421 724840074980526760045579)
                      ·
                        rfl

theorem cell23_1411621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_1411621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411621 prefixEnd_1411621 := by exact prefixLift 1411621
  have htrace : WordTrace (prefixWord ++ tailWord_1411621) baseStart_1411621 baseEnd_1411621 := by
    simpa [prefixWord, tailWord_1411621, baseEnd_1411621] using wordTrace_append hprefix tailTrace_1411621
  have hstable : (prefixWord ++ tailWord_1411621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411621).length < 2 ^ (prefixWord ++ tailWord_1411621).sum := by decide
  have hdescent : baseEnd_1411621 < baseStart_1411621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411665 : List Nat := [1, 2, 2, 1, 3, 3, 2, 4, 1, 4]
def baseStart_1411665 : Nat := 118140960795 + 1411665 * 2 ^ 59
def prefixEnd_1411665 : Nat := 4983230072969 + 3 ^ 40 * 1411665 * 2
def baseEnd_1411665 : Nat := 241620889376441529298459

theorem tailTrace_1411665 : CollatzResearch.WordTrace tailWord_1411665 prefixEnd_1411665 241620889376441529298459 := by
  unfold tailWord_1411665
  simp only [CollatzResearch.WordTrace]
  refine ⟨51487652430786273032700449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34325101620524182021800299 51487652430786273032700449)
  ·
    refine ⟨38615739323089704774525337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51487652430786273032700449 38615739323089704774525337)
    ·
      refine ⟨28961804492317278580894003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38615739323089704774525337 28961804492317278580894003)
      ·
        refine ⟨43442706738475917871341005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28961804492317278580894003 43442706738475917871341005)
        ·
          refine ⟨16291015026928469201752877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43442706738475917871341005 16291015026928469201752877)
          ·
            refine ⟨6109130635098175950657329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16291015026928469201752877 6109130635098175950657329)
            ·
              refine ⟨4581847976323631962992997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6109130635098175950657329 4581847976323631962992997)
              ·
                refine ⟨859096495560680993061187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4581847976323631962992997 859096495560680993061187)
                ·
                  refine ⟨1288644743341021489591781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 859096495560680993061187 1288644743341021489591781)
                  ·
                    refine ⟨241620889376441529298459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1288644743341021489591781 241620889376441529298459)
                    ·
                      rfl

theorem cell23_1411665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 1, 4].length) (baseStart_1411665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411665 prefixEnd_1411665 := by exact prefixLift 1411665
  have htrace : WordTrace (prefixWord ++ tailWord_1411665) baseStart_1411665 baseEnd_1411665 := by
    simpa [prefixWord, tailWord_1411665, baseEnd_1411665] using wordTrace_append hprefix tailTrace_1411665
  have hstable : (prefixWord ++ tailWord_1411665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411665).length < 2 ^ (prefixWord ++ tailWord_1411665).sum := by decide
  have hdescent : baseEnd_1411665 < baseStart_1411665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411708 : List Nat := [2, 2, 2, 1, 1, 2, 4, 3, 1, 5]
def baseStart_1411708 : Nat := 118140960795 + 1411708 * 2 ^ 59
def prefixEnd_1411708 : Nat := 4983230072969 + 3 ^ 40 * 1411708 * 2
def baseEnd_1411708 : Nat := 241628249265822639885893

theorem tailTrace_1411708 : CollatzResearch.WordTrace tailWord_1411708 prefixEnd_1411708 241628249265822639885893 := by
  unfold tailWord_1411708
  simp only [CollatzResearch.WordTrace]
  refine ⟨25744610384815245688257889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34326147179753660917677185 25744610384815245688257889)
  ·
    refine ⟨19308457788611434266193417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25744610384815245688257889 19308457788611434266193417)
    ·
      refine ⟨14481343341458575699645063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19308457788611434266193417 14481343341458575699645063)
      ·
        refine ⟨21722015012187863549467595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14481343341458575699645063 21722015012187863549467595)
        ·
          refine ⟨32583022518281795324201393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21722015012187863549467595 32583022518281795324201393)
          ·
            refine ⟨24437266888711346493151045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32583022518281795324201393 24437266888711346493151045)
            ·
              refine ⟨4581987541633377467465821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24437266888711346493151045 4581987541633377467465821)
              ·
                refine ⟨1718245328112516550299683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4581987541633377467465821 1718245328112516550299683)
                ·
                  refine ⟨2577367992168774825449525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1718245328112516550299683 2577367992168774825449525)
                  ·
                    refine ⟨241628249265822639885893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2577367992168774825449525 241628249265822639885893)
                    ·
                      rfl

theorem cell23_1411708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_1411708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411708 prefixEnd_1411708 := by exact prefixLift 1411708
  have htrace : WordTrace (prefixWord ++ tailWord_1411708) baseStart_1411708 baseEnd_1411708 := by
    simpa [prefixWord, tailWord_1411708, baseEnd_1411708] using wordTrace_append hprefix tailTrace_1411708
  have hstable : (prefixWord ++ tailWord_1411708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411708).length < 2 ^ (prefixWord ++ tailWord_1411708).sum := by decide
  have hdescent : baseEnd_1411708 < baseStart_1411708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411745 : List Nat := [1, 2, 3, 3, 3, 1, 1, 1, 3, 1, 4]
def baseStart_1411745 : Nat := 118140960795 + 1411745 * 2 ^ 59
def prefixEnd_1411745 : Nat := 4983230072969 + 3 ^ 40 * 1411745 * 2
def baseEnd_1411745 : Nat := 724903746581684274895009

theorem tailTrace_1411745 : CollatzResearch.WordTrace tailWord_1411745 prefixEnd_1411745 724903746581684274895009 := by
  unfold tailWord_1411745
  simp only [CollatzResearch.WordTrace]
  refine ⟨51490570270496446695612689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34327046846997631130408459 51490570270496446695612689)
  ·
    refine ⟨38617927702872335021709517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51490570270496446695612689 38617927702872335021709517)
    ·
      refine ⟨14481722888577125633141069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38617927702872335021709517 14481722888577125633141069)
      ·
        refine ⟨5430646083216422112427901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14481722888577125633141069 5430646083216422112427901)
        ·
          refine ⟨2036492281206158292160463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5430646083216422112427901 2036492281206158292160463)
          ·
            refine ⟨3054738421809237438240695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2036492281206158292160463 3054738421809237438240695)
            ·
              refine ⟨4582107632713856157361043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3054738421809237438240695 4582107632713856157361043)
              ·
                refine ⟨6873161449070784236041565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4582107632713856157361043 6873161449070784236041565)
                ·
                  refine ⟨2577435543401544088515587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6873161449070784236041565 2577435543401544088515587)
                  ·
                    refine ⟨3866153315102316132773381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2577435543401544088515587 3866153315102316132773381)
                    ·
                      refine ⟨724903746581684274895009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3866153315102316132773381 724903746581684274895009)
                      ·
                        rfl

theorem cell23_1411745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_1411745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411745 prefixEnd_1411745 := by exact prefixLift 1411745
  have htrace : WordTrace (prefixWord ++ tailWord_1411745) baseStart_1411745 baseEnd_1411745 := by
    simpa [prefixWord, tailWord_1411745, baseEnd_1411745] using wordTrace_append hprefix tailTrace_1411745
  have hstable : (prefixWord ++ tailWord_1411745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411745).length < 2 ^ (prefixWord ++ tailWord_1411745).sum := by decide
  have hdescent : baseEnd_1411745 < baseStart_1411745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411765 : List Nat := [1, 3, 3, 3, 1, 1, 3, 1, 1, 1, 5]
def baseStart_1411765 : Nat := 118140960795 + 1411765 * 2 ^ 59
def prefixEnd_1411765 : Nat := 4983230072969 + 3 ^ 40 * 1411765 * 2
def baseEnd_1411765 : Nat := 724914016194774196644917

theorem tailTrace_1411765 : CollatzResearch.WordTrace tailWord_1411765 prefixEnd_1411765 724914016194774196644917 := by
  unfold tailWord_1411765
  simp only [CollatzResearch.WordTrace]
  refine ⟨51491299730423990111340749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34327533153615993407560499 51491299730423990111340749)
  ·
    refine ⟨19309237398908996291752781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51491299730423990111340749 19309237398908996291752781)
    ·
      refine ⟨7240964024590873609407293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19309237398908996291752781 7240964024590873609407293)
      ·
        refine ⟨2715361509221577603527735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7240964024590873609407293 2715361509221577603527735)
        ·
          refine ⟨4073042263832366405291603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2715361509221577603527735 4073042263832366405291603)
          ·
            refine ⟨6109563395748549607937405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4073042263832366405291603 6109563395748549607937405)
            ·
              refine ⟨2291086273405706102976527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6109563395748549607937405 2291086273405706102976527)
              ·
                refine ⟨3436629410108559154464791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2291086273405706102976527 3436629410108559154464791)
                ·
                  refine ⟨5154944115162838731697187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3436629410108559154464791 5154944115162838731697187)
                  ·
                    refine ⟨7732416172744258097545781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5154944115162838731697187 7732416172744258097545781)
                    ·
                      refine ⟨724914016194774196644917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7732416172744258097545781 724914016194774196644917)
                      ·
                        rfl

theorem cell23_1411765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_1411765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411765 prefixEnd_1411765 := by exact prefixLift 1411765
  have htrace : WordTrace (prefixWord ++ tailWord_1411765) baseStart_1411765 baseEnd_1411765 := by
    simpa [prefixWord, tailWord_1411765, baseEnd_1411765] using wordTrace_append hprefix tailTrace_1411765
  have hstable : (prefixWord ++ tailWord_1411765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411765).length < 2 ^ (prefixWord ++ tailWord_1411765).sum := by decide
  have hdescent : baseEnd_1411765 < baseStart_1411765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411791 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 5]
def baseStart_1411791 : Nat := 118140960795 + 1411791 * 2 ^ 59
def prefixEnd_1411791 : Nat := 4983230072969 + 3 ^ 40 * 1411791 * 2
def baseEnd_1411791 : Nat := 724927366691791094919797

theorem tailTrace_1411791 : CollatzResearch.WordTrace tailWord_1411791 prefixEnd_1411791 724927366691791094919797 := by
  unfold tailWord_1411791
  simp only [CollatzResearch.WordTrace]
  refine ⟨51492248028329796551787227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34328165352219864367858151 51492248028329796551787227)
  ·
    refine ⟨77238372042494694827680841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51492248028329796551787227 77238372042494694827680841)
    ·
      refine ⟨57928779031871021120760631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77238372042494694827680841 57928779031871021120760631)
      ·
        refine ⟨86893168547806531681140947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57928779031871021120760631 86893168547806531681140947)
        ·
          refine ⟨130339752821709797521711421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86893168547806531681140947 130339752821709797521711421)
          ·
            refine ⟨48877407308141174070641783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130339752821709797521711421 48877407308141174070641783)
            ·
              refine ⟨73316110962211761105962675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48877407308141174070641783 73316110962211761105962675)
              ·
                refine ⟨109974166443317641658944013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73316110962211761105962675 109974166443317641658944013)
                ·
                  refine ⟨41240312416244115622104005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109974166443317641658944013 41240312416244115622104005)
                  ·
                    refine ⟨7732558578045771679144501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41240312416244115622104005 7732558578045771679144501)
                    ·
                      refine ⟨724927366691791094919797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7732558578045771679144501 724927366691791094919797)
                      ·
                        rfl

theorem cell23_1411791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 5].length) (baseStart_1411791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411791 prefixEnd_1411791 := by exact prefixLift 1411791
  have htrace : WordTrace (prefixWord ++ tailWord_1411791) baseStart_1411791 baseEnd_1411791 := by
    simpa [prefixWord, tailWord_1411791, baseEnd_1411791] using wordTrace_append hprefix tailTrace_1411791
  have hstable : (prefixWord ++ tailWord_1411791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411791).length < 2 ^ (prefixWord ++ tailWord_1411791).sum := by decide
  have hdescent : baseEnd_1411791 < baseStart_1411791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411816 : List Nat := [2, 1, 4, 1, 5, 1, 2, 1, 1, 2, 3]
def baseStart_1411816 : Nat := 118140960795 + 1411816 * 2 ^ 59
def prefixEnd_1411816 : Nat := 4983230072969 + 3 ^ 40 * 1411816 * 2
def baseEnd_1411816 : Nat := 724940203708153497107183

theorem tailTrace_1411816 : CollatzResearch.WordTrace tailWord_1411816 prefixEnd_1411816 724940203708153497107183 := by
  unfold tailWord_1411816
  simp only [CollatzResearch.WordTrace]
  refine ⟨25746579926619612910723651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34328773235492817214298201 25746579926619612910723651)
  ·
    refine ⟨38619869889929419366085477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25746579926619612910723651 38619869889929419366085477)
    ·
      refine ⟨7241225604361766131141027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38619869889929419366085477 7241225604361766131141027)
      ·
        refine ⟨10861838406542649196711541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7241225604361766131141027 10861838406542649196711541)
        ·
          refine ⟨1018297350613373362191707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10861838406542649196711541 1018297350613373362191707)
          ·
            refine ⟨1527446025920060043287561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1018297350613373362191707 1527446025920060043287561)
            ·
              refine ⟨1145584519440045032465671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1527446025920060043287561 1145584519440045032465671)
              ·
                refine ⟨1718376779160067548698507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1145584519440045032465671 1718376779160067548698507)
                ·
                  refine ⟨2577565168740101323047761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1718376779160067548698507 2577565168740101323047761)
                  ·
                    refine ⟨1933173876555075992285821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2577565168740101323047761 1933173876555075992285821)
                    ·
                      refine ⟨724940203708153497107183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1933173876555075992285821 724940203708153497107183)
                      ·
                        rfl

theorem cell23_1411816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_1411816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411816 prefixEnd_1411816 := by exact prefixLift 1411816
  have htrace : WordTrace (prefixWord ++ tailWord_1411816) baseStart_1411816 baseEnd_1411816 := by
    simpa [prefixWord, tailWord_1411816, baseEnd_1411816] using wordTrace_append hprefix tailTrace_1411816
  have hstable : (prefixWord ++ tailWord_1411816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411816).length < 2 ^ (prefixWord ++ tailWord_1411816).sum := by decide
  have hdescent : baseEnd_1411816 < baseStart_1411816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411895 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 2, 5, 2]
def baseStart_1411895 : Nat := 118140960795 + 1411895 * 2 ^ 59
def prefixEnd_1411895 : Nat := 4983230072969 + 3 ^ 40 * 1411895 * 2
def baseEnd_1411895 : Nat := 724980768679858688019319

theorem tailTrace_1411895 : CollatzResearch.WordTrace tailWord_1411895 prefixEnd_1411895 724980768679858688019319 := by
  unfold tailWord_1411895
  simp only [CollatzResearch.WordTrace]
  refine ⟨51496041219953022313573139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34330694146635348209048759 51496041219953022313573139)
  ·
    refine ⟨77244061829929533470359709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51496041219953022313573139 77244061829929533470359709)
    ·
      refine ⟨28966523186223575051384891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77244061829929533470359709 28966523186223575051384891)
      ·
        refine ⟨43449784779335362577077337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28966523186223575051384891 43449784779335362577077337)
        ·
          refine ⟨32587338584501521932808003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43449784779335362577077337 32587338584501521932808003)
          ·
            refine ⟨48881007876752282899212005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32587338584501521932808003 48881007876752282899212005)
            ·
              refine ⟨9165188976891053043602251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48881007876752282899212005 9165188976891053043602251)
              ·
                refine ⟨13747783465336579565403377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9165188976891053043602251 13747783465336579565403377)
                ·
                  refine ⟨10310837599002434674052533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13747783465336579565403377 10310837599002434674052533)
                  ·
                    refine ⟨966641024906478250692425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10310837599002434674052533 966641024906478250692425)
                    ·
                      refine ⟨724980768679858688019319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 966641024906478250692425 724980768679858688019319)
                      ·
                        rfl

theorem cell23_1411895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 5, 2].length) (baseStart_1411895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411895 prefixEnd_1411895 := by exact prefixLift 1411895
  have htrace : WordTrace (prefixWord ++ tailWord_1411895) baseStart_1411895 baseEnd_1411895 := by
    simpa [prefixWord, tailWord_1411895, baseEnd_1411895] using wordTrace_append hprefix tailTrace_1411895
  have hstable : (prefixWord ++ tailWord_1411895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411895).length < 2 ^ (prefixWord ++ tailWord_1411895).sum := by decide
  have hdescent : baseEnd_1411895 < baseStart_1411895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411918 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 2, 8]
def baseStart_1411918 : Nat := 118140960795 + 1411918 * 2 ^ 59
def prefixEnd_1411918 : Nat := 4983230072969 + 3 ^ 40 * 1411918 * 2
def baseEnd_1411918 : Nat := 241664192911637366010571

theorem tailTrace_1411918 : CollatzResearch.WordTrace tailWord_1411918 prefixEnd_1411918 241664192911637366010571 := by
  unfold tailWord_1411918
  simp only [CollatzResearch.WordTrace]
  refine ⟨6437110012358712155207551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34331253399246464827773605 6437110012358712155207551)
  ·
    refine ⟨9655665018538068232811327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6437110012358712155207551 9655665018538068232811327)
    ·
      refine ⟨14483497527807102349216991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9655665018538068232811327 14483497527807102349216991)
      ·
        refine ⟨21725246291710653523825487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14483497527807102349216991 21725246291710653523825487)
        ·
          refine ⟨32587869437565980285738231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21725246291710653523825487 32587869437565980285738231)
          ·
            refine ⟨48881804156348970428607347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32587869437565980285738231 48881804156348970428607347)
            ·
              refine ⟨73322706234523455642911021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48881804156348970428607347 73322706234523455642911021)
              ·
                refine ⟨27496014837946295866091633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73322706234523455642911021 27496014837946295866091633)
                ·
                  refine ⟨20622011128459721899568725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27496014837946295866091633 20622011128459721899568725)
                  ·
                    refine ⟨241664192911637366010571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20622011128459721899568725 241664192911637366010571)
                    ·
                      rfl

theorem cell23_1411918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_1411918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411918 prefixEnd_1411918 := by exact prefixLift 1411918
  have htrace : WordTrace (prefixWord ++ tailWord_1411918) baseStart_1411918 baseEnd_1411918 := by
    simpa [prefixWord, tailWord_1411918, baseEnd_1411918] using wordTrace_append hprefix tailTrace_1411918
  have hstable : (prefixWord ++ tailWord_1411918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411918).length < 2 ^ (prefixWord ++ tailWord_1411918).sum := by decide
  have hdescent : baseEnd_1411918 < baseStart_1411918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411965 : List Nat := [1, 4, 1, 1, 2, 1, 4, 3, 6]
def baseStart_1411965 : Nat := 118140960795 + 1411965 * 2 ^ 59
def prefixEnd_1411965 : Nat := 4983230072969 + 3 ^ 40 * 1411965 * 2
def baseEnd_1411965 : Nat := 80557412480630379349333

theorem tailTrace_1411965 : CollatzResearch.WordTrace tailWord_1411965 prefixEnd_1411965 80557412480630379349333 := by
  unfold tailWord_1411965
  simp only [CollatzResearch.WordTrace]
  refine ⟨51498594329699424268621349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34332396219799616179080899 51498594329699424268621349)
  ·
    refine ⟨9655986436818642050366503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51498594329699424268621349 9655986436818642050366503)
    ·
      refine ⟨14483979655227963075549755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9655986436818642050366503 14483979655227963075549755)
      ·
        refine ⟨21725969482841944613324633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14483979655227963075549755 21725969482841944613324633)
        ·
          refine ⟨16294477112131458459993475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21725969482841944613324633 16294477112131458459993475)
          ·
            refine ⟨24441715668197187689990213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16294477112131458459993475 24441715668197187689990213)
            ·
              refine ⟨4582821687786972691873165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24441715668197187689990213 4582821687786972691873165)
              ·
                refine ⟨1718558132920114759452437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4582821687786972691873165 1718558132920114759452437)
                ·
                  refine ⟨80557412480630379349333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1718558132920114759452437 80557412480630379349333)
                  ·
                    rfl

theorem cell23_1411965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_1411965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411965 prefixEnd_1411965 := by exact prefixLift 1411965
  have htrace : WordTrace (prefixWord ++ tailWord_1411965) baseStart_1411965 baseEnd_1411965 := by
    simpa [prefixWord, tailWord_1411965, baseEnd_1411965] using wordTrace_append hprefix tailTrace_1411965
  have hstable : (prefixWord ++ tailWord_1411965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411965).length < 2 ^ (prefixWord ++ tailWord_1411965).sum := by decide
  have hdescent : baseEnd_1411965 < baseStart_1411965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411968 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 6]
def baseStart_1411968 : Nat := 118140960795 + 1411968 * 2 ^ 59
def prefixEnd_1411968 : Nat := 4983230072969 + 3 ^ 40 * 1411968 * 2
def baseEnd_1411968 : Nat := 725018252767636902406483

theorem tailTrace_1411968 : CollatzResearch.WordTrace tailWord_1411968 prefixEnd_1411968 725018252767636902406483 := by
  unfold tailWord_1411968
  simp only [CollatzResearch.WordTrace]
  refine ⟨25749351874344277890490279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34332469165792370520653705 25749351874344277890490279)
  ·
    refine ⟨38624027811516416835735419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25749351874344277890490279 38624027811516416835735419)
    ·
      refine ⟨57936041717274625253603129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38624027811516416835735419 57936041717274625253603129)
      ·
        refine ⟨43452031287955968940202347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57936041717274625253603129 43452031287955968940202347)
        ·
          refine ⟨65178046931933953410303521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43452031287955968940202347 65178046931933953410303521)
          ·
            refine ⟨48883535198950465057727641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65178046931933953410303521 48883535198950465057727641)
            ·
              refine ⟨36662651399212848793295731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48883535198950465057727641 36662651399212848793295731)
              ·
                refine ⟨54993977098819273189943597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36662651399212848793295731 54993977098819273189943597)
                ·
                  refine ⟨20622741412057227446228849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54993977098819273189943597 20622741412057227446228849)
                  ·
                    refine ⟨15467056059042920584671637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20622741412057227446228849 15467056059042920584671637)
                    ·
                      refine ⟨725018252767636902406483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15467056059042920584671637 725018252767636902406483)
                      ·
                        rfl

theorem cell23_1411968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_1411968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1411968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1411968 prefixEnd_1411968 := by exact prefixLift 1411968
  have htrace : WordTrace (prefixWord ++ tailWord_1411968) baseStart_1411968 baseEnd_1411968 := by
    simpa [prefixWord, tailWord_1411968, baseEnd_1411968] using wordTrace_append hprefix tailTrace_1411968
  have hstable : (prefixWord ++ tailWord_1411968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411968).length < 2 ^ (prefixWord ++ tailWord_1411968).sum := by decide
  have hdescent : baseEnd_1411968 < baseStart_1411968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412009 : List Nat := [1, 2, 1, 1, 1, 1, 5, 6, 1, 1, 3]
def baseStart_1412009 : Nat := 118140960795 + 1412009 * 2 ^ 59
def prefixEnd_1412009 : Nat := 4983230072969 + 3 ^ 40 * 1412009 * 2
def baseEnd_1412009 : Nat := 725039305474471241993795

theorem tailTrace_1412009 : CollatzResearch.WordTrace tailWord_1412009 prefixEnd_1412009 725039305474471241993795 := by
  unfold tailWord_1412009
  simp only [CollatzResearch.WordTrace]
  refine ⟨51500199141540019783223081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34333466094360013188815387 51500199141540019783223081)
  ·
    refine ⟨38625149356155014837417311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51500199141540019783223081 38625149356155014837417311)
    ·
      refine ⟨57937724034232522256125967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38625149356155014837417311 57937724034232522256125967)
      ·
        refine ⟨86906586051348783384188951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57937724034232522256125967 86906586051348783384188951)
        ·
          refine ⟨130359879077023175076283427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86906586051348783384188951 130359879077023175076283427)
          ·
            refine ⟨195539818615534762614425141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130359879077023175076283427 195539818615534762614425141)
            ·
              refine ⟨18331857995206383995102357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 195539818615534762614425141 18331857995206383995102357)
              ·
                refine ⟨859305843525299249770423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18331857995206383995102357 859305843525299249770423)
                ·
                  refine ⟨1288958765287948874655635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 859305843525299249770423 1288958765287948874655635)
                  ·
                    refine ⟨1933438147931923311983453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1288958765287948874655635 1933438147931923311983453)
                    ·
                      refine ⟨725039305474471241993795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1933438147931923311983453 725039305474471241993795)
                      ·
                        rfl

theorem cell23_1412009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 1, 1, 3].length) (baseStart_1412009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412009 prefixEnd_1412009 := by exact prefixLift 1412009
  have htrace : WordTrace (prefixWord ++ tailWord_1412009) baseStart_1412009 baseEnd_1412009 := by
    simpa [prefixWord, tailWord_1412009, baseEnd_1412009] using wordTrace_append hprefix tailTrace_1412009
  have hstable : (prefixWord ++ tailWord_1412009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412009).length < 2 ^ (prefixWord ++ tailWord_1412009).sum := by decide
  have hdescent : baseEnd_1412009 < baseStart_1412009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412015 : List Nat := [1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 4]
def baseStart_1412015 : Nat := 118140960795 + 1412015 * 2 ^ 59
def prefixEnd_1412015 : Nat := 4983230072969 + 3 ^ 40 * 1412015 * 2
def baseEnd_1412015 : Nat := 725042386358398218518767

theorem tailTrace_1412015 : CollatzResearch.WordTrace tailWord_1412015 prefixEnd_1412015 725042386358398218518767 := by
  unfold tailWord_1412015
  simp only [CollatzResearch.WordTrace]
  refine ⟨51500417979518282807941499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34333611986345521871960999 51500417979518282807941499)
  ·
    refine ⟨77250626969277424211912249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51500417979518282807941499 77250626969277424211912249)
    ·
      refine ⟨57937970226958068158934187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77250626969277424211912249 57937970226958068158934187)
      ·
        refine ⟨86906955340437102238401281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57937970226958068158934187 86906955340437102238401281)
        ·
          refine ⟨65180216505327826678800961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86906955340437102238401281 65180216505327826678800961)
          ·
            refine ⟨48885162378995870009100721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65180216505327826678800961 48885162378995870009100721)
            ·
              refine ⟨36663871784246902506825541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48885162378995870009100721 36663871784246902506825541)
              ·
                refine ⟨6874475959546294220029789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36663871784246902506825541 6874475959546294220029789)
                ·
                  refine ⟨2577928484829860332511171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6874475959546294220029789 2577928484829860332511171)
                  ·
                    refine ⟨3866892727244790498766757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2577928484829860332511171 3866892727244790498766757)
                    ·
                      refine ⟨725042386358398218518767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3866892727244790498766757 725042386358398218518767)
                      ·
                        rfl

theorem cell23_1412015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 4].length) (baseStart_1412015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412015 prefixEnd_1412015 := by exact prefixLift 1412015
  have htrace : WordTrace (prefixWord ++ tailWord_1412015) baseStart_1412015 baseEnd_1412015 := by
    simpa [prefixWord, tailWord_1412015, baseEnd_1412015] using wordTrace_append hprefix tailTrace_1412015
  have hstable : (prefixWord ++ tailWord_1412015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412015).length < 2 ^ (prefixWord ++ tailWord_1412015).sum := by decide
  have hdescent : baseEnd_1412015 < baseStart_1412015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412029 : List Nat := [1, 4, 1, 2, 4, 1, 2, 2, 1, 5]
def baseStart_1412029 : Nat := 118140960795 + 1412029 * 2 ^ 59
def prefixEnd_1412029 : Nat := 4983230072969 + 3 ^ 40 * 1412029 * 2
def baseEnd_1412029 : Nat := 241683191695853721247901

theorem tailTrace_1412029 : CollatzResearch.WordTrace tailWord_1412029 prefixEnd_1412029 241683191695853721247901 := by
  unfold tailWord_1412029
  simp only [CollatzResearch.WordTrace]
  refine ⟨51500928601467563198951141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34333952400978375465967427 51500928601467563198951141)
  ·
    refine ⟨9656424112775168099803339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51500928601467563198951141 9656424112775168099803339)
    ·
      refine ⟨14484636169162752149705009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9656424112775168099803339 14484636169162752149705009)
      ·
        refine ⟨10863477126872064112278757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14484636169162752149705009 10863477126872064112278757)
        ·
          refine ⟨2036901961288512021052267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10863477126872064112278757 2036901961288512021052267)
          ·
            refine ⟨3055352941932768031578401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2036901961288512021052267 3055352941932768031578401)
            ·
              refine ⟨2291514706449576023683801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3055352941932768031578401 2291514706449576023683801)
              ·
                refine ⟨1718636029837182017762851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2291514706449576023683801 1718636029837182017762851)
                ·
                  refine ⟨2577954044755773026644277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1718636029837182017762851 2577954044755773026644277)
                  ·
                    refine ⟨241683191695853721247901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2577954044755773026644277 241683191695853721247901)
                    ·
                      rfl

theorem cell23_1412029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_1412029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412029 prefixEnd_1412029 := by exact prefixLift 1412029
  have htrace : WordTrace (prefixWord ++ tailWord_1412029) baseStart_1412029 baseEnd_1412029 := by
    simpa [prefixWord, tailWord_1412029, baseEnd_1412029] using wordTrace_append hprefix tailTrace_1412029
  have hstable : (prefixWord ++ tailWord_1412029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412029).length < 2 ^ (prefixWord ++ tailWord_1412029).sum := by decide
  have hdescent : baseEnd_1412029 < baseStart_1412029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412032 : List Nat := [2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 4]
def baseStart_1412032 : Nat := 118140960795 + 1412032 * 2 ^ 59
def prefixEnd_1412032 : Nat := 4983230072969 + 3 ^ 40 * 1412032 * 2
def baseEnd_1412032 : Nat := 725051115529524652006189

theorem tailTrace_1412032 : CollatzResearch.WordTrace tailWord_1412032 prefixEnd_1412032 725051115529524652006189 := by
  unfold tailWord_1412032
  simp only [CollatzResearch.WordTrace]
  refine ⟨25750519010228347355655175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34334025346971129807540233 25750519010228347355655175)
  ·
    refine ⟨38625778515342521033482763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25750519010228347355655175 38625778515342521033482763)
    ·
      refine ⟨57938667773013781550224145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38625778515342521033482763 57938667773013781550224145)
      ·
        refine ⟨43454000829760336162668109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57938667773013781550224145 43454000829760336162668109)
        ·
          refine ⟨16295250311160126061000541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43454000829760336162668109 16295250311160126061000541)
          ·
            refine ⟨6110718866685047272875203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16295250311160126061000541 6110718866685047272875203)
            ·
              refine ⟨9166078300027570909312805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6110718866685047272875203 9166078300027570909312805)
              ·
                refine ⟨1718639681255169545496151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9166078300027570909312805 1718639681255169545496151)
                ·
                  refine ⟨2577959521882754318244227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1718639681255169545496151 2577959521882754318244227)
                  ·
                    refine ⟨3866939282824131477366341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2577959521882754318244227 3866939282824131477366341)
                    ·
                      refine ⟨725051115529524652006189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3866939282824131477366341 725051115529524652006189)
                      ·
                        rfl

theorem cell23_1412032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 4].length) (baseStart_1412032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412032 prefixEnd_1412032 := by exact prefixLift 1412032
  have htrace : WordTrace (prefixWord ++ tailWord_1412032) baseStart_1412032 baseEnd_1412032 := by
    simpa [prefixWord, tailWord_1412032, baseEnd_1412032] using wordTrace_append hprefix tailTrace_1412032
  have hstable : (prefixWord ++ tailWord_1412032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412032).length < 2 ^ (prefixWord ++ tailWord_1412032).sum := by decide
  have hdescent : baseEnd_1412032 < baseStart_1412032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412052 : List Nat := [2, 4, 1, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_1412052 : Nat := 118140960795 + 1412052 * 2 ^ 59
def prefixEnd_1412052 : Nat := 4983230072969 + 3 ^ 40 * 1412052 * 2
def baseEnd_1412052 : Nat := 725061385142614573756097

theorem tailTrace_1412052 : CollatzResearch.WordTrace tailWord_1412052 prefixEnd_1412052 725061385142614573756097 := by
  unfold tailWord_1412052
  simp only [CollatzResearch.WordTrace]
  refine ⟨25750883740192119063519205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34334511653589492084692273 25750883740192119063519205)
  ·
    refine ⟨4828290701286022324409851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25750883740192119063519205 4828290701286022324409851)
    ·
      refine ⟨7242436051929033486614777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4828290701286022324409851 7242436051929033486614777)
      ·
        refine ⟨5431827038946775114961083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7242436051929033486614777 5431827038946775114961083)
        ·
          refine ⟨8147740558420162672441625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5431827038946775114961083 8147740558420162672441625)
          ·
            refine ⟨6110805418815122004331219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8147740558420162672441625 6110805418815122004331219)
            ·
              refine ⟨9166208128222683006496829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6110805418815122004331219 9166208128222683006496829)
              ·
                refine ⟨3437328048083506127436311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9166208128222683006496829 3437328048083506127436311)
                ·
                  refine ⟨5155992072125259191154467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3437328048083506127436311 5155992072125259191154467)
                  ·
                    refine ⟨7733988108187888786731701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5155992072125259191154467 7733988108187888786731701)
                    ·
                      refine ⟨725061385142614573756097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7733988108187888786731701 725061385142614573756097)
                      ·
                        rfl

theorem cell23_1412052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_1412052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412052 prefixEnd_1412052 := by exact prefixLift 1412052
  have htrace : WordTrace (prefixWord ++ tailWord_1412052) baseStart_1412052 baseEnd_1412052 := by
    simpa [prefixWord, tailWord_1412052, baseEnd_1412052] using wordTrace_append hprefix tailTrace_1412052
  have hstable : (prefixWord ++ tailWord_1412052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412052).length < 2 ^ (prefixWord ++ tailWord_1412052).sum := by decide
  have hdescent : baseEnd_1412052 < baseStart_1412052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412086 : List Nat := [5, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3]
def baseStart_1412086 : Nat := 118140960795 + 1412086 * 2 ^ 59
def prefixEnd_1412086 : Nat := 4983230072969 + 3 ^ 40 * 1412086 * 2
def baseEnd_1412086 : Nat := 725078843484867440730941

theorem tailTrace_1412086 : CollatzResearch.WordTrace tailWord_1412086 prefixEnd_1412086 725078843484867440730941 := by
  unfold tailWord_1412086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3218937972641316370861007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34335338374840707955850741 3218937972641316370861007)
  ·
    refine ⟨4828406958961974556291511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3218937972641316370861007 4828406958961974556291511)
    ·
      refine ⟨7242610438442961834437267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4828406958961974556291511 7242610438442961834437267)
      ·
        refine ⟨10863915657664442751655901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7242610438442961834437267 10863915657664442751655901)
        ·
          refine ⟨4073968371624166031870963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10863915657664442751655901 4073968371624166031870963)
          ·
            refine ⟨6110952557436249047806445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4073968371624166031870963 6110952557436249047806445)
            ·
              refine ⟨2291607209038593392927417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6110952557436249047806445 2291607209038593392927417)
              ·
                refine ⟨1718705406778945044695563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2291607209038593392927417 1718705406778945044695563)
                ·
                  refine ⟨2578058110168417567043345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1718705406778945044695563 2578058110168417567043345)
                  ·
                    refine ⟨1933543582626313175282509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2578058110168417567043345 1933543582626313175282509)
                    ·
                      refine ⟨725078843484867440730941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1933543582626313175282509 725078843484867440730941)
                      ·
                        rfl

theorem cell23_1412086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_1412086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412086 prefixEnd_1412086 := by exact prefixLift 1412086
  have htrace : WordTrace (prefixWord ++ tailWord_1412086) baseStart_1412086 baseEnd_1412086 := by
    simpa [prefixWord, tailWord_1412086, baseEnd_1412086] using wordTrace_append hprefix tailTrace_1412086
  have hstable : (prefixWord ++ tailWord_1412086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412086).length < 2 ^ (prefixWord ++ tailWord_1412086).sum := by decide
  have hdescent : baseEnd_1412086 < baseStart_1412086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412105 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 4, 3, 4]
def baseStart_1412105 : Nat := 118140960795 + 1412105 * 2 ^ 59
def prefixEnd_1412105 : Nat := 4983230072969 + 3 ^ 40 * 1412105 * 2
def baseEnd_1412105 : Nat := 725088599617302866393353

theorem tailTrace_1412105 : CollatzResearch.WordTrace tailWord_1412105 prefixEnd_1412105 725088599617302866393353 := by
  unfold tailWord_1412105
  simp only [CollatzResearch.WordTrace]
  refine ⟨51503700549192228178717769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34335800366128152119145179 51503700549192228178717769)
  ·
    refine ⟨38627775411894171134038327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51503700549192228178717769 38627775411894171134038327)
    ·
      refine ⟨57941663117841256701057491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38627775411894171134038327 57941663117841256701057491)
      ·
        refine ⟨86912494676761885051586237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57941663117841256701057491 86912494676761885051586237)
        ·
          refine ⟨32592185503785706894344839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86912494676761885051586237 32592185503785706894344839)
          ·
            refine ⟨48888278255678560341517259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32592185503785706894344839 48888278255678560341517259)
            ·
              refine ⟨73332417383517840512275889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48888278255678560341517259 73332417383517840512275889)
              ·
                refine ⟨54999313037638380384206917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73332417383517840512275889 54999313037638380384206917)
                ·
                  refine ⟨10312371194557196322038797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54999313037638380384206917 10312371194557196322038797)
                  ·
                    refine ⟨3867139197958948620764549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10312371194557196322038797 3867139197958948620764549)
                    ·
                      refine ⟨725088599617302866393353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3867139197958948620764549 725088599617302866393353)
                      ·
                        rfl

theorem cell23_1412105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 3, 4].length) (baseStart_1412105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412105 prefixEnd_1412105 := by exact prefixLift 1412105
  have htrace : WordTrace (prefixWord ++ tailWord_1412105) baseStart_1412105 baseEnd_1412105 := by
    simpa [prefixWord, tailWord_1412105, baseEnd_1412105] using wordTrace_append hprefix tailTrace_1412105
  have hstable : (prefixWord ++ tailWord_1412105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412105).length < 2 ^ (prefixWord ++ tailWord_1412105).sum := by decide
  have hdescent : baseEnd_1412105 < baseStart_1412105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412115 : List Nat := [1, 1, 1, 2, 1, 4, 1, 4, 2, 6]
def baseStart_1412115 : Nat := 118140960795 + 1412115 * 2 ^ 59
def prefixEnd_1412115 : Nat := 4983230072969 + 3 ^ 40 * 1412115 * 2
def baseEnd_1412115 : Nat := 241697911474615942422769

theorem tailTrace_1412115 : CollatzResearch.WordTrace tailWord_1412115 prefixEnd_1412115 241697911474615942422769 := by
  unfold tailWord_1412115
  simp only [CollatzResearch.WordTrace]
  refine ⟨51504065279155999886581799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34336043519437333257721199 51504065279155999886581799)
  ·
    refine ⟨77256097918733999829872699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51504065279155999886581799 77256097918733999829872699)
    ·
      refine ⟨115884146878100999744809049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77256097918733999829872699 115884146878100999744809049)
      ·
        refine ⟨86913110158575749808606787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115884146878100999744809049 86913110158575749808606787)
        ·
          refine ⟨130369665237863624712910181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86913110158575749808606787 130369665237863624712910181)
          ·
            refine ⟨24444312232099429633670659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130369665237863624712910181 24444312232099429633670659)
            ·
              refine ⟨36666468348149144450505989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24444312232099429633670659 36666468348149144450505989)
              ·
                refine ⟨6874962815277964584469873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36666468348149144450505989 6874962815277964584469873)
                ·
                  refine ⟨5156222111458473438352405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6874962815277964584469873 5156222111458473438352405)
                  ·
                    refine ⟨241697911474615942422769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5156222111458473438352405 241697911474615942422769)
                    ·
                      rfl

theorem cell23_1412115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 6].length) (baseStart_1412115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412115 prefixEnd_1412115 := by exact prefixLift 1412115
  have htrace : WordTrace (prefixWord ++ tailWord_1412115) baseStart_1412115 baseEnd_1412115 := by
    simpa [prefixWord, tailWord_1412115, baseEnd_1412115] using wordTrace_append hprefix tailTrace_1412115
  have hstable : (prefixWord ++ tailWord_1412115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412115).length < 2 ^ (prefixWord ++ tailWord_1412115).sum := by decide
  have hdescent : baseEnd_1412115 < baseStart_1412115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412132 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 1, 8]
def baseStart_1412132 : Nat := 118140960795 + 1412132 * 2 ^ 59
def prefixEnd_1412132 : Nat := 4983230072969 + 3 ^ 40 * 1412132 * 2
def baseEnd_1412132 : Nat := 241700821198324753585243

theorem tailTrace_1412132 : CollatzResearch.WordTrace tailWord_1412132 prefixEnd_1412132 241700821198324753585243 := by
  unfold tailWord_1412132
  simp only [CollatzResearch.WordTrace]
  refine ⟨25752342660047205894975325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34336456880062941193300433 25752342660047205894975325)
  ·
    refine ⟨9657128497517702210615747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25752342660047205894975325 9657128497517702210615747)
    ·
      refine ⟨14485692746276553315923621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9657128497517702210615747 14485692746276553315923621)
      ·
        refine ⟨2716067389926853746735679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14485692746276553315923621 2716067389926853746735679)
        ·
          refine ⟨4074101084890280620103519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2716067389926853746735679 4074101084890280620103519)
          ·
            refine ⟨6111151627335420930155279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4074101084890280620103519 6111151627335420930155279)
            ·
              refine ⟨9166727441003131395232919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6111151627335420930155279 9166727441003131395232919)
              ·
                refine ⟨13750091161504697092849379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9166727441003131395232919 13750091161504697092849379)
                ·
                  refine ⟨20625136742257045639274069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13750091161504697092849379 20625136742257045639274069)
                  ·
                    refine ⟨241700821198324753585243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20625136742257045639274069 241700821198324753585243)
                    ·
                      rfl

theorem cell23_1412132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_1412132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412132 prefixEnd_1412132 := by exact prefixLift 1412132
  have htrace : WordTrace (prefixWord ++ tailWord_1412132) baseStart_1412132 baseEnd_1412132 := by
    simpa [prefixWord, tailWord_1412132, baseEnd_1412132] using wordTrace_append hprefix tailTrace_1412132
  have hstable : (prefixWord ++ tailWord_1412132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412132).length < 2 ^ (prefixWord ++ tailWord_1412132).sum := by decide
  have hdescent : baseEnd_1412132 < baseStart_1412132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412139 : List Nat := [1, 1, 1, 1, 2, 1, 8, 1, 1, 4, 2]
def baseStart_1412139 : Nat := 118140960795 + 1412139 * 2 ^ 59
def prefixEnd_1412139 : Nat := 4983230072969 + 3 ^ 40 * 1412139 * 2
def baseEnd_1412139 : Nat := 725106057959555733368197

theorem tailTrace_1412139 : CollatzResearch.WordTrace tailWord_1412139 prefixEnd_1412139 725106057959555733368197 := by
  unfold tailWord_1412139
  simp only [CollatzResearch.WordTrace]
  refine ⟨51504940631069051985455471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34336627087379367990303647 51504940631069051985455471)
  ·
    refine ⟨77257410946603577978183207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51504940631069051985455471 77257410946603577978183207)
    ·
      refine ⟨115886116419905366967274811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77257410946603577978183207 115886116419905366967274811)
      ·
        refine ⟨173829174629858050450912217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115886116419905366967274811 173829174629858050450912217)
        ·
          refine ⟨130371880972393537838184163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173829174629858050450912217 130371880972393537838184163)
          ·
            refine ⟨195557821458590306757276245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130371880972393537838184163 195557821458590306757276245)
            ·
              refine ⟨2291693220217855157311831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 195557821458590306757276245 2291693220217855157311831)
              ·
                refine ⟨3437539830326782735967747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2291693220217855157311831 3437539830326782735967747)
                ·
                  refine ⟨5156309745490174103951621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3437539830326782735967747 5156309745490174103951621)
                  ·
                    refine ⟨966808077279407644490929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5156309745490174103951621 966808077279407644490929)
                    ·
                      refine ⟨725106057959555733368197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 966808077279407644490929 725106057959555733368197)
                      ·
                        rfl

theorem cell23_1412139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 4, 2].length) (baseStart_1412139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412139 prefixEnd_1412139 := by exact prefixLift 1412139
  have htrace : WordTrace (prefixWord ++ tailWord_1412139) baseStart_1412139 baseEnd_1412139 := by
    simpa [prefixWord, tailWord_1412139, baseEnd_1412139] using wordTrace_append hprefix tailTrace_1412139
  have hstable : (prefixWord ++ tailWord_1412139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412139).length < 2 ^ (prefixWord ++ tailWord_1412139).sum := by decide
  have hdescent : baseEnd_1412139 < baseStart_1412139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412173 : List Nat := [1, 6, 1, 1, 1, 3, 1, 1, 4, 2, 2]
def baseStart_1412173 : Nat := 118140960795 + 1412173 * 2 ^ 59
def prefixEnd_1412173 : Nat := 4983230072969 + 3 ^ 40 * 1412173 * 2
def baseEnd_1412173 : Nat := 725123516301808600343041

theorem tailTrace_1412173 : CollatzResearch.WordTrace tailWord_1412173 prefixEnd_1412173 725123516301808600343041 := by
  unfold tailWord_1412173
  simp only [CollatzResearch.WordTrace]
  refine ⟨51506180712945875792193173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34337453808630583861462115 51506180712945875792193173)
  ·
    refine ⟨2414352220919337927759055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51506180712945875792193173 2414352220919337927759055)
    ·
      refine ⟨3621528331379006891638583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2414352220919337927759055 3621528331379006891638583)
      ·
        refine ⟨5432292497068510337457875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3621528331379006891638583 5432292497068510337457875)
        ·
          refine ⟨8148438745602765506186813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5432292497068510337457875 8148438745602765506186813)
          ·
            refine ⟨3055664529601037064820055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8148438745602765506186813 3055664529601037064820055)
            ·
              refine ⟨4583496794401555597230083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3055664529601037064820055 4583496794401555597230083)
              ·
                refine ⟨6875245191602333395845125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4583496794401555597230083 6875245191602333395845125)
                ·
                  refine ⟨1289108473425437511720961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6875245191602333395845125 1289108473425437511720961)
                  ·
                    refine ⟨966831355069078133790721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1289108473425437511720961 966831355069078133790721)
                    ·
                      refine ⟨725123516301808600343041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 966831355069078133790721 725123516301808600343041)
                      ·
                        rfl

theorem cell23_1412173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_1412173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412173 prefixEnd_1412173 := by exact prefixLift 1412173
  have htrace : WordTrace (prefixWord ++ tailWord_1412173) baseStart_1412173 baseEnd_1412173 := by
    simpa [prefixWord, tailWord_1412173, baseEnd_1412173] using wordTrace_append hprefix tailTrace_1412173
  have hstable : (prefixWord ++ tailWord_1412173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412173).length < 2 ^ (prefixWord ++ tailWord_1412173).sum := by decide
  have hdescent : baseEnd_1412173 < baseStart_1412173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412175 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 5, 7]
def baseStart_1412175 : Nat := 118140960795 + 1412175 * 2 ^ 59
def prefixEnd_1412175 : Nat := 4983230072969 + 3 ^ 40 * 1412175 * 2
def baseEnd_1412175 : Nat := 241708181087705864172677

theorem tailTrace_1412175 : CollatzResearch.WordTrace tailWord_1412175 prefixEnd_1412175 241708181087705864172677 := by
  unfold tailWord_1412175
  simp only [CollatzResearch.WordTrace]
  refine ⟨51506253658938630133765979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34337502439292420089177319 51506253658938630133765979)
  ·
    refine ⟨77259380488407945200648969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51506253658938630133765979 77259380488407945200648969)
    ·
      refine ⟨57944535366305958900486727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77259380488407945200648969 57944535366305958900486727)
      ·
        refine ⟨86916803049458938350730091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57944535366305958900486727 86916803049458938350730091)
        ·
          refine ⟨130375204574188407526095137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86916803049458938350730091 130375204574188407526095137)
          ·
            refine ⟨97781403430641305644571353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130375204574188407526095137 97781403430641305644571353)
            ·
              refine ⟨73336052572980979233428515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97781403430641305644571353 73336052572980979233428515)
              ·
                refine ⟨110004078859471468850142773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73336052572980979233428515 110004078859471468850142773)
                ·
                  refine ⟨10312882393075450204700885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110004078859471468850142773 10312882393075450204700885)
                  ·
                    refine ⟨241708181087705864172677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10312882393075450204700885 241708181087705864172677)
                    ·
                      rfl

theorem cell23_1412175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 7].length) (baseStart_1412175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412175 prefixEnd_1412175 := by exact prefixLift 1412175
  have htrace : WordTrace (prefixWord ++ tailWord_1412175) baseStart_1412175 baseEnd_1412175 := by
    simpa [prefixWord, tailWord_1412175, baseEnd_1412175] using wordTrace_append hprefix tailTrace_1412175
  have hstable : (prefixWord ++ tailWord_1412175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412175).length < 2 ^ (prefixWord ++ tailWord_1412175).sum := by decide
  have hdescent : baseEnd_1412175 < baseStart_1412175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412190 : List Nat := [4, 4, 1, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_1412190 : Nat := 118140960795 + 1412190 * 2 ^ 59
def prefixEnd_1412190 : Nat := 4983230072969 + 3 ^ 40 * 1412190 * 2
def baseEnd_1412190 : Nat := 725132245472935033830463

theorem tailTrace_1412190 : CollatzResearch.WordTrace tailWord_1412190 prefixEnd_1412190 725132245472935033830463 := by
  unfold tailWord_1412190
  simp only [CollatzResearch.WordTrace]
  refine ⟨6438350094235535961945253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34337867169256191797041349 6438350094235535961945253)
  ·
    refine ⟨1207190642669162992864735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6438350094235535961945253 1207190642669162992864735)
    ·
      refine ⟨1810785964003744489297103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1207190642669162992864735 1810785964003744489297103)
      ·
        refine ⟨2716178946005616733945655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1810785964003744489297103 2716178946005616733945655)
        ·
          refine ⟨4074268419008425100918483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2716178946005616733945655 4074268419008425100918483)
          ·
            refine ⟨6111402628512637651377725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4074268419008425100918483 6111402628512637651377725)
            ·
              refine ⟨2291775985692239119266647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6111402628512637651377725 2291775985692239119266647)
              ·
                refine ⟨3437663978538358678899971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2291775985692239119266647 3437663978538358678899971)
                ·
                  refine ⟨5156495967807538018349957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3437663978538358678899971 5156495967807538018349957)
                  ·
                    refine ⟨966842993963913378440617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5156495967807538018349957 966842993963913378440617)
                    ·
                      refine ⟨725132245472935033830463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 966842993963913378440617 725132245472935033830463)
                      ·
                        rfl

theorem cell23_1412190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_1412190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412190 prefixEnd_1412190 := by exact prefixLift 1412190
  have htrace : WordTrace (prefixWord ++ tailWord_1412190) baseStart_1412190 baseEnd_1412190 := by
    simpa [prefixWord, tailWord_1412190, baseEnd_1412190] using wordTrace_append hprefix tailTrace_1412190
  have hstable : (prefixWord ++ tailWord_1412190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412190).length < 2 ^ (prefixWord ++ tailWord_1412190).sum := by decide
  have hdescent : baseEnd_1412190 < baseStart_1412190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412286 : List Nat := [4, 2, 1, 1, 3, 2, 2, 2, 6]
def baseStart_1412286 : Nat := 118140960795 + 1412286 * 2 ^ 59
def prefixEnd_1412286 : Nat := 4983230072969 + 3 ^ 40 * 1412286 * 2
def baseEnd_1412286 : Nat := 80575726623974073136669

theorem tailTrace_1412286 : CollatzResearch.WordTrace tailWord_1412286 prefixEnd_1412286 80575726623974073136669 := by
  unfold tailWord_1412286
  simp only [CollatzResearch.WordTrace]
  refine ⟨6438787770192062011382089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34340201441024330727371141 6438787770192062011382089)
  ·
    refine ⟨4829090827644046508536567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6438787770192062011382089 4829090827644046508536567)
    ·
      refine ⟨7243636241466069762804851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4829090827644046508536567 7243636241466069762804851)
      ·
        refine ⟨10865454362199104644207277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7243636241466069762804851 10865454362199104644207277)
        ·
          refine ⟨4074545385824664241577729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10865454362199104644207277 4074545385824664241577729)
          ·
            refine ⟨3055909039368498181183297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4074545385824664241577729 3055909039368498181183297)
            ·
              refine ⟨2291931779526373635887473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3055909039368498181183297 2291931779526373635887473)
              ·
                refine ⟨1718948834644780226915605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2291931779526373635887473 1718948834644780226915605)
                ·
                  refine ⟨80575726623974073136669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1718948834644780226915605 80575726623974073136669)
                  ·
                    rfl

theorem cell23_1412286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_1412286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412286 prefixEnd_1412286 := by exact prefixLift 1412286
  have htrace : WordTrace (prefixWord ++ tailWord_1412286) baseStart_1412286 baseEnd_1412286 := by
    simpa [prefixWord, tailWord_1412286, baseEnd_1412286] using wordTrace_append hprefix tailTrace_1412286
  have hstable : (prefixWord ++ tailWord_1412286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412286).length < 2 ^ (prefixWord ++ tailWord_1412286).sum := by decide
  have hdescent : baseEnd_1412286 < baseStart_1412286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412306 : List Nat := [3, 2, 2, 2, 1, 1, 2, 2, 1, 5, 2]
def baseStart_1412306 : Nat := 118140960795 + 1412306 * 2 ^ 59
def prefixEnd_1412306 : Nat := 4983230072969 + 3 ^ 40 * 1412306 * 2
def baseEnd_1412306 : Nat := 725191809228856579979929

theorem tailTrace_1412306 : CollatzResearch.WordTrace tailWord_1412306 prefixEnd_1412306 725191809228856579979929 := by
  unfold tailWord_1412306
  simp only [CollatzResearch.WordTrace]
  refine ⟨12877757905366009876696193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34340687747642693004523181 12877757905366009876696193)
  ·
    refine ⟨9658318429024507407522145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12877757905366009876696193 9658318429024507407522145)
    ·
      refine ⟨7243738821768380555641609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9658318429024507407522145 7243738821768380555641609)
      ·
        refine ⟨5432804116326285416731207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7243738821768380555641609 5432804116326285416731207)
        ·
          refine ⟨8149206174489428125096811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5432804116326285416731207 8149206174489428125096811)
          ·
            refine ⟨12223809261734142187645217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8149206174489428125096811 12223809261734142187645217)
            ·
              refine ⟨9167856946300606640733913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12223809261734142187645217 9167856946300606640733913)
              ·
                refine ⟨6875892709725454980550435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9167856946300606640733913 6875892709725454980550435)
                ·
                  refine ⟨10313839064588182470825653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6875892709725454980550435 10313839064588182470825653)
                  ·
                    refine ⟨966922412305142106639905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10313839064588182470825653 966922412305142106639905)
                    ·
                      refine ⟨725191809228856579979929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 966922412305142106639905 725191809228856579979929)
                      ·
                        rfl

theorem cell23_1412306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_1412306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412306 prefixEnd_1412306 := by exact prefixLift 1412306
  have htrace : WordTrace (prefixWord ++ tailWord_1412306) baseStart_1412306 baseEnd_1412306 := by
    simpa [prefixWord, tailWord_1412306, baseEnd_1412306] using wordTrace_append hprefix tailTrace_1412306
  have hstable : (prefixWord ++ tailWord_1412306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412306).length < 2 ^ (prefixWord ++ tailWord_1412306).sum := by decide
  have hdescent : baseEnd_1412306 < baseStart_1412306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412319 : List Nat := [1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 4]
def baseStart_1412319 : Nat := 118140960795 + 1412319 * 2 ^ 59
def prefixEnd_1412319 : Nat := 4983230072969 + 3 ^ 40 * 1412319 * 2
def baseEnd_1412319 : Nat := 725198484477365029117369

theorem tailTrace_1412319 : CollatzResearch.WordTrace tailWord_1412319 prefixEnd_1412319 725198484477365029117369 := by
  unfold tailWord_1412319
  simp only [CollatzResearch.WordTrace]
  refine ⟨51511505770416942727008011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34341003846944628484672007 51511505770416942727008011)
  ·
    refine ⟨77267258655625414090512017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51511505770416942727008011 77267258655625414090512017)
    ·
      refine ⟨57950443991719060567884013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77267258655625414090512017 57950443991719060567884013)
      ·
        refine ⟨21731416496894647712956505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57950443991719060567884013 21731416496894647712956505)
        ·
          refine ⟨16298562372670985784717379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21731416496894647712956505 16298562372670985784717379)
          ·
            refine ⟨24447843559006478677076069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16298562372670985784717379 24447843559006478677076069)
            ·
              refine ⟨4583970667313714751951763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24447843559006478677076069 4583970667313714751951763)
              ·
                refine ⟨6875956000970572127927645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4583970667313714751951763 6875956000970572127927645)
                ·
                  refine ⟨2578483500363964547972867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6875956000970572127927645 2578483500363964547972867)
                  ·
                    refine ⟨3867725250545946821959301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2578483500363964547972867 3867725250545946821959301)
                    ·
                      refine ⟨725198484477365029117369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3867725250545946821959301 725198484477365029117369)
                      ·
                        rfl

theorem cell23_1412319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_1412319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412319 prefixEnd_1412319 := by exact prefixLift 1412319
  have htrace : WordTrace (prefixWord ++ tailWord_1412319) baseStart_1412319 baseEnd_1412319 := by
    simpa [prefixWord, tailWord_1412319, baseEnd_1412319] using wordTrace_append hprefix tailTrace_1412319
  have hstable : (prefixWord ++ tailWord_1412319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412319).length < 2 ^ (prefixWord ++ tailWord_1412319).sum := by decide
  have hdescent : baseEnd_1412319 < baseStart_1412319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412330 : List Nat := [3, 1, 3, 1, 1, 4, 2, 3, 1, 1, 3]
def baseStart_1412330 : Nat := 118140960795 + 1412330 * 2 ^ 59
def prefixEnd_1412330 : Nat := 4983230072969 + 3 ^ 40 * 1412330 * 2
def baseEnd_1412330 : Nat := 725204132764564486079819

theorem tailTrace_1412330 : CollatzResearch.WordTrace tailWord_1412330 prefixEnd_1412330 725204132764564486079819 := by
  unfold tailWord_1412330
  simp only [CollatzResearch.WordTrace]
  refine ⟨12877976743344272901414611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34341271315584727737105629 12877976743344272901414611)
  ·
    refine ⟨19316965115016409352121917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12877976743344272901414611 19316965115016409352121917)
    ·
      refine ⟨7243861918131153507045719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19316965115016409352121917 7243861918131153507045719)
      ·
        refine ⟨10865792877196730260568579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7243861918131153507045719 10865792877196730260568579)
        ·
          refine ⟨16298689315795095390852869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10865792877196730260568579 16298689315795095390852869)
          ·
            refine ⟨3056004246711580385784913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16298689315795095390852869 3056004246711580385784913)
            ·
              refine ⟨2292003185033685289338685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3056004246711580385784913 2292003185033685289338685)
              ·
                refine ⟨859501194387631983502007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2292003185033685289338685 859501194387631983502007)
                ·
                  refine ⟨1289251791581447975253011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 859501194387631983502007 1289251791581447975253011)
                  ·
                    refine ⟨1933877687372171962879517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1289251791581447975253011 1933877687372171962879517)
                    ·
                      refine ⟨725204132764564486079819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1933877687372171962879517 725204132764564486079819)
                      ·
                        rfl

theorem cell23_1412330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_1412330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412330 prefixEnd_1412330 := by exact prefixLift 1412330
  have htrace : WordTrace (prefixWord ++ tailWord_1412330) baseStart_1412330 baseEnd_1412330 := by
    simpa [prefixWord, tailWord_1412330, baseEnd_1412330] using wordTrace_append hprefix tailTrace_1412330
  have hstable : (prefixWord ++ tailWord_1412330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412330).length < 2 ^ (prefixWord ++ tailWord_1412330).sum := by decide
  have hdescent : baseEnd_1412330 < baseStart_1412330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412333 : List Nat := [1, 5, 1, 2, 2, 1, 4, 1, 1, 5]
def baseStart_1412333 : Nat := 118140960795 + 1412333 * 2 ^ 59
def prefixEnd_1412333 : Nat := 4983230072969 + 3 ^ 40 * 1412333 * 2
def baseEnd_1412333 : Nat := 241735224402175991447435

theorem tailTrace_1412333 : CollatzResearch.WordTrace tailWord_1412333 prefixEnd_1412333 241735224402175991447435 := by
  unfold tailWord_1412333
  simp only [CollatzResearch.WordTrace]
  refine ⟨51512016392366223118017653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34341344261577482078678435 51512016392366223118017653)
  ·
    refine ⟨4829251536784333417314155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51512016392366223118017653 4829251536784333417314155)
    ·
      refine ⟨7243877305176500125971233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4829251536784333417314155 7243877305176500125971233)
      ·
        refine ⟨5432907978882375094478425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7243877305176500125971233 5432907978882375094478425)
        ·
          refine ⟨4074680984161781320858819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5432907978882375094478425 4074680984161781320858819)
          ·
            refine ⟨6112021476242671981288229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4074680984161781320858819 6112021476242671981288229)
            ·
              refine ⟨1146004026795500996491543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6112021476242671981288229 1146004026795500996491543)
              ·
                refine ⟨1719006040193251494737315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1146004026795500996491543 1719006040193251494737315)
                ·
                  refine ⟨2578509060289877242105973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1719006040193251494737315 2578509060289877242105973)
                  ·
                    refine ⟨241735224402175991447435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2578509060289877242105973 241735224402175991447435)
                    ·
                      rfl

theorem cell23_1412333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_1412333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412333 prefixEnd_1412333 := by exact prefixLift 1412333
  have htrace : WordTrace (prefixWord ++ tailWord_1412333) baseStart_1412333 baseEnd_1412333 := by
    simpa [prefixWord, tailWord_1412333, baseEnd_1412333] using wordTrace_append hprefix tailTrace_1412333
  have hstable : (prefixWord ++ tailWord_1412333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412333).length < 2 ^ (prefixWord ++ tailWord_1412333).sum := by decide
  have hdescent : baseEnd_1412333 < baseStart_1412333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412352 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 7]
def baseStart_1412352 : Nat := 118140960795 + 1412352 * 2 ^ 59
def prefixEnd_1412352 : Nat := 4983230072969 + 3 ^ 40 * 1412352 * 2
def baseEnd_1412352 : Nat := 725215429338963400004717

theorem tailTrace_1412352 : CollatzResearch.WordTrace tailWord_1412352 prefixEnd_1412352 725215429338963400004717 := by
  unfold tailWord_1412352
  simp only [CollatzResearch.WordTrace]
  refine ⟨25756354689648694681479655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34341806252864926241972873 25756354689648694681479655)
  ·
    refine ⟨38634532034473042022219483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25756354689648694681479655 38634532034473042022219483)
    ·
      refine ⟨57951798051709563033329225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38634532034473042022219483 57951798051709563033329225)
      ·
        refine ⟨43463848538782172274996919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57951798051709563033329225 43463848538782172274996919)
        ·
          refine ⟨65195772808173258412495379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43463848538782172274996919 65195772808173258412495379)
          ·
            refine ⟨97793659212259887618743069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65195772808173258412495379 97793659212259887618743069)
            ·
              refine ⟨36672622204597457857028651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97793659212259887618743069 36672622204597457857028651)
              ·
                refine ⟨55008933306896186785542977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36672622204597457857028651 55008933306896186785542977)
                ·
                  refine ⟨41256699980172140089157233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55008933306896186785542977 41256699980172140089157233)
                  ·
                    refine ⟨30942524985129105066867925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41256699980172140089157233 30942524985129105066867925)
                    ·
                      refine ⟨725215429338963400004717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 30942524985129105066867925 725215429338963400004717)
                      ·
                        rfl

theorem cell23_1412352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_1412352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412352 prefixEnd_1412352 := by exact prefixLift 1412352
  have htrace : WordTrace (prefixWord ++ tailWord_1412352) baseStart_1412352 baseEnd_1412352 := by
    simpa [prefixWord, tailWord_1412352, baseEnd_1412352] using wordTrace_append hprefix tailTrace_1412352
  have hstable : (prefixWord ++ tailWord_1412352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412352).length < 2 ^ (prefixWord ++ tailWord_1412352).sum := by decide
  have hdescent : baseEnd_1412352 < baseStart_1412352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412353 : List Nat := [1, 2, 4, 1, 1, 3, 1, 3, 3, 2, 2]
def baseStart_1412353 : Nat := 118140960795 + 1412353 * 2 ^ 59
def prefixEnd_1412353 : Nat := 4983230072969 + 3 ^ 40 * 1412353 * 2
def baseEnd_1412353 : Nat := 725215942819617896092213

theorem tailTrace_1412353 : CollatzResearch.WordTrace tailWord_1412353 prefixEnd_1412353 725215942819617896092213 := by
  unfold tailWord_1412353
  simp only [CollatzResearch.WordTrace]
  refine ⟨51512745852293766533745713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34341830568195844355830475 51512745852293766533745713)
  ·
    refine ⟨38634559389220324900309285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51512745852293766533745713 38634559389220324900309285)
    ·
      refine ⟨7243979885478810918807991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38634559389220324900309285 7243979885478810918807991)
      ·
        refine ⟨10865969828218216378211987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7243979885478810918807991 10865969828218216378211987)
        ·
          refine ⟨16298954742327324567317981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10865969828218216378211987 16298954742327324567317981)
          ·
            refine ⟨6112108028372746712744243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16298954742327324567317981 6112108028372746712744243)
            ·
              refine ⟨9168162042559120069116365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6112108028372746712744243 9168162042559120069116365)
              ·
                refine ⟨3438060765959670025918637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9168162042559120069116365 3438060765959670025918637)
                ·
                  refine ⟨1289272787234876259719489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3438060765959670025918637 1289272787234876259719489)
                  ·
                    refine ⟨966954590426157194789617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1289272787234876259719489 966954590426157194789617)
                    ·
                      refine ⟨725215942819617896092213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 966954590426157194789617 725215942819617896092213)
                      ·
                        rfl

theorem cell23_1412353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_1412353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412353 prefixEnd_1412353 := by exact prefixLift 1412353
  have htrace : WordTrace (prefixWord ++ tailWord_1412353) baseStart_1412353 baseEnd_1412353 := by
    simpa [prefixWord, tailWord_1412353, baseEnd_1412353] using wordTrace_append hprefix tailTrace_1412353
  have hstable : (prefixWord ++ tailWord_1412353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412353).length < 2 ^ (prefixWord ++ tailWord_1412353).sum := by decide
  have hdescent : baseEnd_1412353 < baseStart_1412353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412356 : List Nat := [2, 3, 2, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_1412356 : Nat := 118140960795 + 1412356 * 2 ^ 59
def prefixEnd_1412356 : Nat := 4983230072969 + 3 ^ 40 * 1412356 * 2
def baseEnd_1412356 : Nat := 725217483261581384354699

theorem tailTrace_1412356 : CollatzResearch.WordTrace tailWord_1412356 prefixEnd_1412356 725217483261581384354699 := by
  unfold tailWord_1412356
  simp only [CollatzResearch.WordTrace]
  refine ⟨25756427635641449023052461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34341903514188598697403281 25756427635641449023052461)
  ·
    refine ⟨9658660363365543383644673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25756427635641449023052461 9658660363365543383644673)
    ·
      refine ⟨7243995272524157537733505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9658660363365543383644673 7243995272524157537733505)
      ·
        refine ⟨5432996454393118153300129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7243995272524157537733505 5432996454393118153300129)
        ·
          refine ⟨4074747340794838614975097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5432996454393118153300129 4074747340794838614975097)
          ·
            refine ⟨3056060505596128961231323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4074747340794838614975097 3056060505596128961231323)
            ·
              refine ⟨4584090758394193441846985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3056060505596128961231323 4584090758394193441846985)
              ·
                refine ⟨3438068068795645081385239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4584090758394193441846985 3438068068795645081385239)
                ·
                  refine ⟨5157102103193467622077859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3438068068795645081385239 5157102103193467622077859)
                  ·
                    refine ⟨7735653154790201433116789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5157102103193467622077859 7735653154790201433116789)
                    ·
                      refine ⟨725217483261581384354699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7735653154790201433116789 725217483261581384354699)
                      ·
                        rfl

theorem cell23_1412356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_1412356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412356 prefixEnd_1412356 := by exact prefixLift 1412356
  have htrace : WordTrace (prefixWord ++ tailWord_1412356) baseStart_1412356 baseEnd_1412356 := by
    simpa [prefixWord, tailWord_1412356, baseEnd_1412356] using wordTrace_append hprefix tailTrace_1412356
  have hstable : (prefixWord ++ tailWord_1412356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412356).length < 2 ^ (prefixWord ++ tailWord_1412356).sum := by decide
  have hdescent : baseEnd_1412356 < baseStart_1412356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412363 : List Nat := [1, 1, 1, 1, 5, 4, 3, 1, 2, 4]
def baseStart_1412363 : Nat := 118140960795 + 1412363 * 2 ^ 59
def prefixEnd_1412363 : Nat := 4983230072969 + 3 ^ 40 * 1412363 * 2
def baseEnd_1412363 : Nat := 241740359208720952322389

theorem tailTrace_1412363 : CollatzResearch.WordTrace tailWord_1412363 prefixEnd_1412363 241740359208720952322389 := by
  unfold tailWord_1412363
  simp only [CollatzResearch.WordTrace]
  refine ⟨51513110582257538241609743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34342073721505025494406495 51513110582257538241609743)
  ·
    refine ⟨77269665873386307362414615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51513110582257538241609743 77269665873386307362414615)
    ·
      refine ⟨115904498810079461043621923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77269665873386307362414615 115904498810079461043621923)
      ·
        refine ⟨173856748215119191565432885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115904498810079461043621923 173856748215119191565432885)
        ·
          refine ⟨16299070145167424209259333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 173856748215119191565432885 16299070145167424209259333)
          ·
            refine ⟨3056075652218892039236125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16299070145167424209259333 3056075652218892039236125)
            ·
              refine ⟨1146028369582084514713547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3056075652218892039236125 1146028369582084514713547)
              ·
                refine ⟨1719042554373126772070321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1146028369582084514713547 1719042554373126772070321)
                ·
                  refine ⟨1289281915779845079052741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1719042554373126772070321 1289281915779845079052741)
                  ·
                    refine ⟨241740359208720952322389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1289281915779845079052741 241740359208720952322389)
                    ·
                      rfl

theorem cell23_1412363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 2, 4].length) (baseStart_1412363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412363 prefixEnd_1412363 := by exact prefixLift 1412363
  have htrace : WordTrace (prefixWord ++ tailWord_1412363) baseStart_1412363 baseEnd_1412363 := by
    simpa [prefixWord, tailWord_1412363, baseEnd_1412363] using wordTrace_append hprefix tailTrace_1412363
  have hstable : (prefixWord ++ tailWord_1412363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412363).length < 2 ^ (prefixWord ++ tailWord_1412363).sum := by decide
  have hdescent : baseEnd_1412363 < baseStart_1412363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412366 : List Nat := [4, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4]
def baseStart_1412366 : Nat := 118140960795 + 1412366 * 2 ^ 59
def prefixEnd_1412366 : Nat := 4983230072969 + 3 ^ 40 * 1412366 * 2
def baseEnd_1412366 : Nat := 725222618068126345229653

theorem tailTrace_1412366 : CollatzResearch.WordTrace tailWord_1412366 prefixEnd_1412366 725222618068126345229653 := by
  unfold tailWord_1412366
  simp only [CollatzResearch.WordTrace]
  refine ⟨6439152500155833719246119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34342146667497779835979301 6439152500155833719246119)
  ·
    refine ⟨9658728750233750578869179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6439152500155833719246119 9658728750233750578869179)
    ·
      refine ⟨14488093125350625868303769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9658728750233750578869179 14488093125350625868303769)
      ·
        refine ⟨10866069844012969401227827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14488093125350625868303769 10866069844012969401227827)
        ·
          refine ⟨16299104766019454101841741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10866069844012969401227827 16299104766019454101841741)
          ·
            refine ⟨6112164287257295288190653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16299104766019454101841741 6112164287257295288190653)
            ·
              refine ⟨2292061607721485733071495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6112164287257295288190653 2292061607721485733071495)
              ·
                refine ⟨3438092411582228599607243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2292061607721485733071495 3438092411582228599607243)
                ·
                  refine ⟨5157138617373342899410865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3438092411582228599607243 5157138617373342899410865)
                  ·
                    refine ⟨3867853963030007174558149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5157138617373342899410865 3867853963030007174558149)
                    ·
                      refine ⟨725222618068126345229653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3867853963030007174558149 725222618068126345229653)
                      ·
                        rfl

theorem cell23_1412366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_1412366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412366 prefixEnd_1412366 := by exact prefixLift 1412366
  have htrace : WordTrace (prefixWord ++ tailWord_1412366) baseStart_1412366 baseEnd_1412366 := by
    simpa [prefixWord, tailWord_1412366, baseEnd_1412366] using wordTrace_append hprefix tailTrace_1412366
  have hstable : (prefixWord ++ tailWord_1412366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412366).length < 2 ^ (prefixWord ++ tailWord_1412366).sum := by decide
  have hdescent : baseEnd_1412366 < baseStart_1412366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412376 : List Nat := [2, 1, 2, 3, 1, 5, 2, 7]
def baseStart_1412376 : Nat := 118140960795 + 1412376 * 2 ^ 59
def prefixEnd_1412376 : Nat := 4983230072969 + 3 ^ 40 * 1412376 * 2
def baseEnd_1412376 : Nat := 26860287143506344670541

theorem tailTrace_1412376 : CollatzResearch.WordTrace tailWord_1412376 prefixEnd_1412376 26860287143506344670541 := by
  unfold tailWord_1412376
  simp only [CollatzResearch.WordTrace]
  refine ⟨25756792365605220730916491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34342389820806960974555321 25756792365605220730916491)
  ·
    refine ⟨38635188548407831096374737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25756792365605220730916491 38635188548407831096374737)
    ·
      refine ⟨28976391411305873322281053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38635188548407831096374737 28976391411305873322281053)
      ·
        refine ⟨10866146779239702495855395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28976391411305873322281053 10866146779239702495855395)
        ·
          refine ⟨16299220168859553743783093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10866146779239702495855395 16299220168859553743783093)
          ·
            refine ⟨1528051890830583163479665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16299220168859553743783093 1528051890830583163479665)
            ·
              refine ⟨1146038918122937372609749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1528051890830583163479665 1146038918122937372609749)
              ·
                refine ⟨26860287143506344670541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1146038918122937372609749 26860287143506344670541)
                ·
                  rfl

theorem cell23_1412376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 7].length) (baseStart_1412376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412376 prefixEnd_1412376 := by exact prefixLift 1412376
  have htrace : WordTrace (prefixWord ++ tailWord_1412376) baseStart_1412376 baseEnd_1412376 := by
    simpa [prefixWord, tailWord_1412376, baseEnd_1412376] using wordTrace_append hprefix tailTrace_1412376
  have hstable : (prefixWord ++ tailWord_1412376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412376).length < 2 ^ (prefixWord ++ tailWord_1412376).sum := by decide
  have hdescent : baseEnd_1412376 < baseStart_1412376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412387 : List Nat := [1, 1, 1, 4, 2, 5, 1, 3, 1, 2, 2]
def baseStart_1412387 : Nat := 118140960795 + 1412387 * 2 ^ 59
def prefixEnd_1412387 : Nat := 4983230072969 + 3 ^ 40 * 1412387 * 2
def baseEnd_1412387 : Nat := 725233401161870763067057

theorem tailTrace_1412387 : CollatzResearch.WordTrace tailWord_1412387 prefixEnd_1412387 725233401161870763067057 := by
  unfold tailWord_1412387
  simp only [CollatzResearch.WordTrace]
  refine ⟨51513985934170590340483415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34342657289447060226988943 51513985934170590340483415)
  ·
    refine ⟨77270978901255885510725123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51513985934170590340483415 77270978901255885510725123)
    ·
      refine ⟨115906468351883828266087685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77270978901255885510725123 115906468351883828266087685)
      ·
        refine ⟨21732462815978217799891441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115906468351883828266087685 21732462815978217799891441)
        ·
          refine ⟨16299347111983663349918581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21732462815978217799891441 16299347111983663349918581)
          ·
            refine ⟨1528063791748468439054867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16299347111983663349918581 1528063791748468439054867)
            ·
              refine ⟨2292095687622702658582301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1528063791748468439054867 2292095687622702658582301)
              ·
                refine ⟨859535882858513496968363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2292095687622702658582301 859535882858513496968363)
                ·
                  refine ⟨1289303824287770245452545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 859535882858513496968363 1289303824287770245452545)
                  ·
                    refine ⟨966977868215827684089409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1289303824287770245452545 966977868215827684089409)
                    ·
                      refine ⟨725233401161870763067057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 966977868215827684089409 725233401161870763067057)
                      ·
                        rfl

theorem cell23_1412387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 1, 2, 2].length) (baseStart_1412387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412387 prefixEnd_1412387 := by exact prefixLift 1412387
  have htrace : WordTrace (prefixWord ++ tailWord_1412387) baseStart_1412387 baseEnd_1412387 := by
    simpa [prefixWord, tailWord_1412387, baseEnd_1412387] using wordTrace_append hprefix tailTrace_1412387
  have hstable : (prefixWord ++ tailWord_1412387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412387).length < 2 ^ (prefixWord ++ tailWord_1412387).sum := by decide
  have hdescent : baseEnd_1412387 < baseStart_1412387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412396 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 5, 3, 2]
def baseStart_1412396 : Nat := 118140960795 + 1412396 * 2 ^ 59
def prefixEnd_1412396 : Nat := 4983230072969 + 3 ^ 40 * 1412396 * 2
def baseEnd_1412396 : Nat := 725238022487761227854515

theorem tailTrace_1412396 : CollatzResearch.WordTrace tailWord_1412396 prefixEnd_1412396 725238022487761227854515 := by
  unfold tailWord_1412396
  simp only [CollatzResearch.WordTrace]
  refine ⟨25757157095568992438780521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34342876127425323251707361 25757157095568992438780521)
  ·
    refine ⟨19317867821676744329085391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25757157095568992438780521 19317867821676744329085391)
    ·
      refine ⟨28976801732515116493628087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19317867821676744329085391 28976801732515116493628087)
      ·
        refine ⟨43465202598772674740442131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28976801732515116493628087 43465202598772674740442131)
        ·
          refine ⟨65197803898159012110663197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43465202598772674740442131 65197803898159012110663197)
          ·
            refine ⟨24449176461809629541498699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65197803898159012110663197 24449176461809629541498699)
            ·
              refine ⟨36673764692714444312248049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24449176461809629541498699 36673764692714444312248049)
              ·
                refine ⟨27505323519535833234186037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36673764692714444312248049 27505323519535833234186037)
                ·
                  refine ⟨2578624079956484365704941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27505323519535833234186037 2578624079956484365704941)
                  ·
                    refine ⟨966984029983681637139353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2578624079956484365704941 966984029983681637139353)
                    ·
                      refine ⟨725238022487761227854515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 966984029983681637139353 725238022487761227854515)
                      ·
                        rfl

theorem cell23_1412396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 3, 2].length) (baseStart_1412396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412396 prefixEnd_1412396 := by exact prefixLift 1412396
  have htrace : WordTrace (prefixWord ++ tailWord_1412396) baseStart_1412396 baseEnd_1412396 := by
    simpa [prefixWord, tailWord_1412396, baseEnd_1412396] using wordTrace_append hprefix tailTrace_1412396
  have hstable : (prefixWord ++ tailWord_1412396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412396).length < 2 ^ (prefixWord ++ tailWord_1412396).sum := by decide
  have hdescent : baseEnd_1412396 < baseStart_1412396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412404 : List Nat := [2, 5, 1, 1, 1, 1, 5, 2, 1, 2, 2]
def baseStart_1412404 : Nat := 118140960795 + 1412404 * 2 ^ 59
def prefixEnd_1412404 : Nat := 4983230072969 + 3 ^ 40 * 1412404 * 2
def baseEnd_1412404 : Nat := 725242130332997196554479

theorem tailTrace_1412404 : CollatzResearch.WordTrace tailWord_1412404 prefixEnd_1412404 725242130332997196554479 := by
  unfold tailWord_1412404
  simp only [CollatzResearch.WordTrace]
  refine ⟨25757302987554501121926133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34343070650072668162568177 25757302987554501121926133)
  ·
    refine ⟨2414747155083234480180575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25757302987554501121926133 2414747155083234480180575)
    ·
      refine ⟨3622120732624851720270863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2414747155083234480180575 3622120732624851720270863)
      ·
        refine ⟨5433181098937277580406295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3622120732624851720270863 5433181098937277580406295)
        ·
          refine ⟨8149771648405916370609443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5433181098937277580406295 8149771648405916370609443)
          ·
            refine ⟨12224657472608874555914165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8149771648405916370609443 12224657472608874555914165)
            ·
              refine ⟨1146061638057081989616953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12224657472608874555914165 1146061638057081989616953)
              ·
                refine ⟨859546228542811492212715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1146061638057081989616953 859546228542811492212715)
                ·
                  refine ⟨1289319342814217238319073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 859546228542811492212715 1289319342814217238319073)
                  ·
                    refine ⟨966989507110662928739305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1289319342814217238319073 966989507110662928739305)
                    ·
                      refine ⟨725242130332997196554479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 966989507110662928739305 725242130332997196554479)
                      ·
                        rfl

theorem cell23_1412404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_1412404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412404 prefixEnd_1412404 := by exact prefixLift 1412404
  have htrace : WordTrace (prefixWord ++ tailWord_1412404) baseStart_1412404 baseEnd_1412404 := by
    simpa [prefixWord, tailWord_1412404, baseEnd_1412404] using wordTrace_append hprefix tailTrace_1412404
  have hstable : (prefixWord ++ tailWord_1412404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412404).length < 2 ^ (prefixWord ++ tailWord_1412404).sum := by decide
  have hdescent : baseEnd_1412404 < baseStart_1412404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412426 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 5, 4, 2]
def baseStart_1412426 : Nat := 118140960795 + 1412426 * 2 ^ 59
def prefixEnd_1412426 : Nat := 4983230072969 + 3 ^ 40 * 1412426 * 2
def baseEnd_1412426 : Nat := 725253426907396110479377

theorem tailTrace_1412426 : CollatzResearch.WordTrace tailWord_1412426 prefixEnd_1412426 725253426907396110479377 := by
  unfold tailWord_1412426
  simp only [CollatzResearch.WordTrace]
  refine ⟨12878852095257325000288283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34343605587352866667435421 12878852095257325000288283)
  ·
    refine ⟨19318278142885987500432425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12878852095257325000288283 19318278142885987500432425)
    ·
      refine ⟨14488708607164490625324319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19318278142885987500432425 14488708607164490625324319)
      ·
        refine ⟨21733062910746735937986479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14488708607164490625324319 21733062910746735937986479)
        ·
          refine ⟨32599594366120103906979719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21733062910746735937986479 32599594366120103906979719)
          ·
            refine ⟨48899391549180155860469579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32599594366120103906979719 48899391549180155860469579)
            ·
              refine ⟨73349087323770233790704369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48899391549180155860469579 73349087323770233790704369)
              ·
                refine ⟨55011815492827675343028277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73349087323770233790704369 55011815492827675343028277)
                ·
                  refine ⟨5157357702452594563408901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55011815492827675343028277 5157357702452594563408901)
                  ·
                    refine ⟨967004569209861480639169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5157357702452594563408901 967004569209861480639169)
                    ·
                      refine ⟨725253426907396110479377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 967004569209861480639169 725253426907396110479377)
                      ·
                        rfl

theorem cell23_1412426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 5, 4, 2].length) (baseStart_1412426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412426 prefixEnd_1412426 := by exact prefixLift 1412426
  have htrace : WordTrace (prefixWord ++ tailWord_1412426) baseStart_1412426 baseEnd_1412426 := by
    simpa [prefixWord, tailWord_1412426, baseEnd_1412426] using wordTrace_append hprefix tailTrace_1412426
  have hstable : (prefixWord ++ tailWord_1412426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412426).length < 2 ^ (prefixWord ++ tailWord_1412426).sum := by decide
  have hdescent : baseEnd_1412426 < baseStart_1412426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412460 : List Nat := [2, 2, 1, 1, 5, 1, 1, 4, 2, 2, 2]
def baseStart_1412460 : Nat := 118140960795 + 1412460 * 2 ^ 59
def prefixEnd_1412460 : Nat := 4983230072969 + 3 ^ 40 * 1412460 * 2
def baseEnd_1412460 : Nat := 725270885249648977454221

theorem tailTrace_1412460 : CollatzResearch.WordTrace tailWord_1412460 prefixEnd_1412460 725270885249648977454221 := by
  unfold tailWord_1412460
  simp only [CollatzResearch.WordTrace]
  refine ⟨25758324231453061903945417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34344432308604082538593889 25758324231453061903945417)
  ·
    refine ⟨19318743173589796427959063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25758324231453061903945417 19318743173589796427959063)
    ·
      refine ⟨28978114760384694641938595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19318743173589796427959063 28978114760384694641938595)
      ·
        refine ⟨43467172140577041962907893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28978114760384694641938595 43467172140577041962907893)
        ·
          refine ⟨4075047388179097684022615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43467172140577041962907893 4075047388179097684022615)
          ·
            refine ⟨6112571082268646526033923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4075047388179097684022615 6112571082268646526033923)
            ·
              refine ⟨9168856623402969789050885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6112571082268646526033923 9168856623402969789050885)
              ·
                refine ⟨1719160616888056835447041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9168856623402969789050885 1719160616888056835447041)
                ·
                  refine ⟨1289370462666042626585281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1719160616888056835447041 1289370462666042626585281)
                  ·
                    refine ⟨967027846999531969938961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1289370462666042626585281 967027846999531969938961)
                    ·
                      refine ⟨725270885249648977454221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 967027846999531969938961 725270885249648977454221)
                      ·
                        rfl

theorem cell23_1412460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 2, 2].length) (baseStart_1412460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412460 prefixEnd_1412460 := by exact prefixLift 1412460
  have htrace : WordTrace (prefixWord ++ tailWord_1412460) baseStart_1412460 baseEnd_1412460 := by
    simpa [prefixWord, tailWord_1412460, baseEnd_1412460] using wordTrace_append hprefix tailTrace_1412460
  have hstable : (prefixWord ++ tailWord_1412460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412460).length < 2 ^ (prefixWord ++ tailWord_1412460).sum := by decide
  have hdescent : baseEnd_1412460 < baseStart_1412460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412476 : List Nat := [2, 2, 2, 1, 1, 1, 5, 1, 2, 3, 3]
def baseStart_1412476 : Nat := 118140960795 + 1412476 * 2 ^ 59
def prefixEnd_1412476 : Nat := 4983230072969 + 3 ^ 40 * 1412476 * 2
def baseEnd_1412476 : Nat := 725279100940120914854147

theorem tailTrace_1412476 : CollatzResearch.WordTrace tailWord_1412476 prefixEnd_1412476 725279100940120914854147 := by
  unfold tailWord_1412476
  simp only [CollatzResearch.WordTrace]
  refine ⟨25758616015424079270236641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34344821353898772360315521 25758616015424079270236641)
  ·
    refine ⟨19318962011568059452677481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25758616015424079270236641 19318962011568059452677481)
    ·
      refine ⟨14489221508676044589508111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19318962011568059452677481 14489221508676044589508111)
      ·
        refine ⟨21733832263014066884262167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14489221508676044589508111 21733832263014066884262167)
        ·
          refine ⟨32600748394521100326393251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21733832263014066884262167 32600748394521100326393251)
          ·
            refine ⟨48901122591781650489589877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32600748394521100326393251 48901122591781650489589877)
            ·
              refine ⟨4584480242979529733399051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48901122591781650489589877 4584480242979529733399051)
              ·
                refine ⟨6876720364469294600098577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4584480242979529733399051 6876720364469294600098577)
                ·
                  refine ⟨5157540273351970950073933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6876720364469294600098577 5157540273351970950073933)
                  ·
                    refine ⟨1934077602506989106277725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5157540273351970950073933 1934077602506989106277725)
                    ·
                      refine ⟨725279100940120914854147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1934077602506989106277725 725279100940120914854147)
                      ·
                        rfl

theorem cell23_1412476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_1412476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412476 prefixEnd_1412476 := by exact prefixLift 1412476
  have htrace : WordTrace (prefixWord ++ tailWord_1412476) baseStart_1412476 baseEnd_1412476 := by
    simpa [prefixWord, tailWord_1412476, baseEnd_1412476] using wordTrace_append hprefix tailTrace_1412476
  have hstable : (prefixWord ++ tailWord_1412476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412476).length < 2 ^ (prefixWord ++ tailWord_1412476).sum := by decide
  have hdescent : baseEnd_1412476 < baseStart_1412476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412500 : List Nat := [2, 4, 2, 1, 2, 2, 2, 3, 5]
def baseStart_1412500 : Nat := 118140960795 + 1412500 * 2 ^ 59
def prefixEnd_1412500 : Nat := 4983230072969 + 3 ^ 40 * 1412500 * 2
def baseEnd_1412500 : Nat := 80587936052869868994893

theorem tailTrace_1412500 : CollatzResearch.WordTrace tailWord_1412500 prefixEnd_1412500 80587936052869868994893 := by
  unfold tailWord_1412500
  simp only [CollatzResearch.WordTrace]
  refine ⟨25759053691380605319673477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34345404921840807092897969 25759053691380605319673477)
  ·
    refine ⟨4829822567133863497438777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25759053691380605319673477 4829822567133863497438777)
    ·
      refine ⟨3622366925350397623079083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4829822567133863497438777 3622366925350397623079083)
      ·
        refine ⟨5433550388025596434618625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3622366925350397623079083 5433550388025596434618625)
        ·
          refine ⟨4075162791019197325963969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5433550388025596434618625 4075162791019197325963969)
          ·
            refine ⟨3056372093264397994472977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4075162791019197325963969 3056372093264397994472977)
            ·
              refine ⟨2292279069948298495854733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3056372093264397994472977 2292279069948298495854733)
              ·
                refine ⟨859604651230611935945525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2292279069948298495854733 859604651230611935945525)
                ·
                  refine ⟨80587936052869868994893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 859604651230611935945525 80587936052869868994893)
                  ·
                    rfl

theorem cell23_1412500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_1412500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412500 prefixEnd_1412500 := by exact prefixLift 1412500
  have htrace : WordTrace (prefixWord ++ tailWord_1412500) baseStart_1412500 baseEnd_1412500 := by
    simpa [prefixWord, tailWord_1412500, baseEnd_1412500] using wordTrace_append hprefix tailTrace_1412500
  have hstable : (prefixWord ++ tailWord_1412500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412500).length < 2 ^ (prefixWord ++ tailWord_1412500).sum := by decide
  have hdescent : baseEnd_1412500 < baseStart_1412500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412516 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 4, 1, 4]
def baseStart_1412516 : Nat := 118140960795 + 1412516 * 2 ^ 59
def prefixEnd_1412516 : Nat := 4983230072969 + 3 ^ 40 * 1412516 * 2
def baseEnd_1412516 : Nat := 725299640166300758353963

theorem tailTrace_1412516 : CollatzResearch.WordTrace tailWord_1412516 prefixEnd_1412516 725299640166300758353963 := by
  unfold tailWord_1412516
  simp only [CollatzResearch.WordTrace]
  refine ⟨25759345475351622685964701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34345793967135496914619601 25759345475351622685964701)
  ·
    refine ⟨9659754553256858507236763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25759345475351622685964701 9659754553256858507236763)
    ·
      refine ⟨14489631829885287760855145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9659754553256858507236763 14489631829885287760855145)
      ·
        refine ⟨10867223872413965820641359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14489631829885287760855145 10867223872413965820641359)
        ·
          refine ⟨16300835808620948730962039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10867223872413965820641359 16300835808620948730962039)
          ·
            refine ⟨24451253712931423096443059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16300835808620948730962039 24451253712931423096443059)
            ·
              refine ⟨36676880569397134644664589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24451253712931423096443059 36676880569397134644664589)
              ·
                refine ⟨13753830213523925491749221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36676880569397134644664589 13753830213523925491749221)
                ·
                  refine ⟨2578843165035736029702979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13753830213523925491749221 2578843165035736029702979)
                  ·
                    refine ⟨3868264747553604044554469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2578843165035736029702979 3868264747553604044554469)
                    ·
                      refine ⟨725299640166300758353963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3868264747553604044554469 725299640166300758353963)
                      ·
                        rfl

theorem cell23_1412516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_1412516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412516 prefixEnd_1412516 := by exact prefixLift 1412516
  have htrace : WordTrace (prefixWord ++ tailWord_1412516) baseStart_1412516 baseEnd_1412516 := by
    simpa [prefixWord, tailWord_1412516, baseEnd_1412516] using wordTrace_append hprefix tailTrace_1412516
  have hstable : (prefixWord ++ tailWord_1412516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412516).length < 2 ^ (prefixWord ++ tailWord_1412516).sum := by decide
  have hdescent : baseEnd_1412516 < baseStart_1412516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412536 : List Nat := [2, 1, 2, 1, 2, 2, 3, 2, 1, 4, 3]
def baseStart_1412536 : Nat := 118140960795 + 1412536 * 2 ^ 59
def prefixEnd_1412536 : Nat := 4983230072969 + 3 ^ 40 * 1412536 * 2
def baseEnd_1412536 : Nat := 725309909779390680103871

theorem tailTrace_1412536 : CollatzResearch.WordTrace tailWord_1412536 prefixEnd_1412536 725309909779390680103871 := by
  unfold tailWord_1412536
  simp only [CollatzResearch.WordTrace]
  refine ⟨25759710205315394393828731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34346280273753859191771641 25759710205315394393828731)
  ·
    refine ⟨38639565307973091590743097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25759710205315394393828731 38639565307973091590743097)
    ·
      refine ⟨28979673980979818693057323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38639565307973091590743097 28979673980979818693057323)
      ·
        refine ⟨43469510971469728039585985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28979673980979818693057323 43469510971469728039585985)
        ·
          refine ⟨32602133228602296029689489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43469510971469728039585985 32602133228602296029689489)
          ·
            refine ⟨24451599921451722022267117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32602133228602296029689489 24451599921451722022267117)
            ·
              refine ⟨9169349970544395758350169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24451599921451722022267117 9169349970544395758350169)
              ·
                refine ⟨6877012477908296818762627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9169349970544395758350169 6877012477908296818762627)
                ·
                  refine ⟨10315518716862445228143941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6877012477908296818762627 10315518716862445228143941)
                  ·
                    refine ⟨1934159759411708480276989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10315518716862445228143941 1934159759411708480276989)
                    ·
                      refine ⟨725309909779390680103871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1934159759411708480276989 725309909779390680103871)
                      ·
                        rfl

theorem cell23_1412536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 1, 4, 3].length) (baseStart_1412536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412536 prefixEnd_1412536 := by exact prefixLift 1412536
  have htrace : WordTrace (prefixWord ++ tailWord_1412536) baseStart_1412536 baseEnd_1412536 := by
    simpa [prefixWord, tailWord_1412536, baseEnd_1412536] using wordTrace_append hprefix tailTrace_1412536
  have hstable : (prefixWord ++ tailWord_1412536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412536).length < 2 ^ (prefixWord ++ tailWord_1412536).sum := by decide
  have hdescent : baseEnd_1412536 < baseStart_1412536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412549 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 9]
def baseStart_1412549 : Nat := 118140960795 + 1412549 * 2 ^ 59
def prefixEnd_1412549 : Nat := 4983230072969 + 3 ^ 40 * 1412549 * 2
def baseEnd_1412549 : Nat := 725316585027899129241311

theorem tailTrace_1412549 : CollatzResearch.WordTrace tailWord_1412549 prefixEnd_1412549 725316585027899129241311 := by
  unfold tailWord_1412549
  simp only [CollatzResearch.WordTrace]
  refine ⟨51519894559583692007880701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34346596373055794671920467 51519894559583692007880701)
  ·
    refine ⟨19319960459843884502955263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51519894559583692007880701 19319960459843884502955263)
    ·
      refine ⟨28979940689765826754432895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19319960459843884502955263 28979940689765826754432895)
      ·
        refine ⟨43469911034648740131649343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28979940689765826754432895 43469911034648740131649343)
        ·
          refine ⟨65204866551973110197474015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43469911034648740131649343 65204866551973110197474015)
          ·
            refine ⟨97807299827959665296211023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65204866551973110197474015 97807299827959665296211023)
            ·
              refine ⟨146710949741939497944316535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97807299827959665296211023 146710949741939497944316535)
              ·
                refine ⟨220066424612909246916474803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146710949741939497944316535 220066424612909246916474803)
                ·
                  refine ⟨330099636919363870374712205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220066424612909246916474803 330099636919363870374712205)
                  ·
                    refine ⟨123787363844761451390517077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 330099636919363870374712205 123787363844761451390517077)
                    ·
                      refine ⟨725316585027899129241311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 123787363844761451390517077 725316585027899129241311)
                      ·
                        rfl

theorem cell23_1412549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_1412549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412549 prefixEnd_1412549 := by exact prefixLift 1412549
  have htrace : WordTrace (prefixWord ++ tailWord_1412549) baseStart_1412549 baseEnd_1412549 := by
    simpa [prefixWord, tailWord_1412549, baseEnd_1412549] using wordTrace_append hprefix tailTrace_1412549
  have hstable : (prefixWord ++ tailWord_1412549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412549).length < 2 ^ (prefixWord ++ tailWord_1412549).sum := by decide
  have hdescent : baseEnd_1412549 < baseStart_1412549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412556 : List Nat := [2, 2, 1, 4, 2, 1, 1, 2, 8]
def baseStart_1412556 : Nat := 118140960795 + 1412556 * 2 ^ 59
def prefixEnd_1412556 : Nat := 4983230072969 + 3 ^ 40 * 1412556 * 2
def baseEnd_1412556 : Nat := 80591131043608955761531

theorem tailTrace_1412556 : CollatzResearch.WordTrace tailWord_1412556 prefixEnd_1412556 80591131043608955761531 := by
  unfold tailWord_1412556
  simp only [CollatzResearch.WordTrace]
  refine ⟨25760074935279166101692761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34346766580372221468923681 25760074935279166101692761)
  ·
    refine ⟨19320056201459374576269571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25760074935279166101692761 19320056201459374576269571)
    ·
      refine ⟨28980084302189061864404357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19320056201459374576269571 28980084302189061864404357)
      ·
        refine ⟨5433765806660449099575817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28980084302189061864404357 5433765806660449099575817)
        ·
          refine ⟨4075324354995336824681863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5433765806660449099575817 4075324354995336824681863)
          ·
            refine ⟨6112986532493005237022795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4075324354995336824681863 6112986532493005237022795)
            ·
              refine ⟨9169479798739507855534193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6112986532493005237022795 9169479798739507855534193)
              ·
                refine ⟨6877109849054630891650645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9169479798739507855534193 6877109849054630891650645)
                ·
                  refine ⟨80591131043608955761531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6877109849054630891650645 80591131043608955761531)
                  ·
                    rfl

theorem cell23_1412556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 8].length) (baseStart_1412556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412556 prefixEnd_1412556 := by exact prefixLift 1412556
  have htrace : WordTrace (prefixWord ++ tailWord_1412556) baseStart_1412556 baseEnd_1412556 := by
    simpa [prefixWord, tailWord_1412556, baseEnd_1412556] using wordTrace_append hprefix tailTrace_1412556
  have hstable : (prefixWord ++ tailWord_1412556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412556).length < 2 ^ (prefixWord ++ tailWord_1412556).sum := by decide
  have hdescent : baseEnd_1412556 < baseStart_1412556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412577 : List Nat := [1, 2, 3, 1, 2, 4, 3, 2, 1, 4]
def baseStart_1412577 : Nat := 118140960795 + 1412577 * 2 ^ 59
def prefixEnd_1412577 : Nat := 4983230072969 + 3 ^ 40 * 1412577 * 2
def baseEnd_1412577 : Nat := 241776987495408339897061

theorem tailTrace_1412577 : CollatzResearch.WordTrace tailWord_1412577 prefixEnd_1412577 241776987495408339897061 := by
  unfold tailWord_1412577
  simp only [CollatzResearch.WordTrace]
  refine ⟨51520915803482252789899985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34347277202321501859933323 51520915803482252789899985)
  ·
    refine ⟨38640686852611689592424989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51520915803482252789899985 38640686852611689592424989)
    ·
      refine ⟨14490257569729383597159371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38640686852611689592424989 14490257569729383597159371)
      ·
        refine ⟨21735386354594075395739057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14490257569729383597159371 21735386354594075395739057)
        ·
          refine ⟨16301539765945556546804293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21735386354594075395739057 16301539765945556546804293)
          ·
            refine ⟨3056538706114791852525805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16301539765945556546804293 3056538706114791852525805)
            ·
              refine ⟨1146202014793046944697177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3056538706114791852525805 1146202014793046944697177)
              ·
                refine ⟨859651511094785208522883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1146202014793046944697177 859651511094785208522883)
                ·
                  refine ⟨1289477266642177812784325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 859651511094785208522883 1289477266642177812784325)
                  ·
                    refine ⟨241776987495408339897061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1289477266642177812784325 241776987495408339897061)
                    ·
                      rfl

theorem cell23_1412577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_1412577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412577 prefixEnd_1412577 := by exact prefixLift 1412577
  have htrace : WordTrace (prefixWord ++ tailWord_1412577) baseStart_1412577 baseEnd_1412577 := by
    simpa [prefixWord, tailWord_1412577, baseEnd_1412577] using wordTrace_append hprefix tailTrace_1412577
  have hstable : (prefixWord ++ tailWord_1412577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412577).length < 2 ^ (prefixWord ++ tailWord_1412577).sum := by decide
  have hdescent : baseEnd_1412577 < baseStart_1412577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412616 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 3, 6]
def baseStart_1412616 : Nat := 118140960795 + 1412616 * 2 ^ 59
def prefixEnd_1412616 : Nat := 4983230072969 + 3 ^ 40 * 1412616 * 2
def baseEnd_1412616 : Nat := 241783662743916789034501

theorem tailTrace_1412616 : CollatzResearch.WordTrace tailWord_1412616 prefixEnd_1412616 241783662743916789034501 := by
  unfold tailWord_1412616
  simp only [CollatzResearch.WordTrace]
  refine ⟨25761169125170481225284851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34348225500227308300379801 25761169125170481225284851)
  ·
    refine ⟨38641753687755721837927277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25761169125170481225284851 38641753687755721837927277)
    ·
      refine ⟨14490657632908395689222729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38641753687755721837927277 14490657632908395689222729)
      ·
        refine ⟨10867993224681296766917047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14490657632908395689222729 10867993224681296766917047)
        ·
          refine ⟨16301989837021945150375571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10867993224681296766917047 16301989837021945150375571)
          ·
            refine ⟨24452984755532917725563357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16301989837021945150375571 24452984755532917725563357)
            ·
              refine ⟨9169869283324844147086259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24452984755532917725563357 9169869283324844147086259)
              ·
                refine ⟨13754803924987266220629389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9169869283324844147086259 13754803924987266220629389)
                ·
                  refine ⟨5158051471870224832736021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13754803924987266220629389 5158051471870224832736021)
                  ·
                    refine ⟨241783662743916789034501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5158051471870224832736021 241783662743916789034501)
                    ·
                      rfl

theorem cell23_1412616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_1412616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412616 prefixEnd_1412616 := by exact prefixLift 1412616
  have htrace : WordTrace (prefixWord ++ tailWord_1412616) baseStart_1412616 baseEnd_1412616 := by
    simpa [prefixWord, tailWord_1412616, baseEnd_1412616] using wordTrace_append hprefix tailTrace_1412616
  have hstable : (prefixWord ++ tailWord_1412616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412616).length < 2 ^ (prefixWord ++ tailWord_1412616).sum := by decide
  have hdescent : baseEnd_1412616 < baseStart_1412616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412628 : List Nat := [2, 4, 3, 1, 3, 1, 2, 2, 1, 4]
def baseStart_1412628 : Nat := 118140960795 + 1412628 * 2 ^ 59
def prefixEnd_1412628 : Nat := 4983230072969 + 3 ^ 40 * 1412628 * 2
def baseEnd_1412628 : Nat := 241785716666534773384483

theorem tailTrace_1412628 : CollatzResearch.WordTrace tailWord_1412628 prefixEnd_1412628 241785716666534773384483 := by
  unfold tailWord_1412628
  simp only [CollatzResearch.WordTrace]
  refine ⟨25761387963148744250003269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34348517284198325666671025 25761387963148744250003269)
  ·
    refine ⟨4830260243090389546875613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25761387963148744250003269 4830260243090389546875613)
    ·
      refine ⟨1811347591158896080078355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4830260243090389546875613 1811347591158896080078355)
      ·
        refine ⟨2717021386738344120117533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1811347591158896080078355 2717021386738344120117533)
        ·
          refine ⟨1018883020026879045044075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2717021386738344120117533 1018883020026879045044075)
          ·
            refine ⟨1528324530040318567566113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1018883020026879045044075 1528324530040318567566113)
            ·
              refine ⟨1146243397530238925674585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1528324530040318567566113 1146243397530238925674585)
              ·
                refine ⟨859682548147679194255939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1146243397530238925674585 859682548147679194255939)
                ·
                  refine ⟨1289523822221518791383909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 859682548147679194255939 1289523822221518791383909)
                  ·
                    refine ⟨241785716666534773384483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1289523822221518791383909 241785716666534773384483)
                    ·
                      rfl

theorem cell23_1412628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_1412628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412628 prefixEnd_1412628 := by exact prefixLift 1412628
  have htrace : WordTrace (prefixWord ++ tailWord_1412628) baseStart_1412628 baseEnd_1412628 := by
    simpa [prefixWord, tailWord_1412628, baseEnd_1412628] using wordTrace_append hprefix tailTrace_1412628
  have hstable : (prefixWord ++ tailWord_1412628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412628).length < 2 ^ (prefixWord ++ tailWord_1412628).sum := by decide
  have hdescent : baseEnd_1412628 < baseStart_1412628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412650 : List Nat := [3, 1, 4, 1, 1, 1, 1, 5, 2, 4]
def baseStart_1412650 : Nat := 118140960795 + 1412650 * 2 ^ 59
def prefixEnd_1412650 : Nat := 4983230072969 + 3 ^ 40 * 1412650 * 2
def baseEnd_1412650 : Nat := 241789482191334411359449

theorem tailTrace_1412650 : CollatzResearch.WordTrace tailWord_1412650 prefixEnd_1412650 241789482191334411359449 := by
  unfold tailWord_1412650
  simp only [CollatzResearch.WordTrace]
  refine ⟨12880894583054446564326851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34349052221478524171538269 12880894583054446564326851)
  ·
    refine ⟨19321341874581669846490277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12880894583054446564326851 19321341874581669846490277)
    ·
      refine ⟨3622751601484063096216927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19321341874581669846490277 3622751601484063096216927)
      ·
        refine ⟨5434127402226094644325391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3622751601484063096216927 5434127402226094644325391)
        ·
          refine ⟨8151191103339141966488087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5434127402226094644325391 8151191103339141966488087)
          ·
            refine ⟨12226786655008712949732131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8151191103339141966488087 12226786655008712949732131)
            ·
              refine ⟨18340179982513069424598197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12226786655008712949732131 18340179982513069424598197)
              ·
                refine ⟨1719391873360600258556081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18340179982513069424598197 1719391873360600258556081)
                ·
                  refine ⟨1289543905020450193917061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1719391873360600258556081 1289543905020450193917061)
                  ·
                    refine ⟨241789482191334411359449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1289543905020450193917061 241789482191334411359449)
                    ·
                      rfl

theorem cell23_1412650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_1412650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412650 prefixEnd_1412650 := by exact prefixLift 1412650
  have htrace : WordTrace (prefixWord ++ tailWord_1412650) baseStart_1412650 baseEnd_1412650 := by
    simpa [prefixWord, tailWord_1412650, baseEnd_1412650] using wordTrace_append hprefix tailTrace_1412650
  have hstable : (prefixWord ++ tailWord_1412650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412650).length < 2 ^ (prefixWord ++ tailWord_1412650).sum := by decide
  have hdescent : baseEnd_1412650 < baseStart_1412650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412663 : List Nat := [1, 1, 3, 1, 2, 5, 3, 7]
def baseStart_1412663 : Nat := 118140960795 + 1412663 * 2 ^ 59
def prefixEnd_1412663 : Nat := 4983230072969 + 3 ^ 40 * 1412663 * 2
def baseEnd_1412663 : Nat := 26865745252685617896881

theorem tailTrace_1412663 : CollatzResearch.WordTrace tailWord_1412663 prefixEnd_1412663 26865745252685617896881 := by
  unfold tailWord_1412663
  simp only [CollatzResearch.WordTrace]
  refine ⟨51524052481170689477530643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34349368320780459651687095 51524052481170689477530643)
  ·
    refine ⟨77286078721756034216295965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51524052481170689477530643 77286078721756034216295965)
    ·
      refine ⟨28982279520658512831110987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77286078721756034216295965 28982279520658512831110987)
      ·
        refine ⟨43473419280987769246666481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28982279520658512831110987 43473419280987769246666481)
        ·
          refine ⟨32605064460740826934999861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43473419280987769246666481 32605064460740826934999861)
          ·
            refine ⟨3056724793194452525156237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32605064460740826934999861 3056724793194452525156237)
            ·
              refine ⟨1146271797447919696933589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3056724793194452525156237 1146271797447919696933589)
              ·
                refine ⟨26865745252685617896881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1146271797447919696933589 26865745252685617896881)
                ·
                  rfl

theorem cell23_1412663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 7].length) (baseStart_1412663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412663 prefixEnd_1412663 := by exact prefixLift 1412663
  have htrace : WordTrace (prefixWord ++ tailWord_1412663) baseStart_1412663 baseEnd_1412663 := by
    simpa [prefixWord, tailWord_1412663, baseEnd_1412663] using wordTrace_append hprefix tailTrace_1412663
  have hstable : (prefixWord ++ tailWord_1412663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412663).length < 2 ^ (prefixWord ++ tailWord_1412663).sum := by decide
  have hdescent : baseEnd_1412663 < baseStart_1412663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412694 : List Nat := [5, 2, 2, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_1412694 : Nat := 118140960795 + 1412694 * 2 ^ 59
def prefixEnd_1412694 : Nat := 4983230072969 + 3 ^ 40 * 1412694 * 2
def baseEnd_1412694 : Nat := 725391039722801061928145

theorem tailTrace_1412694 : CollatzResearch.WordTrace tailWord_1412694 prefixEnd_1412694 725391039722801061928145 := by
  unfold tailWord_1412694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3220323946503648860744321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34350122096038921181272757 3220323946503648860744321)
  ·
    refine ⟨2415242959877736645558241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3220323946503648860744321 2415242959877736645558241)
    ·
      refine ⟨1811432219908302484168681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2415242959877736645558241 1811432219908302484168681)
      ·
        refine ⟨1358574164931226863126511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1811432219908302484168681 1358574164931226863126511)
        ·
          refine ⟨2037861247396840294689767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1358574164931226863126511 2037861247396840294689767)
          ·
            refine ⟨3056791871095260442034651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2037861247396840294689767 3056791871095260442034651)
            ·
              refine ⟨4585187806642890663051977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3056791871095260442034651 4585187806642890663051977)
              ·
                refine ⟨3438890854982167997288983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4585187806642890663051977 3438890854982167997288983)
                ·
                  refine ⟨5158336282473251995933475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3438890854982167997288983 5158336282473251995933475)
                  ·
                    refine ⟨7737504423709877993900213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5158336282473251995933475 7737504423709877993900213)
                    ·
                      refine ⟨725391039722801061928145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7737504423709877993900213 725391039722801061928145)
                      ·
                        rfl

theorem cell23_1412694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_1412694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412694 prefixEnd_1412694 := by exact prefixLift 1412694
  have htrace : WordTrace (prefixWord ++ tailWord_1412694) baseStart_1412694 baseEnd_1412694 := by
    simpa [prefixWord, tailWord_1412694, baseEnd_1412694] using wordTrace_append hprefix tailTrace_1412694
  have hstable : (prefixWord ++ tailWord_1412694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412694).length < 2 ^ (prefixWord ++ tailWord_1412694).sum := by decide
  have hdescent : baseEnd_1412694 < baseStart_1412694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412701 : List Nat := [1, 4, 4, 2, 1, 1, 3, 1, 2, 4]
def baseStart_1412701 : Nat := 118140960795 + 1412701 * 2 ^ 59
def prefixEnd_1412701 : Nat := 4983230072969 + 3 ^ 40 * 1412701 * 2
def baseEnd_1412701 : Nat := 241798211362460844846871

theorem tailTrace_1412701 : CollatzResearch.WordTrace tailWord_1412701 prefixEnd_1412701 241798211362460844846871 := by
  unfold tailWord_1412701
  simp only [CollatzResearch.WordTrace]
  refine ⟨51525438455033021967413957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34350292303355347978275971 51525438455033021967413957)
  ·
    refine ⟨9661019710318691618890117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51525438455033021967413957 9661019710318691618890117)
    ·
      refine ⟨1811441195684754678541897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9661019710318691618890117 1811441195684754678541897)
      ·
        refine ⟨1358580896763566008906423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1811441195684754678541897 1358580896763566008906423)
        ·
          refine ⟨2037871345145349013359635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1358580896763566008906423 2037871345145349013359635)
          ·
            refine ⟨3056807017718023520039453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2037871345145349013359635 3056807017718023520039453)
            ·
              refine ⟨1146302631644258820014795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3056807017718023520039453 1146302631644258820014795)
              ·
                refine ⟨1719453947466388230022193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1146302631644258820014795 1719453947466388230022193)
                ·
                  refine ⟨1289590460599791172516645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1719453947466388230022193 1289590460599791172516645)
                  ·
                    refine ⟨241798211362460844846871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1289590460599791172516645 241798211362460844846871)
                    ·
                      rfl

theorem cell23_1412701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_1412701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412701 prefixEnd_1412701 := by exact prefixLift 1412701
  have htrace : WordTrace (prefixWord ++ tailWord_1412701) baseStart_1412701 baseEnd_1412701 := by
    simpa [prefixWord, tailWord_1412701, baseEnd_1412701] using wordTrace_append hprefix tailTrace_1412701
  have hstable : (prefixWord ++ tailWord_1412701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412701).length < 2 ^ (prefixWord ++ tailWord_1412701).sum := by decide
  have hdescent : baseEnd_1412701 < baseStart_1412701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412733 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 1, 3, 5]
def baseStart_1412733 : Nat := 118140960795 + 1412733 * 2 ^ 59
def prefixEnd_1412733 : Nat := 4983230072969 + 3 ^ 40 * 1412733 * 2
def baseEnd_1412733 : Nat := 725411065468326409340465

theorem tailTrace_1412733 : CollatzResearch.WordTrace tailWord_1412733 prefixEnd_1412733 725411065468326409340465 := by
  unfold tailWord_1412733
  simp only [CollatzResearch.WordTrace]
  refine ⟨51526605590917091432578853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34351070393944727621719235 51526605590917091432578853)
  ·
    refine ⟨9661238548296954643608535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51526605590917091432578853 9661238548296954643608535)
    ·
      refine ⟨14491857822445431965412803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9661238548296954643608535 14491857822445431965412803)
      ·
        refine ⟨21737786733668147948119205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14491857822445431965412803 21737786733668147948119205)
        ·
          refine ⟨4075835012562777740272351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21737786733668147948119205 4075835012562777740272351)
          ·
            refine ⟨6113752518844166610408527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4075835012562777740272351 6113752518844166610408527)
            ·
              refine ⟨9170628778266249915612791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6113752518844166610408527 9170628778266249915612791)
              ·
                refine ⟨13755943167399374873419187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9170628778266249915612791 13755943167399374873419187)
                ·
                  refine ⟨20633914751099062310128781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13755943167399374873419187 20633914751099062310128781)
                  ·
                    refine ⟨7737718031662148366298293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20633914751099062310128781 7737718031662148366298293)
                    ·
                      refine ⟨725411065468326409340465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7737718031662148366298293 725411065468326409340465)
                      ·
                        rfl

theorem cell23_1412733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_1412733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412733 prefixEnd_1412733 := by exact prefixLift 1412733
  have htrace : WordTrace (prefixWord ++ tailWord_1412733) baseStart_1412733 baseEnd_1412733 := by
    simpa [prefixWord, tailWord_1412733, baseEnd_1412733] using wordTrace_append hprefix tailTrace_1412733
  have hstable : (prefixWord ++ tailWord_1412733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412733).length < 2 ^ (prefixWord ++ tailWord_1412733).sum := by decide
  have hdescent : baseEnd_1412733 < baseStart_1412733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412747 : List Nat := [1, 1, 1, 1, 4, 1, 4, 4, 2, 2, 2]
def baseStart_1412747 : Nat := 118140960795 + 1412747 * 2 ^ 59
def prefixEnd_1412747 : Nat := 4983230072969 + 3 ^ 40 * 1412747 * 2
def baseEnd_1412747 : Nat := 725418254197489354565401

theorem tailTrace_1412747 : CollatzResearch.WordTrace tailWord_1412747 prefixEnd_1412747 725418254197489354565401 := by
  unfold tailWord_1412747
  simp only [CollatzResearch.WordTrace]
  refine ⟨51527116212866371823588495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34351410808577581215725663 51527116212866371823588495)
  ·
    refine ⟨77290674319299557735382743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51527116212866371823588495 77290674319299557735382743)
    ·
      refine ⟨115936011478949336603074115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77290674319299557735382743 115936011478949336603074115)
      ·
        refine ⟨173904017218424004904611173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115936011478949336603074115 173904017218424004904611173)
        ·
          refine ⟨32607003228454500919614595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173904017218424004904611173 32607003228454500919614595)
          ·
            refine ⟨48910504842681751379421893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32607003228454500919614595 48910504842681751379421893)
            ·
              refine ⟨9170719658002828383641605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48910504842681751379421893 9170719658002828383641605)
              ·
                refine ⟨1719509935875530321932801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9170719658002828383641605 1719509935875530321932801)
                ·
                  refine ⟨1289632451906647741449601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1719509935875530321932801 1289632451906647741449601)
                  ·
                    refine ⟨967224338929985806087201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1289632451906647741449601 967224338929985806087201)
                    ·
                      refine ⟨725418254197489354565401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 967224338929985806087201 725418254197489354565401)
                      ·
                        rfl

theorem cell23_1412747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 2, 2].length) (baseStart_1412747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412747 prefixEnd_1412747 := by exact prefixLift 1412747
  have htrace : WordTrace (prefixWord ++ tailWord_1412747) baseStart_1412747 baseEnd_1412747 := by
    simpa [prefixWord, tailWord_1412747, baseEnd_1412747] using wordTrace_append hprefix tailTrace_1412747
  have hstable : (prefixWord ++ tailWord_1412747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412747).length < 2 ^ (prefixWord ++ tailWord_1412747).sum := by decide
  have hdescent : baseEnd_1412747 < baseStart_1412747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412793 : List Nat := [1, 2, 1, 4, 1, 1, 3, 2, 1, 2, 5]
def baseStart_1412793 : Nat := 118140960795 + 1412793 * 2 ^ 59
def prefixEnd_1412793 : Nat := 4983230072969 + 3 ^ 40 * 1412793 * 2
def baseEnd_1412793 : Nat := 725441874307596174590189

theorem tailTrace_1412793 : CollatzResearch.WordTrace tailWord_1412793 prefixEnd_1412793 725441874307596174590189 := by
  unfold tailWord_1412793
  simp only [CollatzResearch.WordTrace]
  refine ⟨51528793970699721679763033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34352529313799814453175355 51528793970699721679763033)
  ·
    refine ⟨38646595478024791259822275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51528793970699721679763033 38646595478024791259822275)
    ·
      refine ⟨57969893217037186889733413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38646595478024791259822275 57969893217037186889733413)
      ·
        refine ⟨10869354978194472541825015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57969893217037186889733413 10869354978194472541825015)
        ·
          refine ⟨16304032467291708812737523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10869354978194472541825015 16304032467291708812737523)
          ·
            refine ⟨24456048700937563219106285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16304032467291708812737523 24456048700937563219106285)
            ·
              refine ⟨9171018262851586207164857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24456048700937563219106285 9171018262851586207164857)
              ·
                refine ⟨6878263697138689655373643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9171018262851586207164857 6878263697138689655373643)
                ·
                  refine ⟨10317395545708034483060465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6878263697138689655373643 10317395545708034483060465)
                  ·
                    refine ⟨7738046659281025862295349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10317395545708034483060465 7738046659281025862295349)
                    ·
                      refine ⟨725441874307596174590189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7738046659281025862295349 725441874307596174590189)
                      ·
                        rfl

theorem cell23_1412793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_1412793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412793 prefixEnd_1412793 := by exact prefixLift 1412793
  have htrace : WordTrace (prefixWord ++ tailWord_1412793) baseStart_1412793 baseEnd_1412793 := by
    simpa [prefixWord, tailWord_1412793, baseEnd_1412793] using wordTrace_append hprefix tailTrace_1412793
  have hstable : (prefixWord ++ tailWord_1412793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412793).length < 2 ^ (prefixWord ++ tailWord_1412793).sum := by decide
  have hdescent : baseEnd_1412793 < baseStart_1412793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412863 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 6]
def baseStart_1412863 : Nat := 118140960795 + 1412863 * 2 ^ 59
def prefixEnd_1412863 : Nat := 4983230072969 + 3 ^ 40 * 1412863 * 2
def baseEnd_1412863 : Nat := 725477817953410900714867

theorem tailTrace_1412863 : CollatzResearch.WordTrace tailWord_1412863 prefixEnd_1412863 725477817953410900714867 := by
  unfold tailWord_1412863
  simp only [CollatzResearch.WordTrace]
  refine ⟨51531347080446123634811243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34354231386964082423207495 51531347080446123634811243)
  ·
    refine ⟨77297020620669185452216865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51531347080446123634811243 77297020620669185452216865)
    ·
      refine ⟨57972765465501889089162649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77297020620669185452216865 57972765465501889089162649)
      ·
        refine ⟨43479574099126416816871987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57972765465501889089162649 43479574099126416816871987)
        ·
          refine ⟨65219361148689625225307981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43479574099126416816871987 65219361148689625225307981)
          ·
            refine ⟨24457260430758609459490493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65219361148689625225307981 24457260430758609459490493)
            ·
              refine ⟨9171472661534478547308935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24457260430758609459490493 9171472661534478547308935)
              ·
                refine ⟨13757208992301717820963403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9171472661534478547308935 13757208992301717820963403)
                ·
                  refine ⟨20635813488452576731445105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13757208992301717820963403 20635813488452576731445105)
                  ·
                    refine ⟨15476860116339432548583829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20635813488452576731445105 15476860116339432548583829)
                    ·
                      refine ⟨725477817953410900714867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15476860116339432548583829 725477817953410900714867)
                      ·
                        rfl

theorem cell23_1412863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_1412863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412863 prefixEnd_1412863 := by exact prefixLift 1412863
  have htrace : WordTrace (prefixWord ++ tailWord_1412863) baseStart_1412863 baseEnd_1412863 := by
    simpa [prefixWord, tailWord_1412863, baseEnd_1412863] using wordTrace_append hprefix tailTrace_1412863
  have hstable : (prefixWord ++ tailWord_1412863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412863).length < 2 ^ (prefixWord ++ tailWord_1412863).sum := by decide
  have hdescent : baseEnd_1412863 < baseStart_1412863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412897 : List Nat := [1, 2, 3, 2, 1, 3, 2, 1, 1, 5, 2]
def baseStart_1412897 : Nat := 118140960795 + 1412897 * 2 ^ 59
def prefixEnd_1412897 : Nat := 4983230072969 + 3 ^ 40 * 1412897 * 2
def baseEnd_1412897 : Nat := 725495276295663767689711

theorem tailTrace_1412897 : CollatzResearch.WordTrace tailWord_1412897 prefixEnd_1412897 725495276295663767689711 := by
  unfold tailWord_1412897
  simp only [CollatzResearch.WordTrace]
  refine ⟨51532587162322947441548945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34355058108215298294365963 51532587162322947441548945)
  ·
    refine ⟨38649440371742210581161709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51532587162322947441548945 38649440371742210581161709)
    ·
      refine ⟨14493540139403328967935641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38649440371742210581161709 14493540139403328967935641)
      ·
        refine ⟨10870155104552496725951731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14493540139403328967935641 10870155104552496725951731)
        ·
          refine ⟨16305232656828745088927597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10870155104552496725951731 16305232656828745088927597)
          ·
            refine ⟨6114462246310779408347849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16305232656828745088927597 6114462246310779408347849)
            ·
              refine ⟨4585846684733084556260887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6114462246310779408347849 4585846684733084556260887)
              ·
                refine ⟨6878770027099626834391331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4585846684733084556260887 6878770027099626834391331)
                ·
                  refine ⟨10318155040649440251586997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6878770027099626834391331 10318155040649440251586997)
                  ·
                    refine ⟨967327035060885023586281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10318155040649440251586997 967327035060885023586281)
                    ·
                      refine ⟨725495276295663767689711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 967327035060885023586281 725495276295663767689711)
                      ·
                        rfl

theorem cell23_1412897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_1412897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412897 prefixEnd_1412897 := by exact prefixLift 1412897
  have htrace : WordTrace (prefixWord ++ tailWord_1412897) baseStart_1412897 baseEnd_1412897 := by
    simpa [prefixWord, tailWord_1412897, baseEnd_1412897] using wordTrace_append hprefix tailTrace_1412897
  have hstable : (prefixWord ++ tailWord_1412897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412897).length < 2 ^ (prefixWord ++ tailWord_1412897).sum := by decide
  have hdescent : baseEnd_1412897 < baseStart_1412897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412914 : List Nat := [3, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2]
def baseStart_1412914 : Nat := 118140960795 + 1412914 * 2 ^ 59
def prefixEnd_1412914 : Nat := 4983230072969 + 3 ^ 40 * 1412914 * 2
def baseEnd_1412914 : Nat := 725504005466790201177133

theorem tailTrace_1412914 : CollatzResearch.WordTrace tailWord_1412914 prefixEnd_1412914 725504005466790201177133 := by
  unfold tailWord_1412914
  simp only [CollatzResearch.WordTrace]
  refine ⟨12883301800815339836229449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34355471468840906229945197 12883301800815339836229449)
  ·
    refine ⟨9662476350611504877172087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12883301800815339836229449 9662476350611504877172087)
    ·
      refine ⟨14493714525917257315758131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9662476350611504877172087 14493714525917257315758131)
      ·
        refine ⟨21740571788875885973637197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14493714525917257315758131 21740571788875885973637197)
        ·
          refine ⟨8152714420828457240113949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21740571788875885973637197 8152714420828457240113949)
          ·
            refine ⟨3057267907810671465042731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8152714420828457240113949 3057267907810671465042731)
            ·
              refine ⟨4585901861716007197564097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3057267907810671465042731 4585901861716007197564097)
              ·
                refine ⟨3439426396287005398173073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4585901861716007197564097 3439426396287005398173073)
                ·
                  refine ⟨2579569797215254048629805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3439426396287005398173073 2579569797215254048629805)
                  ·
                    refine ⟨967338673955720268236177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2579569797215254048629805 967338673955720268236177)
                    ·
                      refine ⟨725504005466790201177133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 967338673955720268236177 725504005466790201177133)
                      ·
                        rfl

theorem cell23_1412914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2].length) (baseStart_1412914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412914 prefixEnd_1412914 := by exact prefixLift 1412914
  have htrace : WordTrace (prefixWord ++ tailWord_1412914) baseStart_1412914 baseEnd_1412914 := by
    simpa [prefixWord, tailWord_1412914, baseEnd_1412914] using wordTrace_append hprefix tailTrace_1412914
  have hstable : (prefixWord ++ tailWord_1412914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412914).length < 2 ^ (prefixWord ++ tailWord_1412914).sum := by decide
  have hdescent : baseEnd_1412914 < baseStart_1412914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412937 : List Nat := [1, 2, 1, 1, 2, 4, 3, 3, 2, 4]
def baseStart_1412937 : Nat := 118140960795 + 1412937 * 2 ^ 59
def prefixEnd_1412937 : Nat := 4983230072969 + 3 ^ 40 * 1412937 * 2
def baseEnd_1412937 : Nat := 241838605173947870396509

theorem tailTrace_1412937 : CollatzResearch.WordTrace tailWord_1412937 prefixEnd_1412937 241838605173947870396509 := by
  unfold tailWord_1412937
  simp only [CollatzResearch.WordTrace]
  refine ⟨51534046082178034273005065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34356030721452022848670043 51534046082178034273005065)
  ·
    refine ⟨38650534561633525704753799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51534046082178034273005065 38650534561633525704753799)
    ·
      refine ⟨57975801842450288557130699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38650534561633525704753799 57975801842450288557130699)
      ·
        refine ⟨86963702763675432835696049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57975801842450288557130699 86963702763675432835696049)
        ·
          refine ⟨65222777072756574626772037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86963702763675432835696049 65222777072756574626772037)
          ·
            refine ⟨12229270701141857742519757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65222777072756574626772037 12229270701141857742519757)
            ·
              refine ⟨4585976512928196653444909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12229270701141857742519757 4585976512928196653444909)
              ·
                refine ⟨1719741192348073745041841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4585976512928196653444909 1719741192348073745041841)
                ·
                  refine ⟨1289805894261055308781381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1719741192348073745041841 1289805894261055308781381)
                  ·
                    refine ⟨241838605173947870396509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1289805894261055308781381 241838605173947870396509)
                    ·
                      rfl

theorem cell23_1412937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 4].length) (baseStart_1412937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412937 prefixEnd_1412937 := by exact prefixLift 1412937
  have htrace : WordTrace (prefixWord ++ tailWord_1412937) baseStart_1412937 baseEnd_1412937 := by
    simpa [prefixWord, tailWord_1412937, baseEnd_1412937] using wordTrace_append hprefix tailTrace_1412937
  have hstable : (prefixWord ++ tailWord_1412937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412937).length < 2 ^ (prefixWord ++ tailWord_1412937).sum := by decide
  have hdescent : baseEnd_1412937 < baseStart_1412937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412941 : List Nat := [1, 6, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_1412941 : Nat := 118140960795 + 1412941 * 2 ^ 59
def prefixEnd_1412941 : Nat := 4983230072969 + 3 ^ 40 * 1412941 * 2
def baseEnd_1412941 : Nat := 241839289814820531846503

theorem tailTrace_1412941 : CollatzResearch.WordTrace tailWord_1412941 prefixEnd_1412941 241839289814820531846503 := by
  unfold tailWord_1412941
  simp only [CollatzResearch.WordTrace]
  refine ⟨51534191974163542956150677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34356127982775695304100451 51534191974163542956150677)
  ·
    refine ⟨2415665248788916076069563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51534191974163542956150677 2415665248788916076069563)
    ·
      refine ⟨3623497873183374114104345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2415665248788916076069563 3623497873183374114104345)
      ·
        refine ⟨2717623404887530585578259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3623497873183374114104345 2717623404887530585578259)
        ·
          refine ⟨4076435107331295878367389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2717623404887530585578259 4076435107331295878367389)
          ·
            refine ⟨1528663165249235954387771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4076435107331295878367389 1528663165249235954387771)
            ·
              refine ⟨2292994747873853931581657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1528663165249235954387771 2292994747873853931581657)
              ·
                refine ⟨1719746060905390448686243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2292994747873853931581657 1719746060905390448686243)
                ·
                  refine ⟨2579619091358085673029365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1719746060905390448686243 2579619091358085673029365)
                  ·
                    refine ⟨241839289814820531846503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2579619091358085673029365 241839289814820531846503)
                    ·
                      rfl

theorem cell23_1412941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_1412941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412941 prefixEnd_1412941 := by exact prefixLift 1412941
  have htrace : WordTrace (prefixWord ++ tailWord_1412941) baseStart_1412941 baseEnd_1412941 := by
    simpa [prefixWord, tailWord_1412941, baseEnd_1412941] using wordTrace_append hprefix tailTrace_1412941
  have hstable : (prefixWord ++ tailWord_1412941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412941).length < 2 ^ (prefixWord ++ tailWord_1412941).sum := by decide
  have hdescent : baseEnd_1412941 < baseStart_1412941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412961 : List Nat := [1, 2, 3, 1, 1, 1, 4, 5, 1, 2, 2]
def baseStart_1412961 : Nat := 118140960795 + 1412961 * 2 ^ 59
def prefixEnd_1412961 : Nat := 4983230072969 + 3 ^ 40 * 1412961 * 2
def baseEnd_1412961 : Nat := 725528139057551517289417

theorem tailTrace_1412961 : CollatzResearch.WordTrace tailWord_1412961 prefixEnd_1412961 725528139057551517289417 := by
  unfold tailWord_1412961
  simp only [CollatzResearch.WordTrace]
  refine ⟨51534921434091086371878737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34356614289394057581252491 51534921434091086371878737)
  ·
    refine ⟨38651191075568314778909053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51534921434091086371878737 38651191075568314778909053)
    ·
      refine ⟨14494196653338118042090895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38651191075568314778909053 14494196653338118042090895)
      ·
        refine ⟨21741294980007177063136343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14494196653338118042090895 21741294980007177063136343)
        ·
          refine ⟨32611942470010765594704515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21741294980007177063136343 32611942470010765594704515)
          ·
            refine ⟨48917913705016148392056773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32611942470010765594704515 48917913705016148392056773)
            ·
              refine ⟨9172108819690527823510645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48917913705016148392056773 9172108819690527823510645)
              ·
                refine ⟨859885201845986983454123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9172108819690527823510645 859885201845986983454123)
                ·
                  refine ⟨1289827802768980475181185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 859885201845986983454123 1289827802768980475181185)
                  ·
                    refine ⟨967370852076735356385889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1289827802768980475181185 967370852076735356385889)
                    ·
                      refine ⟨725528139057551517289417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 967370852076735356385889 725528139057551517289417)
                      ·
                        rfl

theorem cell23_1412961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 1, 2, 2].length) (baseStart_1412961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412961 prefixEnd_1412961 := by exact prefixLift 1412961
  have htrace : WordTrace (prefixWord ++ tailWord_1412961) baseStart_1412961 baseEnd_1412961 := by
    simpa [prefixWord, tailWord_1412961, baseEnd_1412961] using wordTrace_append hprefix tailTrace_1412961
  have hstable : (prefixWord ++ tailWord_1412961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412961).length < 2 ^ (prefixWord ++ tailWord_1412961).sum := by decide
  have hdescent : baseEnd_1412961 < baseStart_1412961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412964 : List Nat := [2, 3, 1, 1, 5, 2, 1, 1, 1, 1, 5]
def baseStart_1412964 : Nat := 118140960795 + 1412964 * 2 ^ 59
def prefixEnd_1412964 : Nat := 4983230072969 + 3 ^ 40 * 1412964 * 2
def baseEnd_1412964 : Nat := 725529679499515005551903

theorem tailTrace_1412964 : CollatzResearch.WordTrace tailWord_1412964 prefixEnd_1412964 725529679499515005551903 := by
  unfold tailWord_1412964
  simp only [CollatzResearch.WordTrace]
  refine ⟨25767515426540108942118973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34356687235386811922825297 25767515426540108942118973)
  ·
    refine ⟨9662818284952540853294615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25767515426540108942118973 9662818284952540853294615)
    ·
      refine ⟨14494227427428811279941923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9662818284952540853294615 14494227427428811279941923)
      ·
        refine ⟨21741341141143216919912885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14494227427428811279941923 21741341141143216919912885)
        ·
          refine ⟨2038250731982176586241833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21741341141143216919912885 2038250731982176586241833)
          ·
            refine ⟨1528688048986632439681375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2038250731982176586241833 1528688048986632439681375)
            ·
              refine ⟨2293032073479948659522063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1528688048986632439681375 2293032073479948659522063)
              ·
                refine ⟨3439548110219922989283095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2293032073479948659522063 3439548110219922989283095)
                ·
                  refine ⟨5159322165329884483924643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3439548110219922989283095 5159322165329884483924643)
                  ·
                    refine ⟨7738983247994826725886965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5159322165329884483924643 7738983247994826725886965)
                    ·
                      refine ⟨725529679499515005551903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7738983247994826725886965 725529679499515005551903)
                      ·
                        rfl

theorem cell23_1412964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_1412964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1412964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1412964 prefixEnd_1412964 := by exact prefixLift 1412964
  have htrace : WordTrace (prefixWord ++ tailWord_1412964) baseStart_1412964 baseEnd_1412964 := by
    simpa [prefixWord, tailWord_1412964, baseEnd_1412964] using wordTrace_append hprefix tailTrace_1412964
  have hstable : (prefixWord ++ tailWord_1412964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412964).length < 2 ^ (prefixWord ++ tailWord_1412964).sum := by decide
  have hdescent : baseEnd_1412964 < baseStart_1412964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413004 : List Nat := [2, 2, 1, 2, 1, 2, 1, 6, 1, 3, 2]
def baseStart_1413004 : Nat := 118140960795 + 1413004 * 2 ^ 59
def prefixEnd_1413004 : Nat := 4983230072969 + 3 ^ 40 * 1413004 * 2
def baseEnd_1413004 : Nat := 725550218725694849051719

theorem tailTrace_1413004 : CollatzResearch.WordTrace tailWord_1413004 prefixEnd_1413004 725550218725694849051719 := by
  unfold tailWord_1413004
  simp only [CollatzResearch.WordTrace]
  refine ⟨25768244886467652357847033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34357659848623536477129377 25768244886467652357847033)
  ·
    refine ⟨19326183664850739268385275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25768244886467652357847033 19326183664850739268385275)
    ·
      refine ⟨28989275497276108902577913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19326183664850739268385275 28989275497276108902577913)
      ·
        refine ⟨21741956622957081676933435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28989275497276108902577913 21741956622957081676933435)
        ·
          refine ⟨32612934934435622515400153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21741956622957081676933435 32612934934435622515400153)
          ·
            refine ⟨24459701200826716886550115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32612934934435622515400153 24459701200826716886550115)
            ·
              refine ⟨36689551801240075329825173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24459701200826716886550115 36689551801240075329825173)
              ·
                refine ⟨1719822740683128531085555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36689551801240075329825173 1719822740683128531085555)
                ·
                  refine ⟨2579734111024692796628333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1719822740683128531085555 2579734111024692796628333)
                  ·
                    refine ⟨967400291634259798735625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2579734111024692796628333 967400291634259798735625)
                    ·
                      refine ⟨725550218725694849051719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 967400291634259798735625 725550218725694849051719)
                      ·
                        rfl

theorem cell23_1413004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 1, 3, 2].length) (baseStart_1413004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413004 prefixEnd_1413004 := by exact prefixLift 1413004
  have htrace : WordTrace (prefixWord ++ tailWord_1413004) baseStart_1413004 baseEnd_1413004 := by
    simpa [prefixWord, tailWord_1413004, baseEnd_1413004] using wordTrace_append hprefix tailTrace_1413004
  have hstable : (prefixWord ++ tailWord_1413004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413004).length < 2 ^ (prefixWord ++ tailWord_1413004).sum := by decide
  have hdescent : baseEnd_1413004 < baseStart_1413004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413021 : List Nat := [1, 4, 2, 1, 2, 3, 1, 3, 1, 3, 2]
def baseStart_1413021 : Nat := 118140960795 + 1413021 * 2 ^ 59
def prefixEnd_1413021 : Nat := 4983230072969 + 3 ^ 40 * 1413021 * 2
def baseEnd_1413021 : Nat := 725558947896821282539141

theorem tailTrace_1413021 : CollatzResearch.WordTrace tailWord_1413021 prefixEnd_1413021 725558947896821282539141 := by
  unfold tailWord_1413021
  simp only [CollatzResearch.WordTrace]
  refine ⟨51537109813873716619062917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34358073209249144412708611 51537109813873716619062917)
  ·
    refine ⟨9663208090101321866074297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51537109813873716619062917 9663208090101321866074297)
    ·
      refine ⟨7247406067575991399555723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9663208090101321866074297 7247406067575991399555723)
      ·
        refine ⟨10871109101363987099333585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7247406067575991399555723 10871109101363987099333585)
        ·
          refine ⟨8153331826022990324500189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10871109101363987099333585 8153331826022990324500189)
          ·
            refine ⟨3057499434758621371687571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8153331826022990324500189 3057499434758621371687571)
            ·
              refine ⟨4586249152137932057531357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3057499434758621371687571 4586249152137932057531357)
              ·
                refine ⟨1719843432051724521574259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4586249152137932057531357 1719843432051724521574259)
                ·
                  refine ⟨2579765148077586782361389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1719843432051724521574259 2579765148077586782361389)
                  ·
                    refine ⟨967411930529095043385521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2579765148077586782361389 967411930529095043385521)
                    ·
                      refine ⟨725558947896821282539141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 967411930529095043385521 725558947896821282539141)
                      ·
                        rfl

theorem cell23_1413021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_1413021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413021 prefixEnd_1413021 := by exact prefixLift 1413021
  have htrace : WordTrace (prefixWord ++ tailWord_1413021) baseStart_1413021 baseEnd_1413021 := by
    simpa [prefixWord, tailWord_1413021, baseEnd_1413021] using wordTrace_append hprefix tailTrace_1413021
  have hstable : (prefixWord ++ tailWord_1413021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413021).length < 2 ^ (prefixWord ++ tailWord_1413021).sum := by decide
  have hdescent : baseEnd_1413021 < baseStart_1413021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413087 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 4, 5]
def baseStart_1413087 : Nat := 118140960795 + 1413087 * 2 ^ 59
def prefixEnd_1413087 : Nat := 4983230072969 + 3 ^ 40 * 1413087 * 2
def baseEnd_1413087 : Nat := 241864279206672674771279

theorem tailTrace_1413087 : CollatzResearch.WordTrace tailWord_1413087 prefixEnd_1413087 241864279206672674771279 := by
  unfold tailWord_1413087
  simp only [CollatzResearch.WordTrace]
  refine ⟨51539517031634609890965515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34359678021089739927310343 51539517031634609890965515)
  ·
    refine ⟨77309275547451914836448273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51539517031634609890965515 77309275547451914836448273)
    ·
      refine ⟨57981956660588936127336205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77309275547451914836448273 57981956660588936127336205)
      ·
        refine ⟨21743233747720851047751077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57981956660588936127336205 21743233747720851047751077)
        ·
          refine ⟨4076856327697659571453327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21743233747720851047751077 4076856327697659571453327)
          ·
            refine ⟨6115284491546489357179991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4076856327697659571453327 6115284491546489357179991)
            ·
              refine ⟨9172926737319734035769987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6115284491546489357179991 9172926737319734035769987)
              ·
                refine ⟨13759390105979601053654981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9172926737319734035769987 13759390105979601053654981)
                ·
                  refine ⟨2579885644871175197560309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13759390105979601053654981 2579885644871175197560309)
                  ·
                    refine ⟨241864279206672674771279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2579885644871175197560309 241864279206672674771279)
                    ·
                      rfl

theorem cell23_1413087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 5].length) (baseStart_1413087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413087 prefixEnd_1413087 := by exact prefixLift 1413087
  have htrace : WordTrace (prefixWord ++ tailWord_1413087) baseStart_1413087 baseEnd_1413087 := by
    simpa [prefixWord, tailWord_1413087, baseEnd_1413087] using wordTrace_append hprefix tailTrace_1413087
  have hstable : (prefixWord ++ tailWord_1413087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413087).length < 2 ^ (prefixWord ++ tailWord_1413087).sum := by decide
  have hdescent : baseEnd_1413087 < baseStart_1413087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413091 : List Nat := [1, 1, 1, 6, 1, 3, 3, 2, 5]
def baseStart_1413091 : Nat := 118140960795 + 1413091 * 2 ^ 59
def prefixEnd_1413091 : Nat := 4983230072969 + 3 ^ 40 * 1413091 * 2
def baseEnd_1413091 : Nat := 80621654615848445407091

theorem tailTrace_1413091 : CollatzResearch.WordTrace tailWord_1413091 prefixEnd_1413091 80621654615848445407091 := by
  unfold tailWord_1413091
  simp only [CollatzResearch.WordTrace]
  refine ⟨51539662923620118574111127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34359775282413412382740751 51539662923620118574111127)
  ·
    refine ⟨77309494385430177861166691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51539662923620118574111127 77309494385430177861166691)
    ·
      refine ⟨115964241578145266791750037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77309494385430177861166691 115964241578145266791750037)
      ·
        refine ⟨5435823823975559380863283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 115964241578145266791750037 5435823823975559380863283)
        ·
          refine ⟨8153735735963339071294925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5435823823975559380863283 8153735735963339071294925)
          ·
            refine ⟨3057650900986252151735597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8153735735963339071294925 3057650900986252151735597)
            ·
              refine ⟨1146619087869844556900849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3057650900986252151735597 1146619087869844556900849)
              ·
                refine ⟨859964315902383417675637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1146619087869844556900849 859964315902383417675637)
                ·
                  refine ⟨80621654615848445407091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 859964315902383417675637 80621654615848445407091)
                  ·
                    rfl

theorem cell23_1413091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 5].length) (baseStart_1413091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413091 prefixEnd_1413091 := by exact prefixLift 1413091
  have htrace : WordTrace (prefixWord ++ tailWord_1413091) baseStart_1413091 baseEnd_1413091 := by
    simpa [prefixWord, tailWord_1413091, baseEnd_1413091] using wordTrace_append hprefix tailTrace_1413091
  have hstable : (prefixWord ++ tailWord_1413091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413091).length < 2 ^ (prefixWord ++ tailWord_1413091).sum := by decide
  have hdescent : baseEnd_1413091 < baseStart_1413091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413144 : List Nat := [2, 1, 2, 3, 2, 1, 1, 4, 2, 2, 3]
def baseStart_1413144 : Nat := 118140960795 + 1413144 * 2 ^ 59
def prefixEnd_1413144 : Nat := 4983230072969 + 3 ^ 40 * 1413144 * 2
def baseEnd_1413144 : Nat := 725622106017324301301075

theorem tailTrace_1413144 : CollatzResearch.WordTrace tailWord_1413144 prefixEnd_1413144 725622106017324301301075 := by
  unfold tailWord_1413144
  simp only [CollatzResearch.WordTrace]
  refine ⟨25770797996214054312895243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34361063994952072417193657 25770797996214054312895243)
  ·
    refine ⟨38656196994321081469342865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25770797996214054312895243 38656196994321081469342865)
    ·
      refine ⟨28992147745740811102007149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38656196994321081469342865 28992147745740811102007149)
      ·
        refine ⟨10872055404652804163252681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28992147745740811102007149 10872055404652804163252681)
        ·
          refine ⟨8154041553489603122439511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10872055404652804163252681 8154041553489603122439511)
          ·
            refine ⟨12231062330234404683659267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8154041553489603122439511 12231062330234404683659267)
            ·
              refine ⟨18346593495351607025488901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12231062330234404683659267 18346593495351607025488901)
              ·
                refine ⟨3439986280378426317279169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18346593495351607025488901 3439986280378426317279169)
                ·
                  refine ⟨2579989710283819737959377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3439986280378426317279169 2579989710283819737959377)
                  ·
                    refine ⟨1934992282712864803469533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2579989710283819737959377 1934992282712864803469533)
                    ·
                      refine ⟨725622106017324301301075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1934992282712864803469533 725622106017324301301075)
                      ·
                        rfl

theorem cell23_1413144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_1413144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413144 prefixEnd_1413144 := by exact prefixLift 1413144
  have htrace : WordTrace (prefixWord ++ tailWord_1413144) baseStart_1413144 baseEnd_1413144 := by
    simpa [prefixWord, tailWord_1413144, baseEnd_1413144] using wordTrace_append hprefix tailTrace_1413144
  have hstable : (prefixWord ++ tailWord_1413144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413144).length < 2 ^ (prefixWord ++ tailWord_1413144).sum := by decide
  have hdescent : baseEnd_1413144 < baseStart_1413144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413151 : List Nat := [1, 1, 2, 4, 1, 2, 3, 4, 1, 4]
def baseStart_1413151 : Nat := 118140960795 + 1413151 * 2 ^ 59
def prefixEnd_1413151 : Nat := 4983230072969 + 3 ^ 40 * 1413151 * 2
def baseEnd_1413151 : Nat := 241875233460635257971181

theorem tailTrace_1413151 : CollatzResearch.WordTrace tailWord_1413151 prefixEnd_1413151 241875233460635257971181 := by
  unfold tailWord_1413151
  simp only [CollatzResearch.WordTrace]
  refine ⟨51541851303402748821295307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34361234202268499214196871 51541851303402748821295307)
  ·
    refine ⟨77312776955104123231942961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51541851303402748821295307 77312776955104123231942961)
    ·
      refine ⟨57984582716328092423957221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77312776955104123231942961 57984582716328092423957221)
      ·
        refine ⟨10872109259311517329491979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57984582716328092423957221 10872109259311517329491979)
        ·
          refine ⟨16308163888967275994237969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10872109259311517329491979 16308163888967275994237969)
          ·
            refine ⟨12231122916725456995678477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16308163888967275994237969 12231122916725456995678477)
            ·
              refine ⟨4586671093772046373379429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12231122916725456995678477 4586671093772046373379429)
              ·
                refine ⟨860000830082258695008643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4586671093772046373379429 860000830082258695008643)
                ·
                  refine ⟨1290001245123388042512965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 860000830082258695008643 1290001245123388042512965)
                  ·
                    refine ⟨241875233460635257971181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1290001245123388042512965 241875233460635257971181)
                    ·
                      rfl

theorem cell23_1413151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 1, 4].length) (baseStart_1413151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413151 prefixEnd_1413151 := by exact prefixLift 1413151
  have htrace : WordTrace (prefixWord ++ tailWord_1413151) baseStart_1413151 baseEnd_1413151 := by
    simpa [prefixWord, tailWord_1413151, baseEnd_1413151] using wordTrace_append hprefix tailTrace_1413151
  have hstable : (prefixWord ++ tailWord_1413151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413151).length < 2 ^ (prefixWord ++ tailWord_1413151).sum := by decide
  have hdescent : baseEnd_1413151 < baseStart_1413151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413207 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 3, 6]
def baseStart_1413207 : Nat := 118140960795 + 1413207 * 2 ^ 59
def prefixEnd_1413207 : Nat := 4983230072969 + 3 ^ 40 * 1413207 * 2
def baseEnd_1413207 : Nat := 241884818432852518271095

theorem tailTrace_1413207 : CollatzResearch.WordTrace tailWord_1413207 prefixEnd_1413207 241884818432852518271095 := by
  unfold tailWord_1413207
  simp only [CollatzResearch.WordTrace]
  refine ⟨51543893791199870385333875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34362595860799913590222583 51543893791199870385333875)
  ·
    refine ⟨77315840686799805578000813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51543893791199870385333875 77315840686799805578000813)
    ·
      refine ⟨28993440257549927091750305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77315840686799805578000813 28993440257549927091750305)
      ·
        refine ⟨21745080193162445318812729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28993440257549927091750305 21745080193162445318812729)
        ·
          refine ⟨16308810144871833989109547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21745080193162445318812729 16308810144871833989109547)
          ·
            refine ⟨24463215217307750983664321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16308810144871833989109547 24463215217307750983664321)
            ·
              refine ⟨18347411412980813237748241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24463215217307750983664321 18347411412980813237748241)
              ·
                refine ⟨13760558559735609928311181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18347411412980813237748241 13760558559735609928311181)
                ·
                  refine ⟨5160209459900853723116693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13760558559735609928311181 5160209459900853723116693)
                  ·
                    refine ⟨241884818432852518271095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5160209459900853723116693 241884818432852518271095)
                    ·
                      rfl

theorem cell23_1413207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_1413207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413207 prefixEnd_1413207 := by exact prefixLift 1413207
  have htrace : WordTrace (prefixWord ++ tailWord_1413207) baseStart_1413207 baseEnd_1413207 := by
    simpa [prefixWord, tailWord_1413207, baseEnd_1413207] using wordTrace_append hprefix tailTrace_1413207
  have hstable : (prefixWord ++ tailWord_1413207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413207).length < 2 ^ (prefixWord ++ tailWord_1413207).sum := by decide
  have hdescent : baseEnd_1413207 < baseStart_1413207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413208 : List Nat := [2, 1, 2, 2, 1, 4, 2, 4, 1, 1, 3]
def baseStart_1413208 : Nat := 118140960795 + 1413208 * 2 ^ 59
def prefixEnd_1413208 : Nat := 4983230072969 + 3 ^ 40 * 1413208 * 2
def baseEnd_1413208 : Nat := 725654968779212050900781

theorem tailTrace_1413208 : CollatzResearch.WordTrace tailWord_1413208 prefixEnd_1413208 725654968779212050900781 := by
  unfold tailWord_1413208
  simp only [CollatzResearch.WordTrace]
  refine ⟨25771965132098123778060139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34362620176130831704080185 25771965132098123778060139)
  ·
    refine ⟨38657947698147185667090209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25771965132098123778060139 38657947698147185667090209)
    ·
      refine ⟨28993460773610389250317657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38657947698147185667090209 28993460773610389250317657)
      ·
        refine ⟨21745095580207791937738243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28993460773610389250317657 21745095580207791937738243)
        ·
          refine ⟨32617643370311687906607365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21745095580207791937738243 32617643370311687906607365)
          ·
            refine ⟨6115808131933441482488881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32617643370311687906607365 6115808131933441482488881)
            ·
              refine ⟨4586856098950081111866661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6115808131933441482488881 4586856098950081111866661)
              ·
                refine ⟨860035518553140208474999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4586856098950081111866661 860035518553140208474999)
                ·
                  refine ⟨1290053277829710312712499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 860035518553140208474999 1290053277829710312712499)
                  ·
                    refine ⟨1935079916744565469068749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1290053277829710312712499 1935079916744565469068749)
                    ·
                      refine ⟨725654968779212050900781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1935079916744565469068749 725654968779212050900781)
                      ·
                        rfl

theorem cell23_1413208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 1, 1, 3].length) (baseStart_1413208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413208 prefixEnd_1413208 := by exact prefixLift 1413208
  have htrace : WordTrace (prefixWord ++ tailWord_1413208) baseStart_1413208 baseEnd_1413208 := by
    simpa [prefixWord, tailWord_1413208, baseEnd_1413208] using wordTrace_append hprefix tailTrace_1413208
  have hstable : (prefixWord ++ tailWord_1413208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413208).length < 2 ^ (prefixWord ++ tailWord_1413208).sum := by decide
  have hdescent : baseEnd_1413208 < baseStart_1413208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413231 : List Nat := [1, 1, 2, 1, 3, 5, 2, 2, 1, 1, 4]
def baseStart_1413231 : Nat := 118140960795 + 1413231 * 2 ^ 59
def prefixEnd_1413231 : Nat := 4983230072969 + 3 ^ 40 * 1413231 * 2
def baseEnd_1413231 : Nat := 725666778834265460913175

theorem tailTrace_1413231 : CollatzResearch.WordTrace tailWord_1413231 prefixEnd_1413231 725666778834265460913175 := by
  unfold tailWord_1413231
  simp only [CollatzResearch.WordTrace]
  refine ⟨51544769143112922484207547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34363179428741948322805031 51544769143112922484207547)
  ·
    refine ⟨77317153714669383726311321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51544769143112922484207547 77317153714669383726311321)
    ·
      refine ⟨57987865286002037794733491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77317153714669383726311321 57987865286002037794733491)
      ·
        refine ⟨86981797929003056692100237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57987865286002037794733491 86981797929003056692100237)
        ·
          refine ⟨32618174223376146259537589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86981797929003056692100237 32618174223376146259537589)
          ·
            refine ⟨3057953833441513711831649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32618174223376146259537589 3057953833441513711831649)
            ·
              refine ⟨2293465375081135283873737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3057953833441513711831649 2293465375081135283873737)
              ·
                refine ⟨1720099031310851462905303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2293465375081135283873737 1720099031310851462905303)
                ·
                  refine ⟨2580148546966277194357955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1720099031310851462905303 2580148546966277194357955)
                  ·
                    refine ⟨3870222820449415791536933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2580148546966277194357955 3870222820449415791536933)
                    ·
                      refine ⟨725666778834265460913175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3870222820449415791536933 725666778834265460913175)
                      ·
                        rfl

theorem cell23_1413231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 1, 4].length) (baseStart_1413231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413231 prefixEnd_1413231 := by exact prefixLift 1413231
  have htrace : WordTrace (prefixWord ++ tailWord_1413231) baseStart_1413231 baseEnd_1413231 := by
    simpa [prefixWord, tailWord_1413231, baseEnd_1413231] using wordTrace_append hprefix tailTrace_1413231
  have hstable : (prefixWord ++ tailWord_1413231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413231).length < 2 ^ (prefixWord ++ tailWord_1413231).sum := by decide
  have hdescent : baseEnd_1413231 < baseStart_1413231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413251 : List Nat := [1, 1, 1, 3, 3, 3, 2, 3, 1, 2, 3]
def baseStart_1413251 : Nat := 118140960795 + 1413251 * 2 ^ 59
def prefixEnd_1413251 : Nat := 4983230072969 + 3 ^ 40 * 1413251 * 2
def baseEnd_1413251 : Nat := 725677048447355382663083

theorem tailTrace_1413251 : CollatzResearch.WordTrace tailWord_1413251 prefixEnd_1413251 725677048447355382663083 := by
  unfold tailWord_1413251
  simp only [CollatzResearch.WordTrace]
  refine ⟨51545498603040465899935607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34363665735360310599957071 51545498603040465899935607)
  ·
    refine ⟨77318247904560698849903411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51545498603040465899935607 77318247904560698849903411)
    ·
      refine ⟨115977371856841048274855117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77318247904560698849903411 115977371856841048274855117)
      ·
        refine ⟨43491514446315393103070669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115977371856841048274855117 43491514446315393103070669)
        ·
          refine ⟨16309317917368272413651501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43491514446315393103070669 16309317917368272413651501)
          ·
            refine ⟨6115994219013102155119313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16309317917368272413651501 6115994219013102155119313)
            ·
              refine ⟨4586995664259826616339485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6115994219013102155119313 4586995664259826616339485)
              ·
                refine ⟨1720123374097434981127307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4586995664259826616339485 1720123374097434981127307)
                ·
                  refine ⟨2580185061146152471690961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1720123374097434981127307 2580185061146152471690961)
                  ·
                    refine ⟨1935138795859614353768221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2580185061146152471690961 1935138795859614353768221)
                    ·
                      refine ⟨725677048447355382663083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1935138795859614353768221 725677048447355382663083)
                      ·
                        rfl

theorem cell23_1413251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 2, 3].length) (baseStart_1413251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413251 prefixEnd_1413251 := by exact prefixLift 1413251
  have htrace : WordTrace (prefixWord ++ tailWord_1413251) baseStart_1413251 baseEnd_1413251 := by
    simpa [prefixWord, tailWord_1413251, baseEnd_1413251] using wordTrace_append hprefix tailTrace_1413251
  have hstable : (prefixWord ++ tailWord_1413251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413251).length < 2 ^ (prefixWord ++ tailWord_1413251).sum := by decide
  have hdescent : baseEnd_1413251 < baseStart_1413251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413267 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 2, 7]
def baseStart_1413267 : Nat := 118140960795 + 1413267 * 2 ^ 59
def prefixEnd_1413267 : Nat := 4983230072969 + 3 ^ 40 * 1413267 * 2
def baseEnd_1413267 : Nat := 241895088045942440021003

theorem tailTrace_1413267 : CollatzResearch.WordTrace tailWord_1413267 prefixEnd_1413267 241895088045942440021003 := by
  unfold tailWord_1413267
  simp only [CollatzResearch.WordTrace]
  refine ⟨51546082170982500632518055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34364054780655000421678703 51546082170982500632518055)
  ·
    refine ⟨77319123256473750948777083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51546082170982500632518055 77319123256473750948777083)
    ·
      refine ⟨115978684884710626423165625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77319123256473750948777083 115978684884710626423165625)
      ·
        refine ⟨86984013663532969817374219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115978684884710626423165625 86984013663532969817374219)
        ·
          refine ⟨130476020495299454726061329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86984013663532969817374219 130476020495299454726061329)
          ·
            refine ⟨97857015371474591044545997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130476020495299454726061329 97857015371474591044545997)
            ·
              refine ⟨36696380764302971641704749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97857015371474591044545997 36696380764302971641704749)
              ·
                refine ⟨13761142786613614365639281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36696380764302971641704749 13761142786613614365639281)
                ·
                  refine ⟨10320857089960210774229461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13761142786613614365639281 10320857089960210774229461)
                  ·
                    refine ⟨241895088045942440021003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10320857089960210774229461 241895088045942440021003)
                    ·
                      rfl

theorem cell23_1413267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 7].length) (baseStart_1413267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413267 prefixEnd_1413267 := by exact prefixLift 1413267
  have htrace : WordTrace (prefixWord ++ tailWord_1413267) baseStart_1413267 baseEnd_1413267 := by
    simpa [prefixWord, tailWord_1413267, baseEnd_1413267] using wordTrace_append hprefix tailTrace_1413267
  have hstable : (prefixWord ++ tailWord_1413267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413267).length < 2 ^ (prefixWord ++ tailWord_1413267).sum := by decide
  have hdescent : baseEnd_1413267 < baseStart_1413267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413344 : List Nat := [2, 1, 1, 3, 1, 3, 3, 2, 7]
def baseStart_1413344 : Nat := 118140960795 + 1413344 * 2 ^ 59
def prefixEnd_1413344 : Nat := 4983230072969 + 3 ^ 40 * 1413344 * 2
def baseEnd_1413344 : Nat := 80636089127580390977795

theorem tailTrace_1413344 : CollatzResearch.WordTrace tailWord_1413344 prefixEnd_1413344 80636089127580390977795 := by
  unfold tailWord_1413344
  simp only [CollatzResearch.WordTrace]
  refine ⟨25774445295851771391535543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34365927061135695188714057 25774445295851771391535543)
  ·
    refine ⟨38661667943777657087303315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25774445295851771391535543 38661667943777657087303315)
    ·
      refine ⟨57992501915666485630954973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38661667943777657087303315 57992501915666485630954973)
      ·
        refine ⟨21747188218374932111608115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57992501915666485630954973 21747188218374932111608115)
        ·
          refine ⟨32620782327562398167412173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21747188218374932111608115 32620782327562398167412173)
          ·
            refine ⟨12232793372835899312779565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32620782327562398167412173 12232793372835899312779565)
            ·
              refine ⟨4587297514813462242292337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12232793372835899312779565 4587297514813462242292337)
              ·
                refine ⟨3440473136110096681719253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4587297514813462242292337 3440473136110096681719253)
                ·
                  refine ⟨80636089127580390977795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3440473136110096681719253 80636089127580390977795)
                  ·
                    rfl

theorem cell23_1413344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 7].length) (baseStart_1413344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413344 prefixEnd_1413344 := by exact prefixLift 1413344
  have htrace : WordTrace (prefixWord ++ tailWord_1413344) baseStart_1413344 baseEnd_1413344 := by
    simpa [prefixWord, tailWord_1413344, baseEnd_1413344] using wordTrace_append hprefix tailTrace_1413344
  have hstable : (prefixWord ++ tailWord_1413344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413344).length < 2 ^ (prefixWord ++ tailWord_1413344).sum := by decide
  have hdescent : baseEnd_1413344 < baseStart_1413344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413361 : List Nat := [1, 2, 2, 2, 2, 1, 3, 5, 5]
def baseStart_1413361 : Nat := 118140960795 + 1413361 * 2 ^ 59
def prefixEnd_1413361 : Nat := 4983230072969 + 3 ^ 40 * 1413361 * 2
def baseEnd_1413361 : Nat := 80637059035483328031953

theorem tailTrace_1413361 : CollatzResearch.WordTrace tailWord_1413361 prefixEnd_1413361 80637059035483328031953 := by
  unfold tailWord_1413361
  simp only [CollatzResearch.WordTrace]
  refine ⟨51549510632641954686439937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34366340421761303124293291 51549510632641954686439937)
  ·
    refine ⟨38662132974481466014829953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51549510632641954686439937 38662132974481466014829953)
    ·
      refine ⟨28996599730861099511122465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38662132974481466014829953 28996599730861099511122465)
      ·
        refine ⟨21747449798145824633341849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28996599730861099511122465 21747449798145824633341849)
        ·
          refine ⟨16310587348609368475006387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21747449798145824633341849 16310587348609368475006387)
          ·
            refine ⟨24465881022914052712509581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16310587348609368475006387 24465881022914052712509581)
            ·
              refine ⟨9174705383592769767191093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24465881022914052712509581 9174705383592769767191093)
              ·
                refine ⟨860128629711822165674165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9174705383592769767191093 860128629711822165674165)
                ·
                  refine ⟨80637059035483328031953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 860128629711822165674165 80637059035483328031953)
                  ·
                    rfl

theorem cell23_1413361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 5].length) (baseStart_1413361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413361 prefixEnd_1413361 := by exact prefixLift 1413361
  have htrace : WordTrace (prefixWord ++ tailWord_1413361) baseStart_1413361 baseEnd_1413361 := by
    simpa [prefixWord, tailWord_1413361, baseEnd_1413361] using wordTrace_append hprefix tailTrace_1413361
  have hstable : (prefixWord ++ tailWord_1413361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413361).length < 2 ^ (prefixWord ++ tailWord_1413361).sum := by decide
  have hdescent : baseEnd_1413361 < baseStart_1413361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413372 : List Nat := [2, 2, 2, 1, 4, 3, 1, 2, 2, 2, 2]
def baseStart_1413372 : Nat := 118140960795 + 1413372 * 2 ^ 59
def prefixEnd_1413372 : Nat := 4983230072969 + 3 ^ 40 * 1413372 * 2
def baseEnd_1413372 : Nat := 725739179606549409250027

theorem tailTrace_1413372 : CollatzResearch.WordTrace tailWord_1413372 prefixEnd_1413372 725739179606549409250027 := by
  unfold tailWord_1413372
  simp only [CollatzResearch.WordTrace]
  refine ⟨25774955917801051782545185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34366607890401402376726913 25774955917801051782545185)
  ·
    refine ⟨19331216938350788836908889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25774955917801051782545185 19331216938350788836908889)
    ·
      refine ⟨14498412703763091627681667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19331216938350788836908889 14498412703763091627681667)
      ·
        refine ⟨21747619055644637441522501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14498412703763091627681667 21747619055644637441522501)
        ·
          refine ⟨4077678572933369520285469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21747619055644637441522501 4077678572933369520285469)
          ·
            refine ⟨1529129464850013570107051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4077678572933369520285469 1529129464850013570107051)
            ·
              refine ⟨2293694197275020355160577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1529129464850013570107051 2293694197275020355160577)
              ·
                refine ⟨1720270647956265266370433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2293694197275020355160577 1720270647956265266370433)
                ·
                  refine ⟨1290202985967198949777825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1720270647956265266370433 1290202985967198949777825)
                  ·
                    refine ⟨967652239475399212333369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1290202985967198949777825 967652239475399212333369)
                    ·
                      refine ⟨725739179606549409250027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 967652239475399212333369 725739179606549409250027)
                      ·
                        rfl

theorem cell23_1413372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 2, 2, 2].length) (baseStart_1413372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413372 prefixEnd_1413372 := by exact prefixLift 1413372
  have htrace : WordTrace (prefixWord ++ tailWord_1413372) baseStart_1413372 baseEnd_1413372 := by
    simpa [prefixWord, tailWord_1413372, baseEnd_1413372] using wordTrace_append hprefix tailTrace_1413372
  have hstable : (prefixWord ++ tailWord_1413372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413372).length < 2 ^ (prefixWord ++ tailWord_1413372).sum := by decide
  have hdescent : baseEnd_1413372 < baseStart_1413372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413378 : List Nat := [3, 4, 1, 1, 2, 2, 2, 1, 7]
def baseStart_1413378 : Nat := 118140960795 + 1413378 * 2 ^ 59
def prefixEnd_1413378 : Nat := 4983230072969 + 3 ^ 40 * 1413378 * 2
def baseEnd_1413378 : Nat := 80638028943386265086111

theorem tailTrace_1413378 : CollatzResearch.WordTrace tailWord_1413378 prefixEnd_1413378 80638028943386265086111 := by
  unfold tailWord_1413378
  simp only [CollatzResearch.WordTrace]
  refine ⟨12887532668395091647452197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34366753782386911059872525 12887532668395091647452197)
  ·
    refine ⟨2416412375324079683897287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12887532668395091647452197 2416412375324079683897287)
    ·
      refine ⟨3624618562986119525845931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2416412375324079683897287 3624618562986119525845931)
      ·
        refine ⟨5436927844479179288768897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3624618562986119525845931 5436927844479179288768897)
        ·
          refine ⟨4077695883359384466576673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5436927844479179288768897 4077695883359384466576673)
          ·
            refine ⟨3058271912519538349932505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4077695883359384466576673 3058271912519538349932505)
            ·
              refine ⟨2293703934389653762449379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3058271912519538349932505 2293703934389653762449379)
              ·
                refine ⟨3440555901584480643674069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2293703934389653762449379 3440555901584480643674069)
                ·
                  refine ⟨80638028943386265086111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3440555901584480643674069 80638028943386265086111)
                  ·
                    rfl

theorem cell23_1413378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_1413378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413378 prefixEnd_1413378 := by exact prefixLift 1413378
  have htrace : WordTrace (prefixWord ++ tailWord_1413378) baseStart_1413378 baseEnd_1413378 := by
    simpa [prefixWord, tailWord_1413378, baseEnd_1413378] using wordTrace_append hprefix tailTrace_1413378
  have hstable : (prefixWord ++ tailWord_1413378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413378).length < 2 ^ (prefixWord ++ tailWord_1413378).sum := by decide
  have hdescent : baseEnd_1413378 < baseStart_1413378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413381 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 2, 5, 2]
def baseStart_1413381 : Nat := 118140960795 + 1413381 * 2 ^ 59
def prefixEnd_1413381 : Nat := 4983230072969 + 3 ^ 40 * 1413381 * 2
def baseEnd_1413381 : Nat := 725743800932439874037485

theorem tailTrace_1413381 : CollatzResearch.WordTrace tailWord_1413381 prefixEnd_1413381 725743800932439874037485 := by
  unfold tailWord_1413381
  simp only [CollatzResearch.WordTrace]
  refine ⟨51550240092569498102167997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34366826728379665401445331 51550240092569498102167997)
  ·
    refine ⟨19331340034713561788312999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51550240092569498102167997 19331340034713561788312999)
    ·
      refine ⟨28997010052070342682469499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19331340034713561788312999 28997010052070342682469499)
      ·
        refine ⟨43495515078105514023704249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28997010052070342682469499 43495515078105514023704249)
        ·
          refine ⟨32621636308579135517778187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43495515078105514023704249 32621636308579135517778187)
          ·
            refine ⟨48932454462868703276667281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32621636308579135517778187 48932454462868703276667281)
            ·
              refine ⟨36699340847151527457500461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48932454462868703276667281 36699340847151527457500461)
              ·
                refine ⟨13762252817681822796562673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36699340847151527457500461 13762252817681822796562673)
                ·
                  refine ⟨10321689613261367097422005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13762252817681822796562673 10321689613261367097422005)
                  ·
                    refine ⟨967658401243253165383313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10321689613261367097422005 967658401243253165383313)
                    ·
                      refine ⟨725743800932439874037485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 967658401243253165383313 725743800932439874037485)
                      ·
                        rfl

theorem cell23_1413381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 5, 2].length) (baseStart_1413381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413381 prefixEnd_1413381 := by exact prefixLift 1413381
  have htrace : WordTrace (prefixWord ++ tailWord_1413381) baseStart_1413381 baseEnd_1413381 := by
    simpa [prefixWord, tailWord_1413381, baseEnd_1413381] using wordTrace_append hprefix tailTrace_1413381
  have hstable : (prefixWord ++ tailWord_1413381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413381).length < 2 ^ (prefixWord ++ tailWord_1413381).sum := by decide
  have hdescent : baseEnd_1413381 < baseStart_1413381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413404 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 1, 10]
def baseStart_1413404 : Nat := 118140960795 + 1413404 * 2 ^ 59
def prefixEnd_1413404 : Nat := 4983230072969 + 3 ^ 40 * 1413404 * 2
def baseEnd_1413404 : Nat := 241918536995831094683293

theorem tailTrace_1413404 : CollatzResearch.WordTrace tailWord_1413404 prefixEnd_1413404 241918536995831094683293 := by
  unfold tailWord_1413404
  simp only [CollatzResearch.WordTrace]
  refine ⟨25775539485743086515127633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34367385980990782020170177 25775539485743086515127633)
  ·
    refine ⟨19331654614307314886345725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25775539485743086515127633 19331654614307314886345725)
    ·
      refine ⟨7249370480365243082379647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19331654614307314886345725 7249370480365243082379647)
      ·
        refine ⟨10874055720547864623569471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7249370480365243082379647 10874055720547864623569471)
        ·
          refine ⟨16311083580821796935354207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10874055720547864623569471 16311083580821796935354207)
          ·
            refine ⟨24466625371232695403031311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16311083580821796935354207 24466625371232695403031311)
            ·
              refine ⟨36699938056849043104546967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24466625371232695403031311 36699938056849043104546967)
              ·
                refine ⟨55049907085273564656820451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36699938056849043104546967 55049907085273564656820451)
                ·
                  refine ⟨82574860627910346985230677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55049907085273564656820451 82574860627910346985230677)
                  ·
                    refine ⟨241918536995831094683293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 82574860627910346985230677 241918536995831094683293)
                    ·
                      rfl

theorem cell23_1413404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_1413404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413404 prefixEnd_1413404 := by exact prefixLift 1413404
  have htrace : WordTrace (prefixWord ++ tailWord_1413404) baseStart_1413404 baseEnd_1413404 := by
    simpa [prefixWord, tailWord_1413404, baseEnd_1413404] using wordTrace_append hprefix tailTrace_1413404
  have hstable : (prefixWord ++ tailWord_1413404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413404).length < 2 ^ (prefixWord ++ tailWord_1413404).sum := by decide
  have hdescent : baseEnd_1413404 < baseStart_1413404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413411 : List Nat := [1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 4]
def baseStart_1413411 : Nat := 118140960795 + 1413411 * 2 ^ 59
def prefixEnd_1413411 : Nat := 4983230072969 + 3 ^ 40 * 1413411 * 2
def baseEnd_1413411 : Nat := 725759205352074756662347

theorem tailTrace_1413411 : CollatzResearch.WordTrace tailWord_1413411 prefixEnd_1413411 725759205352074756662347 := by
  unfold tailWord_1413411
  simp only [CollatzResearch.WordTrace]
  refine ⟨51551334282460813225760087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34367556188307208817173391 51551334282460813225760087)
  ·
    refine ⟨77327001423691219838640131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51551334282460813225760087 77327001423691219838640131)
    ·
      refine ⟨115990502135536829757960197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77327001423691219838640131 115990502135536829757960197)
      ·
        refine ⟨21748219150413155579617537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115990502135536829757960197 21748219150413155579617537)
        ·
          refine ⟨16311164362809866684713153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21748219150413155579617537 16311164362809866684713153)
          ·
            refine ⟨12233373272107400013534865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16311164362809866684713153 12233373272107400013534865)
            ·
              refine ⟨9175029954080550010151149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12233373272107400013534865 9175029954080550010151149)
              ·
                refine ⟨3440636232780206253806681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9175029954080550010151149 3440636232780206253806681)
                ·
                  refine ⟨2580477174585154690355011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3440636232780206253806681 2580477174585154690355011)
                  ·
                    refine ⟨3870715761877732035532517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2580477174585154690355011 3870715761877732035532517)
                    ·
                      refine ⟨725759205352074756662347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3870715761877732035532517 725759205352074756662347)
                      ·
                        rfl

theorem cell23_1413411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_1413411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413411 prefixEnd_1413411 := by exact prefixLift 1413411
  have htrace : WordTrace (prefixWord ++ tailWord_1413411) baseStart_1413411 baseEnd_1413411 := by
    simpa [prefixWord, tailWord_1413411, baseEnd_1413411] using wordTrace_append hprefix tailTrace_1413411
  have hstable : (prefixWord ++ tailWord_1413411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413411).length < 2 ^ (prefixWord ++ tailWord_1413411).sum := by decide
  have hdescent : baseEnd_1413411 < baseStart_1413411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413424 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 6]
def baseStart_1413424 : Nat := 118140960795 + 1413424 * 2 ^ 59
def prefixEnd_1413424 : Nat := 4983230072969 + 3 ^ 40 * 1413424 * 2
def baseEnd_1413424 : Nat := 725765880600583205799787

theorem tailTrace_1413424 : CollatzResearch.WordTrace tailWord_1413424 prefixEnd_1413424 725765880600583205799787 := by
  unfold tailWord_1413424
  simp only [CollatzResearch.WordTrace]
  refine ⟨25775904215706858222991663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34367872287609144297322217 25775904215706858222991663)
  ·
    refine ⟨38663856323560287334487495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25775904215706858222991663 38663856323560287334487495)
    ·
      refine ⟨57995784485340431001731243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38663856323560287334487495 57995784485340431001731243)
      ·
        refine ⟨86993676728010646502596865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57995784485340431001731243 86993676728010646502596865)
        ·
          refine ⟨65245257546007984876947649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86993676728010646502596865 65245257546007984876947649)
          ·
            refine ⟨48933943159505988657710737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65245257546007984876947649 48933943159505988657710737)
            ·
              refine ⟨36700457369629491493283053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48933943159505988657710737 36700457369629491493283053)
              ·
                refine ⟨13762671513611059309981145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36700457369629491493283053 13762671513611059309981145)
                ·
                  refine ⟨10322003635208294482485859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13762671513611059309981145 10322003635208294482485859)
                  ·
                    refine ⟨15483005452812441723728789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10322003635208294482485859 15483005452812441723728789)
                    ·
                      refine ⟨725765880600583205799787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15483005452812441723728789 725765880600583205799787)
                      ·
                        rfl

theorem cell23_1413424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 6].length) (baseStart_1413424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413424 prefixEnd_1413424 := by exact prefixLift 1413424
  have htrace : WordTrace (prefixWord ++ tailWord_1413424) baseStart_1413424 baseEnd_1413424 := by
    simpa [prefixWord, tailWord_1413424, baseEnd_1413424] using wordTrace_append hprefix tailTrace_1413424
  have hstable : (prefixWord ++ tailWord_1413424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413424).length < 2 ^ (prefixWord ++ tailWord_1413424).sum := by decide
  have hdescent : baseEnd_1413424 < baseStart_1413424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413428 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_1413428 : Nat := 118140960795 + 1413428 * 2 ^ 59
def prefixEnd_1413428 : Nat := 4983230072969 + 3 ^ 40 * 1413428 * 2
def baseEnd_1413428 : Nat := 725767934523201190149769

theorem tailTrace_1413428 : CollatzResearch.WordTrace tailWord_1413428 prefixEnd_1413428 725767934523201190149769 := by
  unfold tailWord_1413428
  simp only [CollatzResearch.WordTrace]
  refine ⟨25775977161699612564564469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34367969548932816752752625 25775977161699612564564469)
  ·
    refine ⟨2416497858909338677927919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25775977161699612564564469 2416497858909338677927919)
    ·
      refine ⟨3624746788364008016891879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2416497858909338677927919 3624746788364008016891879)
      ·
        refine ⟨5437120182546012025337819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3624746788364008016891879 5437120182546012025337819)
        ·
          refine ⟨8155680273819018038006729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5437120182546012025337819 8155680273819018038006729)
          ·
            refine ⟨6116760205364263528505047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8155680273819018038006729 6116760205364263528505047)
            ·
              refine ⟨9175140308046395292757571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6116760205364263528505047 9175140308046395292757571)
              ·
                refine ⟨13762710462069592939136357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9175140308046395292757571 13762710462069592939136357)
                ·
                  refine ⟨2580508211638048676088067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13762710462069592939136357 2580508211638048676088067)
                  ·
                    refine ⟨3870762317457073014132101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2580508211638048676088067 3870762317457073014132101)
                    ·
                      refine ⟨725767934523201190149769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3870762317457073014132101 725767934523201190149769)
                      ·
                        rfl

theorem cell23_1413428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_1413428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413428 prefixEnd_1413428 := by exact prefixLift 1413428
  have htrace : WordTrace (prefixWord ++ tailWord_1413428) baseStart_1413428 baseEnd_1413428 := by
    simpa [prefixWord, tailWord_1413428, baseEnd_1413428] using wordTrace_append hprefix tailTrace_1413428
  have hstable : (prefixWord ++ tailWord_1413428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413428).length < 2 ^ (prefixWord ++ tailWord_1413428).sum := by decide
  have hdescent : baseEnd_1413428 < baseStart_1413428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413528 : List Nat := [2, 1, 2, 5, 1, 1, 2, 2, 1, 6]
def baseStart_1413528 : Nat := 118140960795 + 1413528 * 2 ^ 59
def prefixEnd_1413528 : Nat := 4983230072969 + 3 ^ 40 * 1413528 * 2
def baseEnd_1413528 : Nat := 241939760862883599633103

theorem tailTrace_1413528 : CollatzResearch.WordTrace tailWord_1413528 prefixEnd_1413528 241939760862883599633103 := by
  unfold tailWord_1413528
  simp only [CollatzResearch.WordTrace]
  refine ⟨25777800811518471103884619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34370401082024628138512825 25777800811518471103884619)
  ·
    refine ⟨38666701217277706655826929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25777800811518471103884619 38666701217277706655826929)
    ·
      refine ⟨29000025912958279991870197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38666701217277706655826929 29000025912958279991870197)
      ·
        refine ⟨2718752429339838749237831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29000025912958279991870197 2718752429339838749237831)
        ·
          refine ⟨4078128644009758123856747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2718752429339838749237831 4078128644009758123856747)
          ·
            refine ⟨6117192966014637185785121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4078128644009758123856747 6117192966014637185785121)
            ·
              refine ⟨4587894724510977889338841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6117192966014637185785121 4587894724510977889338841)
              ·
                refine ⟨3440921043383233417004131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4587894724510977889338841 3440921043383233417004131)
                ·
                  refine ⟨5161381565074850125506197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3440921043383233417004131 5161381565074850125506197)
                  ·
                    refine ⟨241939760862883599633103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5161381565074850125506197 241939760862883599633103)
                    ·
                      rfl

theorem cell23_1413528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 1, 6].length) (baseStart_1413528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413528 prefixEnd_1413528 := by exact prefixLift 1413528
  have htrace : WordTrace (prefixWord ++ tailWord_1413528) baseStart_1413528 baseEnd_1413528 := by
    simpa [prefixWord, tailWord_1413528, baseEnd_1413528] using wordTrace_append hprefix tailTrace_1413528
  have hstable : (prefixWord ++ tailWord_1413528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413528).length < 2 ^ (prefixWord ++ tailWord_1413528).sum := by decide
  have hdescent : baseEnd_1413528 < baseStart_1413528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413535 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 5, 2, 2]
def baseStart_1413535 : Nat := 118140960795 + 1413535 * 2 ^ 59
def prefixEnd_1413535 : Nat := 4983230072969 + 3 ^ 40 * 1413535 * 2
def baseEnd_1413535 : Nat := 725822876953232271511777

theorem tailTrace_1413535 : CollatzResearch.WordTrace tailWord_1413535 prefixEnd_1413535 725822876953232271511777 := by
  unfold tailWord_1413535
  simp only [CollatzResearch.WordTrace]
  refine ⟨51555856934011582403274059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34370571289341054935516039 51555856934011582403274059)
  ·
    refine ⟨77333785401017373604911089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51555856934011582403274059 77333785401017373604911089)
    ·
      refine ⟨58000339050763030203683317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77333785401017373604911089 58000339050763030203683317)
      ·
        refine ⟨5437531786009034081595311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58000339050763030203683317 5437531786009034081595311)
        ·
          refine ⟨8156297679013551122392967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5437531786009034081595311 8156297679013551122392967)
          ·
            refine ⟨12234446518520326683589451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8156297679013551122392967 12234446518520326683589451)
            ·
              refine ⟨18351669777780490025384177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12234446518520326683589451 18351669777780490025384177)
              ·
                refine ⟨13763752333335367519038133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18351669777780490025384177 13763752333335367519038133)
                ·
                  refine ⟨1290351781250190704909825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13763752333335367519038133 1290351781250190704909825)
                  ·
                    refine ⟨967763835937643028682369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1290351781250190704909825 967763835937643028682369)
                    ·
                      refine ⟨725822876953232271511777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 967763835937643028682369 725822876953232271511777)
                      ·
                        rfl

theorem cell23_1413535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_1413535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413535 prefixEnd_1413535 := by exact prefixLift 1413535
  have htrace : WordTrace (prefixWord ++ tailWord_1413535) baseStart_1413535 baseEnd_1413535 := by
    simpa [prefixWord, tailWord_1413535, baseEnd_1413535] using wordTrace_append hprefix tailTrace_1413535
  have hstable : (prefixWord ++ tailWord_1413535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413535).length < 2 ^ (prefixWord ++ tailWord_1413535).sum := by decide
  have hdescent : baseEnd_1413535 < baseStart_1413535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413538 : List Nat := [3, 3, 1, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_1413538 : Nat := 118140960795 + 1413538 * 2 ^ 59
def prefixEnd_1413538 : Nat := 4983230072969 + 3 ^ 40 * 1413538 * 2
def baseEnd_1413538 : Nat := 725824417395195759774263

theorem tailTrace_1413538 : CollatzResearch.WordTrace tailWord_1413538 prefixEnd_1413538 725824417395195759774263 := by
  unfold tailWord_1413538
  simp only [CollatzResearch.WordTrace]
  refine ⟨12888991588250178478908317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34370644235333809277088845 12888991588250178478908317)
  ·
    refine ⟨4833371845593816929590619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12888991588250178478908317 4833371845593816929590619)
    ·
      refine ⟨7250057768390725394385929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4833371845593816929590619 7250057768390725394385929)
      ·
        refine ⟨5437543326293044045789447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7250057768390725394385929 5437543326293044045789447)
        ·
          refine ⟨8156314989439566068684171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5437543326293044045789447 8156314989439566068684171)
          ·
            refine ⟨12234472484159349103026257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8156314989439566068684171 12234472484159349103026257)
            ·
              refine ⟨9175854363119511827269693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12234472484159349103026257 9175854363119511827269693)
              ·
                refine ⟨3440945386169816935226135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9175854363119511827269693 3440945386169816935226135)
                ·
                  refine ⟨5161418079254725402839203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3440945386169816935226135 5161418079254725402839203)
                  ·
                    refine ⟨7742127118882088104258805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5161418079254725402839203 7742127118882088104258805)
                    ·
                      refine ⟨725824417395195759774263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7742127118882088104258805 725824417395195759774263)
                      ·
                        rfl

theorem cell23_1413538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_1413538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413538 prefixEnd_1413538 := by exact prefixLift 1413538
  have htrace : WordTrace (prefixWord ++ tailWord_1413538) baseStart_1413538 baseEnd_1413538 := by
    simpa [prefixWord, tailWord_1413538, baseEnd_1413538] using wordTrace_append hprefix tailTrace_1413538
  have hstable : (prefixWord ++ tailWord_1413538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413538).length < 2 ^ (prefixWord ++ tailWord_1413538).sum := by decide
  have hdescent : baseEnd_1413538 < baseStart_1413538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413546 : List Nat := [3, 1, 6, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_1413546 : Nat := 118140960795 + 1413546 * 2 ^ 59
def prefixEnd_1413546 : Nat := 4983230072969 + 3 ^ 40 * 1413546 * 2
def baseEnd_1413546 : Nat := 725828525240431728474227

theorem tailTrace_1413546 : CollatzResearch.WordTrace tailWord_1413546 prefixEnd_1413546 725828525240431728474227 := by
  unfold tailWord_1413546
  simp only [CollatzResearch.WordTrace]
  refine ⟨12889064534242932820481123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34370838757981154187949661 12889064534242932820481123)
  ·
    refine ⟨19333596801364399230721685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12889064534242932820481123 19333596801364399230721685)
    ·
      refine ⟨906262350063956213940079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19333596801364399230721685 906262350063956213940079)
      ·
        refine ⟨1359393525095934320910119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 906262350063956213940079 1359393525095934320910119)
        ·
          refine ⟨2039090287643901481365179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1359393525095934320910119 2039090287643901481365179)
          ·
            refine ⟨3058635431465852222047769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2039090287643901481365179 3058635431465852222047769)
            ·
              refine ⟨2293976573599389166535827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3058635431465852222047769 2293976573599389166535827)
              ·
                refine ⟨3440964860399083749803741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2293976573599389166535827 3440964860399083749803741)
                ·
                  refine ⟨1290361822649656406176403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3440964860399083749803741 1290361822649656406176403)
                  ·
                    refine ⟨1935542733974484609264605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1290361822649656406176403 1935542733974484609264605)
                    ·
                      refine ⟨725828525240431728474227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1935542733974484609264605 725828525240431728474227)
                      ·
                        rfl

theorem cell23_1413546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_1413546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413546 prefixEnd_1413546 := by exact prefixLift 1413546
  have htrace : WordTrace (prefixWord ++ tailWord_1413546) baseStart_1413546 baseEnd_1413546 := by
    simpa [prefixWord, tailWord_1413546, baseEnd_1413546] using wordTrace_append hprefix tailTrace_1413546
  have hstable : (prefixWord ++ tailWord_1413546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413546).length < 2 ^ (prefixWord ++ tailWord_1413546).sum := by decide
  have hdescent : baseEnd_1413546 < baseStart_1413546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413551 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 3]
def baseStart_1413551 : Nat := 118140960795 + 1413551 * 2 ^ 59
def prefixEnd_1413551 : Nat := 4983230072969 + 3 ^ 40 * 1413551 * 2
def baseEnd_1413551 : Nat := 725831092643704208911703

theorem tailTrace_1413551 : CollatzResearch.WordTrace tailWord_1413551 prefixEnd_1413551 725831092643704208911703 := by
  unfold tailWord_1413551
  simp only [CollatzResearch.WordTrace]
  refine ⟨51556440501953617135856507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34370960334635744757237671 51556440501953617135856507)
  ·
    refine ⟨77334660752930425703784761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51556440501953617135856507 77334660752930425703784761)
    ·
      refine ⟨58000995564697819277838571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77334660752930425703784761 58000995564697819277838571)
      ·
        refine ⟨87001493347046728916757857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58000995564697819277838571 87001493347046728916757857)
        ·
          refine ⟨65251120010285046687568393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87001493347046728916757857 65251120010285046687568393)
          ·
            refine ⟨48938340007713785015676295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65251120010285046687568393 48938340007713785015676295)
            ·
              refine ⟨73407510011570677523514443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48938340007713785015676295 73407510011570677523514443)
              ·
                refine ⟨110111265017356016285271665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73407510011570677523514443 110111265017356016285271665)
                ·
                  refine ⟨82583448763017012213953749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110111265017356016285271665 82583448763017012213953749)
                  ·
                    refine ⟨1935549580383211223764541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 82583448763017012213953749 1935549580383211223764541)
                    ·
                      refine ⟨725831092643704208911703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1935549580383211223764541 725831092643704208911703)
                      ·
                        rfl

theorem cell23_1413551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 3].length) (baseStart_1413551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413551 prefixEnd_1413551 := by exact prefixLift 1413551
  have htrace : WordTrace (prefixWord ++ tailWord_1413551) baseStart_1413551 baseEnd_1413551 := by
    simpa [prefixWord, tailWord_1413551, baseEnd_1413551] using wordTrace_append hprefix tailTrace_1413551
  have hstable : (prefixWord ++ tailWord_1413551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413551).length < 2 ^ (prefixWord ++ tailWord_1413551).sum := by decide
  have hdescent : baseEnd_1413551 < baseStart_1413551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413565 : List Nat := [1, 4, 1, 2, 2, 4, 1, 1, 1, 2, 4]
def baseStart_1413565 : Nat := 118140960795 + 1413565 * 2 ^ 59
def prefixEnd_1413565 : Nat := 4983230072969 + 3 ^ 40 * 1413565 * 2
def baseEnd_1413565 : Nat := 725838281372867154136639

theorem tailTrace_1413565 : CollatzResearch.WordTrace tailWord_1413565 prefixEnd_1413565 725838281372867154136639 := by
  unfold tailWord_1413565
  simp only [CollatzResearch.WordTrace]
  refine ⟨51556951123902897526866149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34371300749268598351244099 51556951123902897526866149)
  ·
    refine ⟨9666928335731793286287403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51556951123902897526866149 9666928335731793286287403)
    ·
      refine ⟨14500392503597689929431105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9666928335731793286287403 14500392503597689929431105)
      ·
        refine ⟨10875294377698267447073329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14500392503597689929431105 10875294377698267447073329)
        ·
          refine ⟨8156470783273700585304997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10875294377698267447073329 8156470783273700585304997)
          ·
            refine ⟨1529338271863818859744687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8156470783273700585304997 1529338271863818859744687)
            ·
              refine ⟨2294007407795728289617031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1529338271863818859744687 2294007407795728289617031)
              ·
                refine ⟨3441011111693592434425547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2294007407795728289617031 3441011111693592434425547)
                ·
                  refine ⟨5161516667540388651638321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3441011111693592434425547 5161516667540388651638321)
                  ·
                    refine ⟨3871137500655291488728741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5161516667540388651638321 3871137500655291488728741)
                    ·
                      refine ⟨725838281372867154136639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3871137500655291488728741 725838281372867154136639)
                      ·
                        rfl

theorem cell23_1413565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_1413565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413565 prefixEnd_1413565 := by exact prefixLift 1413565
  have htrace : WordTrace (prefixWord ++ tailWord_1413565) baseStart_1413565 baseEnd_1413565 := by
    simpa [prefixWord, tailWord_1413565, baseEnd_1413565] using wordTrace_append hprefix tailTrace_1413565
  have hstable : (prefixWord ++ tailWord_1413565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413565).length < 2 ^ (prefixWord ++ tailWord_1413565).sum := by decide
  have hdescent : baseEnd_1413565 < baseStart_1413565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413591 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 4]
def baseStart_1413591 : Nat := 118140960795 + 1413591 * 2 ^ 59
def prefixEnd_1413591 : Nat := 4983230072969 + 3 ^ 40 * 1413591 * 2
def baseEnd_1413591 : Nat := 725851631869884052411519

theorem tailTrace_1413591 : CollatzResearch.WordTrace tailWord_1413591 prefixEnd_1413591 725851631869884052411519 := by
  unfold tailWord_1413591
  simp only [CollatzResearch.WordTrace]
  refine ⟨51557899421808703967312627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34371932947872469311541751 51557899421808703967312627)
  ·
    refine ⟨77336849132713055950968941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51557899421808703967312627 77336849132713055950968941)
    ·
      refine ⟨29001318424767395981613353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77336849132713055950968941 29001318424767395981613353)
      ·
        refine ⟨21750988818575546986210015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29001318424767395981613353 21750988818575546986210015)
        ·
          refine ⟨32626483227863320479315023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21750988818575546986210015 32626483227863320479315023)
          ·
            refine ⟨48939724841794980718972535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32626483227863320479315023 48939724841794980718972535)
            ·
              refine ⟨73409587262692471078458803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48939724841794980718972535 73409587262692471078458803)
              ·
                refine ⟨110114380894038706617688205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73409587262692471078458803 110114380894038706617688205)
                ·
                  refine ⟨41292892835264514981633077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110114380894038706617688205 41292892835264514981633077)
                  ·
                    refine ⟨3871208703306048279528101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41292892835264514981633077 3871208703306048279528101)
                    ·
                      refine ⟨725851631869884052411519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3871208703306048279528101 725851631869884052411519)
                      ·
                        rfl

theorem cell23_1413591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_1413591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413591 prefixEnd_1413591 := by exact prefixLift 1413591
  have htrace : WordTrace (prefixWord ++ tailWord_1413591) baseStart_1413591 baseEnd_1413591 := by
    simpa [prefixWord, tailWord_1413591, baseEnd_1413591] using wordTrace_append hprefix tailTrace_1413591
  have hstable : (prefixWord ++ tailWord_1413591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413591).length < 2 ^ (prefixWord ++ tailWord_1413591).sum := by decide
  have hdescent : baseEnd_1413591 < baseStart_1413591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413611 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 5]
def baseStart_1413611 : Nat := 118140960795 + 1413611 * 2 ^ 59
def prefixEnd_1413611 : Nat := 4983230072969 + 3 ^ 40 * 1413611 * 2
def baseEnd_1413611 : Nat := 725861901482973974161427

theorem tailTrace_1413611 : CollatzResearch.WordTrace tailWord_1413611 prefixEnd_1413611 725861901482973974161427 := by
  unfold tailWord_1413611
  simp only [CollatzResearch.WordTrace]
  refine ⟨51558628881736247383040687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34372419254490831588693791 51558628881736247383040687)
  ·
    refine ⟨77337943322604371074561031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51558628881736247383040687 77337943322604371074561031)
    ·
      refine ⟨116006914983906556611841547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77337943322604371074561031 116006914983906556611841547)
      ·
        refine ⟨174010372475859834917762321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116006914983906556611841547 174010372475859834917762321)
        ·
          refine ⟨130507779356894876188321741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174010372475859834917762321 130507779356894876188321741)
          ·
            refine ⟨48940417258835578570620653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130507779356894876188321741 48940417258835578570620653)
            ·
              refine ⟨18352656472063341963982745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48940417258835578570620653 18352656472063341963982745)
              ·
                refine ⟨13764492354047506472987059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18352656472063341963982745 13764492354047506472987059)
                ·
                  refine ⟨20646738531071259709480589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13764492354047506472987059 20646738531071259709480589)
                  ·
                    refine ⟨7742526949151722391055221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20646738531071259709480589 7742526949151722391055221)
                    ·
                      refine ⟨725861901482973974161427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7742526949151722391055221 725861901482973974161427)
                      ·
                        rfl

theorem cell23_1413611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 5].length) (baseStart_1413611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413611 prefixEnd_1413611 := by exact prefixLift 1413611
  have htrace : WordTrace (prefixWord ++ tailWord_1413611) baseStart_1413611 baseEnd_1413611 := by
    simpa [prefixWord, tailWord_1413611, baseEnd_1413611] using wordTrace_append hprefix tailTrace_1413611
  have hstable : (prefixWord ++ tailWord_1413611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413611).length < 2 ^ (prefixWord ++ tailWord_1413611).sum := by decide
  have hdescent : baseEnd_1413611 < baseStart_1413611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413631 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 9]
def baseStart_1413631 : Nat := 118140960795 + 1413631 * 2 ^ 59
def prefixEnd_1413631 : Nat := 4983230072969 + 3 ^ 40 * 1413631 * 2
def baseEnd_1413631 : Nat := 80652463455118210656815

theorem tailTrace_1413631 : CollatzResearch.WordTrace tailWord_1413631 prefixEnd_1413631 80652463455118210656815 := by
  unfold tailWord_1413631
  simp only [CollatzResearch.WordTrace]
  refine ⟨51559358341663790798768747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34372905561109193865845831 51559358341663790798768747)
  ·
    refine ⟨77339037512495686198153121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51559358341663790798768747 77339037512495686198153121)
    ·
      refine ⟨58004278134371764648614841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77339037512495686198153121 58004278134371764648614841)
      ·
        refine ⟨43503208600778823486461131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58004278134371764648614841 43503208600778823486461131)
        ·
          refine ⟨65254812901168235229691697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43503208600778823486461131 65254812901168235229691697)
          ·
            refine ⟨48941109675876176422268773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65254812901168235229691697 48941109675876176422268773)
            ·
              refine ⟨9176458064226783079175395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48941109675876176422268773 9176458064226783079175395)
              ·
                refine ⟨13764687096340174618763093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9176458064226783079175395 13764687096340174618763093)
                ·
                  refine ⟨80652463455118210656815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13764687096340174618763093 80652463455118210656815)
                  ·
                    rfl

theorem cell23_1413631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 9].length) (baseStart_1413631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413631 prefixEnd_1413631 := by exact prefixLift 1413631
  have htrace : WordTrace (prefixWord ++ tailWord_1413631) baseStart_1413631 baseEnd_1413631 := by
    simpa [prefixWord, tailWord_1413631, baseEnd_1413631] using wordTrace_append hprefix tailTrace_1413631
  have hstable : (prefixWord ++ tailWord_1413631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413631).length < 2 ^ (prefixWord ++ tailWord_1413631).sum := by decide
  have hdescent : baseEnd_1413631 < baseStart_1413631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413641 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 7]
def baseStart_1413641 : Nat := 118140960795 + 1413641 * 2 ^ 59
def prefixEnd_1413641 : Nat := 4983230072969 + 3 ^ 40 * 1413641 * 2
def baseEnd_1413641 : Nat := 725877305902608856786289

theorem tailTrace_1413641 : CollatzResearch.WordTrace tailWord_1413641 prefixEnd_1413641 725877305902608856786289 := by
  unfold tailWord_1413641
  simp only [CollatzResearch.WordTrace]
  refine ⟨51559723071627562506632777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34373148714418375004421851 51559723071627562506632777)
  ·
    refine ⟨38669792303720671879974583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51559723071627562506632777 38669792303720671879974583)
    ·
      refine ⟨58004688455581007819961875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38669792303720671879974583 58004688455581007819961875)
      ·
        refine ⟨87007032683371511729942813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58004688455581007819961875 87007032683371511729942813)
        ·
          refine ⟨32627637256264316898728555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87007032683371511729942813 32627637256264316898728555)
          ·
            refine ⟨48941455884396475348092833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32627637256264316898728555 48941455884396475348092833)
            ·
              refine ⟨36706091913297356511069625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48941455884396475348092833 36706091913297356511069625)
              ·
                refine ⟨27529568934973017383302219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36706091913297356511069625 27529568934973017383302219)
                ·
                  refine ⟨41294353402459526074953329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27529568934973017383302219 41294353402459526074953329)
                  ·
                    refine ⟨30970765051844644556214997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41294353402459526074953329 30970765051844644556214997)
                    ·
                      refine ⟨725877305902608856786289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 30970765051844644556214997 725877305902608856786289)
                      ·
                        rfl

theorem cell23_1413641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_1413641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413641 prefixEnd_1413641 := by exact prefixLift 1413641
  have htrace : WordTrace (prefixWord ++ tailWord_1413641) baseStart_1413641 baseEnd_1413641 := by
    simpa [prefixWord, tailWord_1413641, baseEnd_1413641] using wordTrace_append hprefix tailTrace_1413641
  have hstable : (prefixWord ++ tailWord_1413641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413641).length < 2 ^ (prefixWord ++ tailWord_1413641).sum := by decide
  have hdescent : baseEnd_1413641 < baseStart_1413641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413665 : List Nat := [1, 2, 3, 2, 2, 1, 3, 4, 5]
def baseStart_1413665 : Nat := 118140960795 + 1413665 * 2 ^ 59
def prefixEnd_1413665 : Nat := 4983230072969 + 3 ^ 40 * 1413665 * 2
def baseEnd_1413665 : Nat := 80654403270924084765131

theorem tailTrace_1413665 : CollatzResearch.WordTrace tailWord_1413665 prefixEnd_1413665 80654403270924084765131 := by
  unfold tailWord_1413665
  simp only [CollatzResearch.WordTrace]
  refine ⟨51560598423540614605506449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34373732282360409737004299 51560598423540614605506449)
  ·
    refine ⟨38670448817655460954129837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51560598423540614605506449 38670448817655460954129837)
    ·
      refine ⟨14501418306620797857798689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38670448817655460954129837 14501418306620797857798689)
      ·
        refine ⟨10876063729965598393349017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14501418306620797857798689 10876063729965598393349017)
        ·
          refine ⟨8157047797474198795011763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10876063729965598393349017 8157047797474198795011763)
          ·
            refine ⟨12235571696211298192517645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8157047797474198795011763 12235571696211298192517645)
            ·
              refine ⟨4588339386079236822194117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12235571696211298192517645 4588339386079236822194117)
              ·
                refine ⟨860313634889856904161397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4588339386079236822194117 860313634889856904161397)
                ·
                  refine ⟨80654403270924084765131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 860313634889856904161397 80654403270924084765131)
                  ·
                    rfl

theorem cell23_1413665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 5].length) (baseStart_1413665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413665 prefixEnd_1413665 := by exact prefixLift 1413665
  have htrace : WordTrace (prefixWord ++ tailWord_1413665) baseStart_1413665 baseEnd_1413665 := by
    simpa [prefixWord, tailWord_1413665, baseEnd_1413665] using wordTrace_append hprefix tailTrace_1413665
  have hstable : (prefixWord ++ tailWord_1413665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413665).length < 2 ^ (prefixWord ++ tailWord_1413665).sum := by decide
  have hdescent : baseEnd_1413665 < baseStart_1413665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413685 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 2, 5, 2]
def baseStart_1413685 : Nat := 118140960795 + 1413685 * 2 ^ 59
def prefixEnd_1413685 : Nat := 4983230072969 + 3 ^ 40 * 1413685 * 2
def baseEnd_1413685 : Nat := 725899899051406684636087

theorem tailTrace_1413685 : CollatzResearch.WordTrace tailWord_1413685 prefixEnd_1413685 725899899051406684636087 := by
  unfold tailWord_1413685
  simp only [CollatzResearch.WordTrace]
  refine ⟨51561327883468158021234509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34374218588978772014156339 51561327883468158021234509)
  ·
    refine ⟨19335497956300559257962941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51561327883468158021234509 19335497956300559257962941)
    ·
      refine ⟨7250811733612709721736103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19335497956300559257962941 7250811733612709721736103)
      ·
        refine ⟨10876217600419064582604155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7250811733612709721736103 10876217600419064582604155)
        ·
          refine ⟨16314326400628596873906233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10876217600419064582604155 16314326400628596873906233)
          ·
            refine ⟨12235744800471447655429675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16314326400628596873906233 12235744800471447655429675)
            ·
              refine ⟨18353617200707171483144513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12235744800471447655429675 18353617200707171483144513)
              ·
                refine ⟨13765212900530378612358385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18353617200707171483144513 13765212900530378612358385)
                ·
                  refine ⟨10323909675397783959268789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13765212900530378612358385 10323909675397783959268789)
                  ·
                    refine ⟨967866532068542246181449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10323909675397783959268789 967866532068542246181449)
                    ·
                      refine ⟨725899899051406684636087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 967866532068542246181449 725899899051406684636087)
                      ·
                        rfl

theorem cell23_1413685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_1413685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413685 prefixEnd_1413685 := by exact prefixLift 1413685
  have htrace : WordTrace (prefixWord ++ tailWord_1413685) baseStart_1413685 baseEnd_1413685 := by
    simpa [prefixWord, tailWord_1413685, baseEnd_1413685] using wordTrace_append hprefix tailTrace_1413685
  have hstable : (prefixWord ++ tailWord_1413685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413685).length < 2 ^ (prefixWord ++ tailWord_1413685).sum := by decide
  have hdescent : baseEnd_1413685 < baseStart_1413685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413742 : List Nat := [4, 1, 2, 2, 2, 1, 2, 2, 3, 4]
def baseStart_1413742 : Nat := 118140960795 + 1413742 * 2 ^ 59
def prefixEnd_1413742 : Nat := 4983230072969 + 3 ^ 40 * 1413742 * 2
def baseEnd_1413742 : Nat := 241976389149570987207775

theorem tailTrace_1413742 : CollatzResearch.WordTrace tailWord_1413742 prefixEnd_1413742 241976389149570987207775 := by
  unfold tailWord_1413742
  simp only [CollatzResearch.WordTrace]
  refine ⟨6445425855532707094507435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34375604562841104504039653 6445425855532707094507435)
  ·
    refine ⟨9668138783299060641761153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6445425855532707094507435 9668138783299060641761153)
    ·
      refine ⟨7251104087474295481320865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9668138783299060641761153 7251104087474295481320865)
      ·
        refine ⟨5438328065605721610990649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7251104087474295481320865 5438328065605721610990649)
        ·
          refine ⟨4078746049204291208242987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5438328065605721610990649 4078746049204291208242987)
          ·
            refine ⟨6118119073806436812364481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4078746049204291208242987 6118119073806436812364481)
            ·
              refine ⟨4588589305354827609273361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6118119073806436812364481 4588589305354827609273361)
              ·
                refine ⟨3441441979016120706955021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4588589305354827609273361 3441441979016120706955021)
                ·
                  refine ⟨1290540742131045265108133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3441441979016120706955021 1290540742131045265108133)
                  ·
                    refine ⟨241976389149570987207775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1290540742131045265108133 241976389149570987207775)
                    ·
                      rfl

theorem cell23_1413742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_1413742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413742 prefixEnd_1413742 := by exact prefixLift 1413742
  have htrace : WordTrace (prefixWord ++ tailWord_1413742) baseStart_1413742 baseEnd_1413742 := by
    simpa [prefixWord, tailWord_1413742, baseEnd_1413742] using wordTrace_append hprefix tailTrace_1413742
  have hstable : (prefixWord ++ tailWord_1413742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413742).length < 2 ^ (prefixWord ++ tailWord_1413742).sum := by decide
  have hdescent : baseEnd_1413742 < baseStart_1413742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413832 : List Nat := [2, 1, 3, 1, 2, 3, 1, 4, 2, 4]
def baseStart_1413832 : Nat := 118140960795 + 1413832 * 2 ^ 59
def prefixEnd_1413832 : Nat := 4983230072969 + 3 ^ 40 * 1413832 * 2
def baseEnd_1413832 : Nat := 241991793569205869832637

theorem tailTrace_1413832 : CollatzResearch.WordTrace tailWord_1413832 prefixEnd_1413832 241991793569205869832637 := by
  unfold tailWord_1413832
  simp only [CollatzResearch.WordTrace]
  refine ⟨25783344706967801063417875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34377792942623734751223833 25783344706967801063417875)
  ·
    refine ⟨38675017060451701595126813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25783344706967801063417875 38675017060451701595126813)
    ·
      refine ⟨14503131397669388098172555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38675017060451701595126813 14503131397669388098172555)
      ·
        refine ⟨21754697096504082147258833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14503131397669388098172555 21754697096504082147258833)
        ·
          refine ⟨16316022822378061610444125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21754697096504082147258833 16316022822378061610444125)
          ·
            refine ⟨6118508558391773103916547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16316022822378061610444125 6118508558391773103916547)
            ·
              refine ⟨9177762837587659655874821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6118508558391773103916547 9177762837587659655874821)
              ·
                refine ⟨1720830532047686185476529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9177762837587659655874821 1720830532047686185476529)
                ·
                  refine ⟨1290622899035764639107397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1720830532047686185476529 1290622899035764639107397)
                  ·
                    refine ⟨241991793569205869832637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1290622899035764639107397 241991793569205869832637)
                    ·
                      rfl

theorem cell23_1413832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_1413832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413832 prefixEnd_1413832 := by exact prefixLift 1413832
  have htrace : WordTrace (prefixWord ++ tailWord_1413832) baseStart_1413832 baseEnd_1413832 := by
    simpa [prefixWord, tailWord_1413832, baseEnd_1413832] using wordTrace_append hprefix tailTrace_1413832
  have hstable : (prefixWord ++ tailWord_1413832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413832).length < 2 ^ (prefixWord ++ tailWord_1413832).sum := by decide
  have hdescent : baseEnd_1413832 < baseStart_1413832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413872 : List Nat := [2, 1, 1, 1, 3, 1, 4, 2, 4, 1, 3]
def baseStart_1413872 : Nat := 118140960795 + 1413872 * 2 ^ 59
def prefixEnd_1413872 : Nat := 4983230072969 + 3 ^ 40 * 1413872 * 2
def baseEnd_1413872 : Nat := 725995919933797452997727

theorem tailTrace_1413872 : CollatzResearch.WordTrace tailWord_1413872 prefixEnd_1413872 725995919933797452997727 := by
  unfold tailWord_1413872
  simp only [CollatzResearch.WordTrace]
  refine ⟨25784074166895344479145935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34378765555860459305527913 25784074166895344479145935)
  ·
    refine ⟨38676111250343016718718903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25784074166895344479145935 38676111250343016718718903)
    ·
      refine ⟨58014166875514525078078355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38676111250343016718718903 58014166875514525078078355)
      ·
        refine ⟨87021250313271787617117533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58014166875514525078078355 87021250313271787617117533)
        ·
          refine ⟨32632968867476920356419075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87021250313271787617117533 32632968867476920356419075)
          ·
            refine ⟨48949453301215380534628613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32632968867476920356419075 48949453301215380534628613)
            ·
              refine ⟨9178022493977883850242865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48949453301215380534628613 9178022493977883850242865)
              ·
                refine ⟨6883516870483412887682149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9178022493977883850242865 6883516870483412887682149)
                ·
                  refine ⟨1290659413215639916440403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6883516870483412887682149 1290659413215639916440403)
                  ·
                    refine ⟨1935989119823459874660605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1290659413215639916440403 1935989119823459874660605)
                    ·
                      refine ⟨725995919933797452997727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1935989119823459874660605 725995919933797452997727)
                      ·
                        rfl

theorem cell23_1413872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 4, 1, 3].length) (baseStart_1413872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413872 prefixEnd_1413872 := by exact prefixLift 1413872
  have htrace : WordTrace (prefixWord ++ tailWord_1413872) baseStart_1413872 baseEnd_1413872 := by
    simpa [prefixWord, tailWord_1413872, baseEnd_1413872] using wordTrace_append hprefix tailTrace_1413872
  have hstable : (prefixWord ++ tailWord_1413872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413872).length < 2 ^ (prefixWord ++ tailWord_1413872).sum := by decide
  have hdescent : baseEnd_1413872 < baseStart_1413872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413905 : List Nat := [1, 2, 2, 1, 1, 3, 4, 1, 2, 6]
def baseStart_1413905 : Nat := 118140960795 + 1413905 * 2 ^ 59
def prefixEnd_1413905 : Nat := 4983230072969 + 3 ^ 40 * 1413905 * 2
def baseEnd_1413905 : Nat := 242004288265131941295025

theorem tailTrace_1413905 : CollatzResearch.WordTrace tailWord_1413905 prefixEnd_1413905 242004288265131941295025 := by
  unfold tailWord_1413905
  simp only [CollatzResearch.WordTrace]
  refine ⟨51569351942671135594243169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34379567961780757062828779 51569351942671135594243169)
  ·
    refine ⟨38677013957003351695682377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51569351942671135594243169 38677013957003351695682377)
    ·
      refine ⟨29007760467752513771761783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38677013957003351695682377 29007760467752513771761783)
      ·
        refine ⟨43511640701628770657642675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29007760467752513771761783 43511640701628770657642675)
        ·
          refine ⟨65267461052443155986464013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43511640701628770657642675 65267461052443155986464013)
          ·
            refine ⟨24475297894666183494924005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65267461052443155986464013 24475297894666183494924005)
            ·
              refine ⟨4589118355249909405298251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24475297894666183494924005 4589118355249909405298251)
              ·
                refine ⟨6883677532874864107947377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4589118355249909405298251 6883677532874864107947377)
                ·
                  refine ⟨5162758149656148080960533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6883677532874864107947377 5162758149656148080960533)
                  ·
                    refine ⟨242004288265131941295025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5162758149656148080960533 242004288265131941295025)
                    ·
                      rfl

theorem cell23_1413905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_1413905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413905 prefixEnd_1413905 := by exact prefixLift 1413905
  have htrace : WordTrace (prefixWord ++ tailWord_1413905) baseStart_1413905 baseEnd_1413905 := by
    simpa [prefixWord, tailWord_1413905, baseEnd_1413905] using wordTrace_append hprefix tailTrace_1413905
  have hstable : (prefixWord ++ tailWord_1413905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413905).length < 2 ^ (prefixWord ++ tailWord_1413905).sum := by decide
  have hdescent : baseEnd_1413905 < baseStart_1413905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413916 : List Nat := [2, 2, 3, 1, 1, 4, 2, 2, 1, 3, 2]
def baseStart_1413916 : Nat := 118140960795 + 1413916 * 2 ^ 59
def prefixEnd_1413916 : Nat := 4983230072969 + 3 ^ 40 * 1413916 * 2
def baseEnd_1413916 : Nat := 726018513082595280847525

theorem tailTrace_1413916 : CollatzResearch.WordTrace tailWord_1413916 prefixEnd_1413916 726018513082595280847525 := by
  unfold tailWord_1413916
  simp only [CollatzResearch.WordTrace]
  refine ⟨25784876572815642236446801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34379835430420856315262401 25784876572815642236446801)
  ·
    refine ⟨19338657429611731677335101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25784876572815642236446801 19338657429611731677335101)
    ·
      refine ⟨7251996536104399379000663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19338657429611731677335101 7251996536104399379000663)
      ·
        refine ⟨10877994804156599068500995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7251996536104399379000663 10877994804156599068500995)
        ·
          refine ⟨16316992206234898602751493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10877994804156599068500995 16316992206234898602751493)
          ·
            refine ⟨3059436038669043488015905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16316992206234898602751493 3059436038669043488015905)
            ·
              refine ⟨2294577029001782616011929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3059436038669043488015905 2294577029001782616011929)
              ·
                refine ⟨1720932771751336962008947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2294577029001782616011929 1720932771751336962008947)
                ·
                  refine ⟨2581399157627005443013421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1720932771751336962008947 2581399157627005443013421)
                  ·
                    refine ⟨968024684110127041130033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2581399157627005443013421 968024684110127041130033)
                    ·
                      refine ⟨726018513082595280847525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 968024684110127041130033 726018513082595280847525)
                      ·
                        rfl

theorem cell23_1413916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_1413916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413916 prefixEnd_1413916 := by exact prefixLift 1413916
  have htrace : WordTrace (prefixWord ++ tailWord_1413916) baseStart_1413916 baseEnd_1413916 := by
    simpa [prefixWord, tailWord_1413916, baseEnd_1413916] using wordTrace_append hprefix tailTrace_1413916
  have hstable : (prefixWord ++ tailWord_1413916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413916).length < 2 ^ (prefixWord ++ tailWord_1413916).sum := by decide
  have hdescent : baseEnd_1413916 < baseStart_1413916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413952 : List Nat := [2, 1, 1, 2, 2, 1, 1, 8, 5]
def baseStart_1413952 : Nat := 118140960795 + 1413952 * 2 ^ 59
def prefixEnd_1413952 : Nat := 4983230072969 + 3 ^ 40 * 1413952 * 2
def baseEnd_1413952 : Nat := 80670777598461904444151

theorem tailTrace_1413952 : CollatzResearch.WordTrace tailWord_1413952 prefixEnd_1413952 80670777598461904444151 := by
  unfold tailWord_1413952
  simp only [CollatzResearch.WordTrace]
  refine ⟨25785533086750431310602055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34380710782333908414136073 25785533086750431310602055)
  ·
    refine ⟨38678299630125646965903083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25785533086750431310602055 38678299630125646965903083)
    ·
      refine ⟨58017449445188470448854625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38678299630125646965903083 58017449445188470448854625)
      ·
        refine ⟨43513087083891352836640969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58017449445188470448854625 43513087083891352836640969)
        ·
          refine ⟨32634815312918514627480727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43513087083891352836640969 32634815312918514627480727)
          ·
            refine ⟨48952222969377771941221091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32634815312918514627480727 48952222969377771941221091)
            ·
              refine ⟨73428334454066657911831637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48952222969377771941221091 73428334454066657911831637)
              ·
                refine ⟨860488294383593647404277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 73428334454066657911831637 860488294383593647404277)
                ·
                  refine ⟨80670777598461904444151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 860488294383593647404277 80670777598461904444151)
                  ·
                    rfl

theorem cell23_1413952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 5].length) (baseStart_1413952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413952 prefixEnd_1413952 := by exact prefixLift 1413952
  have htrace : WordTrace (prefixWord ++ tailWord_1413952) baseStart_1413952 baseEnd_1413952 := by
    simpa [prefixWord, tailWord_1413952, baseEnd_1413952] using wordTrace_append hprefix tailTrace_1413952
  have hstable : (prefixWord ++ tailWord_1413952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413952).length < 2 ^ (prefixWord ++ tailWord_1413952).sum := by decide
  have hdescent : baseEnd_1413952 < baseStart_1413952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413992 : List Nat := [2, 1, 4, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_1413992 : Nat := 118140960795 + 1413992 * 2 ^ 59
def prefixEnd_1413992 : Nat := 4983230072969 + 3 ^ 40 * 1413992 * 2
def baseEnd_1413992 : Nat := 726057537612336983497175

theorem tailTrace_1413992 : CollatzResearch.WordTrace tailWord_1413992 prefixEnd_1413992 726057537612336983497175 := by
  unfold tailWord_1413992
  simp only [CollatzResearch.WordTrace]
  refine ⟨25786262546677974726330115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34381683395570632968440153 25786262546677974726330115)
  ·
    refine ⟨38679393820016962089495173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25786262546677974726330115 38679393820016962089495173)
    ·
      refine ⟨7252386341253180391780345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38679393820016962089495173 7252386341253180391780345)
      ·
        refine ⟨5439289755939885293835259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7252386341253180391780345 5439289755939885293835259)
        ·
          refine ⟨8158934633909827940752889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5439289755939885293835259 8158934633909827940752889)
          ·
            refine ⟨6119200975432370955564667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8158934633909827940752889 6119200975432370955564667)
            ·
              refine ⟨9178801463148556433347001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6119200975432370955564667 9178801463148556433347001)
              ·
                refine ⟨6884101097361417325010251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9178801463148556433347001 6884101097361417325010251)
                ·
                  refine ⟨10326151646042125987515377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6884101097361417325010251 10326151646042125987515377)
                  ·
                    refine ⟨7744613734531594490636533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10326151646042125987515377 7744613734531594490636533)
                    ·
                      refine ⟨726057537612336983497175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7744613734531594490636533 726057537612336983497175)
                      ·
                        rfl

theorem cell23_1413992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_1413992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1413992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1413992 prefixEnd_1413992 := by exact prefixLift 1413992
  have htrace : WordTrace (prefixWord ++ tailWord_1413992) baseStart_1413992 baseEnd_1413992 := by
    simpa [prefixWord, tailWord_1413992, baseEnd_1413992] using wordTrace_append hprefix tailTrace_1413992
  have hstable : (prefixWord ++ tailWord_1413992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413992).length < 2 ^ (prefixWord ++ tailWord_1413992).sum := by decide
  have hdescent : baseEnd_1413992 < baseStart_1413992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414006 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2]
def baseStart_1414006 : Nat := 118140960795 + 1414006 * 2 ^ 59
def prefixEnd_1414006 : Nat := 4983230072969 + 3 ^ 40 * 1414006 * 2
def baseEnd_1414006 : Nat := 726064726341499928722111

theorem tailTrace_1414006 : CollatzResearch.WordTrace tailWord_1414006 prefixEnd_1414006 726064726341499928722111 := by
  unfold tailWord_1414006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3223314732206576865229367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34382023810203486562446581 3223314732206576865229367)
  ·
    refine ⟨4834972098309865297844051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3223314732206576865229367 4834972098309865297844051)
    ·
      refine ⟨7252458147464797946766077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4834972098309865297844051 7252458147464797946766077)
      ·
        refine ⟨2719671805299299230037279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7252458147464797946766077 2719671805299299230037279)
        ·
          refine ⟨4079507707948948845055919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2719671805299299230037279 4079507707948948845055919)
          ·
            refine ⟨6119261561923423267583879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4079507707948948845055919 6119261561923423267583879)
            ·
              refine ⟨9178892342885134901375819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6119261561923423267583879 9178892342885134901375819)
              ·
                refine ⟨13768338514327702352063729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9178892342885134901375819 13768338514327702352063729)
                ·
                  refine ⟨10326253885745776764047797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13768338514327702352063729 10326253885745776764047797)
                  ·
                    refine ⟨968086301788666571629481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10326253885745776764047797 968086301788666571629481)
                    ·
                      refine ⟨726064726341499928722111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 968086301788666571629481 726064726341499928722111)
                      ·
                        rfl

theorem cell23_1414006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_1414006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414006 prefixEnd_1414006 := by exact prefixLift 1414006
  have htrace : WordTrace (prefixWord ++ tailWord_1414006) baseStart_1414006 baseEnd_1414006 := by
    simpa [prefixWord, tailWord_1414006, baseEnd_1414006] using wordTrace_append hprefix tailTrace_1414006
  have hstable : (prefixWord ++ tailWord_1414006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414006).length < 2 ^ (prefixWord ++ tailWord_1414006).sum := by decide
  have hdescent : baseEnd_1414006 < baseStart_1414006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414012 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 7, 4]
def baseStart_1414012 : Nat := 118140960795 + 1414012 * 2 ^ 59
def prefixEnd_1414012 : Nat := 4983230072969 + 3 ^ 40 * 1414012 * 2
def baseEnd_1414012 : Nat := 242022602408475635082361

theorem tailTrace_1414012 : CollatzResearch.WordTrace tailWord_1414012 prefixEnd_1414012 242022602408475635082361 := by
  unfold tailWord_1414012
  simp only [CollatzResearch.WordTrace]
  refine ⟨25786627276641746434194145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34382169702188995245592193 25786627276641746434194145)
  ·
    refine ⟨19339970457481309825645609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25786627276641746434194145 19339970457481309825645609)
    ·
      refine ⟨14504977843110982369234207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19339970457481309825645609 14504977843110982369234207)
      ·
        refine ⟨21757466764666473553851311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14504977843110982369234207 21757466764666473553851311)
        ·
          refine ⟨32636200146999710330776967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21757466764666473553851311 32636200146999710330776967)
          ·
            refine ⟨48954300220499565496165451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32636200146999710330776967 48954300220499565496165451)
            ·
              refine ⟨73431450330749348244248177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48954300220499565496165451 73431450330749348244248177)
              ·
                refine ⟨55073587748062011183186133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73431450330749348244248177 55073587748062011183186133)
                ·
                  refine ⟨1290787212845203387105925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 55073587748062011183186133 1290787212845203387105925)
                  ·
                    refine ⟨242022602408475635082361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1290787212845203387105925 242022602408475635082361)
                    ·
                      rfl

theorem cell23_1414012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_1414012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414012 prefixEnd_1414012 := by exact prefixLift 1414012
  have htrace : WordTrace (prefixWord ++ tailWord_1414012) baseStart_1414012 baseEnd_1414012 := by
    simpa [prefixWord, tailWord_1414012, baseEnd_1414012] using wordTrace_append hprefix tailTrace_1414012
  have hstable : (prefixWord ++ tailWord_1414012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414012).length < 2 ^ (prefixWord ++ tailWord_1414012).sum := by decide
  have hdescent : baseEnd_1414012 < baseStart_1414012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414019 : List Nat := [1, 1, 1, 3, 4, 1, 3, 1, 2, 4, 2]
def baseStart_1414019 : Nat := 118140960795 + 1414019 * 2 ^ 59
def prefixEnd_1414019 : Nat := 4983230072969 + 3 ^ 40 * 1414019 * 2
def baseEnd_1414019 : Nat := 726071401590008377859551

theorem tailTrace_1414019 : CollatzResearch.WordTrace tailWord_1414019 prefixEnd_1414019 726071401590008377859551 := by
  unfold tailWord_1414019
  simp only [CollatzResearch.WordTrace]
  refine ⟨51573509864258133063893111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34382339909505422042595407 51573509864258133063893111)
  ·
    refine ⟨77360264796387199595839667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51573509864258133063893111 77360264796387199595839667)
    ·
      refine ⟨116040397194580799393759501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77360264796387199595839667 116040397194580799393759501)
      ·
        refine ⟨43515148947967799772659813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116040397194580799393759501 43515148947967799772659813)
        ·
          refine ⟨8159090427743962457373715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43515148947967799772659813 8159090427743962457373715)
          ·
            refine ⟨12238635641615943686060573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8159090427743962457373715 12238635641615943686060573)
            ·
              refine ⟨4589488365605978882272715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12238635641615943686060573 4589488365605978882272715)
              ·
                refine ⟨6884232548408968323409073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4589488365605978882272715 6884232548408968323409073)
                ·
                  refine ⟨5163174411306726242556805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6884232548408968323409073 5163174411306726242556805)
                  ·
                    refine ⟨968095202120011170479401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5163174411306726242556805 968095202120011170479401)
                    ·
                      refine ⟨726071401590008377859551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 968095202120011170479401 726071401590008377859551)
                      ·
                        rfl

theorem cell23_1414019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 4, 2].length) (baseStart_1414019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414019 prefixEnd_1414019 := by exact prefixLift 1414019
  have htrace : WordTrace (prefixWord ++ tailWord_1414019) baseStart_1414019 baseEnd_1414019 := by
    simpa [prefixWord, tailWord_1414019, baseEnd_1414019] using wordTrace_append hprefix tailTrace_1414019
  have hstable : (prefixWord ++ tailWord_1414019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414019).length < 2 ^ (prefixWord ++ tailWord_1414019).sum := by decide
  have hdescent : baseEnd_1414019 < baseStart_1414019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414079 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 6, 3, 2]
def baseStart_1414079 : Nat := 118140960795 + 1414079 * 2 ^ 59
def prefixEnd_1414079 : Nat := 4983230072969 + 3 ^ 40 * 1414079 * 2
def baseEnd_1414079 : Nat := 726102210429278143109275

theorem tailTrace_1414079 : CollatzResearch.WordTrace tailWord_1414079 prefixEnd_1414079 726102210429278143109275 := by
  unfold tailWord_1414079
  simp only [CollatzResearch.WordTrace]
  refine ⟨51575698244040763311077291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34383798829360508874051527 51575698244040763311077291)
  ·
    refine ⟨77363547366061144966615937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51575698244040763311077291 77363547366061144966615937)
    ·
      refine ⟨58022660524545858724961953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77363547366061144966615937 58022660524545858724961953)
      ·
        refine ⟨43516995393409394043721465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58022660524545858724961953 43516995393409394043721465)
        ·
          refine ⟨32637746545057045532791099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43516995393409394043721465 32637746545057045532791099)
          ·
            refine ⟨48956619817585568299186649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32637746545057045532791099 48956619817585568299186649)
            ·
              refine ⟨36717464863189176224389987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48956619817585568299186649 36717464863189176224389987)
              ·
                refine ⟨55076197294783764336584981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36717464863189176224389987 55076197294783764336584981)
                ·
                  refine ⟨2581696748192988953277421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55076197294783764336584981 2581696748192988953277421)
                  ·
                    refine ⟨968136280572370857479033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2581696748192988953277421 968136280572370857479033)
                    ·
                      refine ⟨726102210429278143109275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 968136280572370857479033 726102210429278143109275)
                      ·
                        rfl

theorem cell23_1414079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 3, 2].length) (baseStart_1414079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414079 prefixEnd_1414079 := by exact prefixLift 1414079
  have htrace : WordTrace (prefixWord ++ tailWord_1414079) baseStart_1414079 baseEnd_1414079 := by
    simpa [prefixWord, tailWord_1414079, baseEnd_1414079] using wordTrace_append hprefix tailTrace_1414079
  have hstable : (prefixWord ++ tailWord_1414079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414079).length < 2 ^ (prefixWord ++ tailWord_1414079).sum := by decide
  have hdescent : baseEnd_1414079 < baseStart_1414079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
