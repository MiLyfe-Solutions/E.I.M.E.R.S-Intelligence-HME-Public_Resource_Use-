import V185TrunkScan23Chunk0218

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1295448 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 2, 6, 2]
def baseStart_1295448 : Nat := 118140960795 + 1295448 * 2 ^ 59
def prefixEnd_1295448 : Nat := 4983230072969 + 3 ^ 40 * 1295448 * 2
def baseEnd_1295448 : Nat := 665187486905752787442349

theorem tailTrace_1295448 : CollatzResearch.WordTrace tailWord_1295448 prefixEnd_1295448 665187486905752787442349 := by
  unfold tailWord_1295448
  simp only [CollatzResearch.WordTrace]
  refine ⟨23624435105410307874651499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31499246807213743832868665 23624435105410307874651499)
  ·
    refine ⟨35436652658115461811977249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23624435105410307874651499 35436652658115461811977249)
    ·
      refine ⟨26577489493586596358982937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35436652658115461811977249 26577489493586596358982937)
      ·
        refine ⟨19933117120189947269237203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26577489493586596358982937 19933117120189947269237203)
        ·
          refine ⟨29899675680284920903855805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19933117120189947269237203 29899675680284920903855805)
          ·
            refine ⟨11212378380106845338945927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29899675680284920903855805 11212378380106845338945927)
            ·
              refine ⟨16818567570160268008418891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11212378380106845338945927 16818567570160268008418891)
              ·
                refine ⟨25227851355240402012628337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16818567570160268008418891 25227851355240402012628337)
                ·
                  refine ⟨18920888516430301509471253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25227851355240402012628337 18920888516430301509471253)
                  ·
                    refine ⟨886916649207670383256465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18920888516430301509471253 886916649207670383256465)
                    ·
                      refine ⟨665187486905752787442349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 886916649207670383256465 665187486905752787442349)
                      ·
                        rfl

theorem cell23_1295448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 2, 6, 2].length) (baseStart_1295448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295448 prefixEnd_1295448 := by exact prefixLift 1295448
  have htrace : WordTrace (prefixWord ++ tailWord_1295448) baseStart_1295448 baseEnd_1295448 := by
    simpa [prefixWord, tailWord_1295448, baseEnd_1295448] using wordTrace_append hprefix tailTrace_1295448
  have hstable : (prefixWord ++ tailWord_1295448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295448).length < 2 ^ (prefixWord ++ tailWord_1295448).sum := by decide
  have hdescent : baseEnd_1295448 < baseStart_1295448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295468 : List Nat := [2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 5]
def baseStart_1295468 : Nat := 118140960795 + 1295468 * 2 ^ 59
def prefixEnd_1295468 : Nat := 4983230072969 + 3 ^ 40 * 1295468 * 2
def baseEnd_1295468 : Nat := 665197756518842709192257

theorem tailTrace_1295468 : CollatzResearch.WordTrace tailWord_1295468 prefixEnd_1295468 665197756518842709192257 := by
  unfold tailWord_1295468
  simp only [CollatzResearch.WordTrace]
  refine ⟨23624799835374079582515529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31499733113832106110020705 23624799835374079582515529)
  ·
    refine ⟨17718599876530559686886647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23624799835374079582515529 17718599876530559686886647)
    ·
      refine ⟨26577899814795839530329971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17718599876530559686886647 26577899814795839530329971)
      ·
        refine ⟨39866849722193759295494957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26577899814795839530329971 39866849722193759295494957)
        ·
          refine ⟨14950068645822659735810609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39866849722193759295494957 14950068645822659735810609)
          ·
            refine ⟨11212551484366994801857957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14950068645822659735810609 11212551484366994801857957)
            ·
              refine ⟨2102353403318811525348367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11212551484366994801857957 2102353403318811525348367)
              ·
                refine ⟨3153530104978217288022551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2102353403318811525348367 3153530104978217288022551)
                ·
                  refine ⟨4730295157467325932033827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3153530104978217288022551 4730295157467325932033827)
                  ·
                    refine ⟨7095442736200988898050741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4730295157467325932033827 7095442736200988898050741)
                    ·
                      refine ⟨665197756518842709192257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7095442736200988898050741 665197756518842709192257)
                      ·
                        rfl

theorem cell23_1295468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 5].length) (baseStart_1295468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295468 prefixEnd_1295468 := by exact prefixLift 1295468
  have htrace : WordTrace (prefixWord ++ tailWord_1295468) baseStart_1295468 baseEnd_1295468 := by
    simpa [prefixWord, tailWord_1295468, baseEnd_1295468] using wordTrace_append hprefix tailTrace_1295468
  have hstable : (prefixWord ++ tailWord_1295468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295468).length < 2 ^ (prefixWord ++ tailWord_1295468).sum := by decide
  have hdescent : baseEnd_1295468 < baseStart_1295468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295478 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_1295478 : Nat := 118140960795 + 1295478 * 2 ^ 59
def prefixEnd_1295478 : Nat := 4983230072969 + 3 ^ 40 * 1295478 * 2
def baseEnd_1295478 : Nat := 665202891325387670067211

theorem tailTrace_1295478 : CollatzResearch.WordTrace tailWord_1295478 prefixEnd_1295478 665202891325387670067211 := by
  unfold tailWord_1295478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2953122775044495679555943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31499976267141287248596725 2953122775044495679555943)
  ·
    refine ⟨4429684162566743519333915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2953122775044495679555943 4429684162566743519333915)
    ·
      refine ⟨6644526243850115279000873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4429684162566743519333915 6644526243850115279000873)
      ·
        refine ⟨4983394682887586459250655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6644526243850115279000873 4983394682887586459250655)
        ·
          refine ⟨7475092024331379688875983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4983394682887586459250655 7475092024331379688875983)
          ·
            refine ⟨11212638036497069533313975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7475092024331379688875983 11212638036497069533313975)
            ·
              refine ⟨16818957054745604299970963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11212638036497069533313975 16818957054745604299970963)
              ·
                refine ⟨25228435582118406449956445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16818957054745604299970963 25228435582118406449956445)
                ·
                  refine ⟨9460663343294402418733667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25228435582118406449956445 9460663343294402418733667)
                  ·
                    refine ⟨14190995014941603628100501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9460663343294402418733667 14190995014941603628100501)
                    ·
                      refine ⟨665202891325387670067211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14190995014941603628100501 665202891325387670067211)
                      ·
                        rfl

theorem cell23_1295478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_1295478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295478 prefixEnd_1295478 := by exact prefixLift 1295478
  have htrace : WordTrace (prefixWord ++ tailWord_1295478) baseStart_1295478 baseEnd_1295478 := by
    simpa [prefixWord, tailWord_1295478, baseEnd_1295478] using wordTrace_append hprefix tailTrace_1295478
  have hstable : (prefixWord ++ tailWord_1295478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295478).length < 2 ^ (prefixWord ++ tailWord_1295478).sum := by decide
  have hdescent : baseEnd_1295478 < baseStart_1295478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295491 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 6]
def baseStart_1295491 : Nat := 118140960795 + 1295491 * 2 ^ 59
def prefixEnd_1295491 : Nat := 4983230072969 + 3 ^ 40 * 1295491 * 2
def baseEnd_1295491 : Nat := 665209566573896119204651

theorem tailTrace_1295491 : CollatzResearch.WordTrace tailWord_1295491 prefixEnd_1295491 665209566573896119204651 := by
  unfold tailWord_1295491
  simp only [CollatzResearch.WordTrace]
  refine ⟨47250438549664834093118327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31500292366443222728745551 47250438549664834093118327)
  ·
    refine ⟨70875657824497251139677491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47250438549664834093118327 70875657824497251139677491)
    ·
      refine ⟨106313486736745876709516237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70875657824497251139677491 106313486736745876709516237)
      ·
        refine ⟨39867557526279703766068589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106313486736745876709516237 39867557526279703766068589)
        ·
          refine ⟨14950334072354888912275721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39867557526279703766068589 14950334072354888912275721)
          ·
            refine ⟨11212750554266166684206791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14950334072354888912275721 11212750554266166684206791)
            ·
              refine ⟨16819125831399250026310187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11212750554266166684206791 16819125831399250026310187)
              ·
                refine ⟨25228688747098875039465281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16819125831399250026310187 25228688747098875039465281)
                ·
                  refine ⟨18921516560324156279598961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25228688747098875039465281 18921516560324156279598961)
                  ·
                    refine ⟨14191137420243117209699221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18921516560324156279598961 14191137420243117209699221)
                    ·
                      refine ⟨665209566573896119204651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14191137420243117209699221 665209566573896119204651)
                      ·
                        rfl

theorem cell23_1295491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_1295491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295491 prefixEnd_1295491 := by exact prefixLift 1295491
  have htrace : WordTrace (prefixWord ++ tailWord_1295491) baseStart_1295491 baseEnd_1295491 := by
    simpa [prefixWord, tailWord_1295491, baseEnd_1295491] using wordTrace_append hprefix tailTrace_1295491
  have hstable : (prefixWord ++ tailWord_1295491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295491).length < 2 ^ (prefixWord ++ tailWord_1295491).sum := by decide
  have hdescent : baseEnd_1295491 < baseStart_1295491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295492 : List Nat := [2, 3, 2, 1, 2, 2, 4, 1, 2, 4]
def baseStart_1295492 : Nat := 118140960795 + 1295492 * 2 ^ 59
def prefixEnd_1295492 : Nat := 4983230072969 + 3 ^ 40 * 1295492 * 2
def baseEnd_1295492 : Nat := 221736693351516871764049

theorem tailTrace_1295492 : CollatzResearch.WordTrace tailWord_1295492 prefixEnd_1295492 221736693351516871764049 := by
  unfold tailWord_1295492
  simp only [CollatzResearch.WordTrace]
  refine ⟨23625237511330605631952365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31500316681774140842603153 23625237511330605631952365)
  ·
    refine ⟨8859464066748977111982137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23625237511330605631952365 8859464066748977111982137)
    ·
      refine ⟨6644598050061732833986603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8859464066748977111982137 6644598050061732833986603)
      ·
        refine ⟨9966897075092599250979905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6644598050061732833986603 9966897075092599250979905)
        ·
          refine ⟨7475172806319449438234929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9966897075092599250979905 7475172806319449438234929)
          ·
            refine ⟨5606379604739587078676197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7475172806319449438234929 5606379604739587078676197)
            ·
              refine ⟨1051196175888672577251787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5606379604739587078676197 1051196175888672577251787)
              ·
                refine ⟨1576794263833008865877681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1051196175888672577251787 1576794263833008865877681)
                ·
                  refine ⟨1182595697874756649408261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1576794263833008865877681 1182595697874756649408261)
                  ·
                    refine ⟨221736693351516871764049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1182595697874756649408261 221736693351516871764049)
                    ·
                      rfl

theorem cell23_1295492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_1295492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295492 prefixEnd_1295492 := by exact prefixLift 1295492
  have htrace : WordTrace (prefixWord ++ tailWord_1295492) baseStart_1295492 baseEnd_1295492 := by
    simpa [prefixWord, tailWord_1295492, baseEnd_1295492] using wordTrace_append hprefix tailTrace_1295492
  have hstable : (prefixWord ++ tailWord_1295492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295492).length < 2 ^ (prefixWord ++ tailWord_1295492).sum := by decide
  have hdescent : baseEnd_1295492 < baseStart_1295492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295502 : List Nat := [4, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3]
def baseStart_1295502 : Nat := 118140960795 + 1295502 * 2 ^ 59
def prefixEnd_1295502 : Nat := 4983230072969 + 3 ^ 40 * 1295502 * 2
def baseEnd_1295502 : Nat := 665215214861095576167101

theorem tailTrace_1295502 : CollatzResearch.WordTrace tailWord_1295502 prefixEnd_1295502 665215214861095576167101 := by
  unfold tailWord_1295502
  simp only [CollatzResearch.WordTrace]
  refine ⟨5906354969078122871471095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31500559835083321981179173 5906354969078122871471095)
  ·
    refine ⟨8859532453617184307206643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5906354969078122871471095 8859532453617184307206643)
    ·
      refine ⟨13289298680425776460809965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8859532453617184307206643 13289298680425776460809965)
      ·
        refine ⟨4983487005159666172803737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13289298680425776460809965 4983487005159666172803737)
        ·
          refine ⟨3737615253869749629602803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4983487005159666172803737 3737615253869749629602803)
          ·
            refine ⟨5606422880804624444404205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3737615253869749629602803 5606422880804624444404205)
            ·
              refine ⟨2102408580301734166651577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5606422880804624444404205 2102408580301734166651577)
              ·
                refine ⟨1576806435226300624988683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2102408580301734166651577 1576806435226300624988683)
                ·
                  refine ⟨2365209652839450937483025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1576806435226300624988683 2365209652839450937483025)
                  ·
                    refine ⟨1773907239629588203112269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2365209652839450937483025 1773907239629588203112269)
                    ·
                      refine ⟨665215214861095576167101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1773907239629588203112269 665215214861095576167101)
                      ·
                        rfl

theorem cell23_1295502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_1295502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295502 prefixEnd_1295502 := by exact prefixLift 1295502
  have htrace : WordTrace (prefixWord ++ tailWord_1295502) baseStart_1295502 baseEnd_1295502 := by
    simpa [prefixWord, tailWord_1295502, baseEnd_1295502] using wordTrace_append hprefix tailTrace_1295502
  have hstable : (prefixWord ++ tailWord_1295502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295502).length < 2 ^ (prefixWord ++ tailWord_1295502).sum := by decide
  have hdescent : baseEnd_1295502 < baseStart_1295502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295519 : List Nat := [1, 1, 2, 6, 2, 1, 3, 1, 1, 2, 3]
def baseStart_1295519 : Nat := 118140960795 + 1295519 * 2 ^ 59
def prefixEnd_1295519 : Nat := 4983230072969 + 3 ^ 40 * 1295519 * 2
def baseEnd_1295519 : Nat := 665223944032222009654523

theorem tailTrace_1295519 : CollatzResearch.WordTrace tailWord_1295519 prefixEnd_1295519 665223944032222009654523 := by
  unfold tailWord_1295519
  simp only [CollatzResearch.WordTrace]
  refine ⟨47251459793563394875137611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31500973195708929916758407 47251459793563394875137611)
  ·
    refine ⟨70877189690345092312706417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47251459793563394875137611 70877189690345092312706417)
    ·
      refine ⟨53157892267758819234529813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70877189690345092312706417 53157892267758819234529813)
      ·
        refine ⟨2491776200051194651618585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53157892267758819234529813 2491776200051194651618585)
        ·
          refine ⟨1868832150038395988713939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2491776200051194651618585 1868832150038395988713939)
          ·
            refine ⟨2803248225057593983070909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1868832150038395988713939 2803248225057593983070909)
            ·
              refine ⟨1051218084396597743651591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2803248225057593983070909 1051218084396597743651591)
              ·
                refine ⟨1576827126594896615477387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1051218084396597743651591 1576827126594896615477387)
                ·
                  refine ⟨2365240689892344923216081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1576827126594896615477387 2365240689892344923216081)
                  ·
                    refine ⟨1773930517419258692412061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2365240689892344923216081 1773930517419258692412061)
                    ·
                      refine ⟨665223944032222009654523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1773930517419258692412061 665223944032222009654523)
                      ·
                        rfl

theorem cell23_1295519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_1295519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295519 prefixEnd_1295519 := by exact prefixLift 1295519
  have htrace : WordTrace (prefixWord ++ tailWord_1295519) baseStart_1295519 baseEnd_1295519 := by
    simpa [prefixWord, tailWord_1295519, baseEnd_1295519] using wordTrace_append hprefix tailTrace_1295519
  have hstable : (prefixWord ++ tailWord_1295519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295519).length < 2 ^ (prefixWord ++ tailWord_1295519).sum := by decide
  have hdescent : baseEnd_1295519 < baseStart_1295519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295538 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4]
def baseStart_1295538 : Nat := 118140960795 + 1295538 * 2 ^ 59
def prefixEnd_1295538 : Nat := 4983230072969 + 3 ^ 40 * 1295538 * 2
def baseEnd_1295538 : Nat := 665233700164657435316935

theorem tailTrace_1295538 : CollatzResearch.WordTrace tailWord_1295538 prefixEnd_1295538 665233700164657435316935 := by
  unfold tailWord_1295538
  simp only [CollatzResearch.WordTrace]
  refine ⟨11813038195123640280019817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31501435186996374080052845 11813038195123640280019817)
  ·
    refine ⟨8859778646342730210014863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11813038195123640280019817 8859778646342730210014863)
    ·
      refine ⟨13289667969514095315022295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8859778646342730210014863 13289667969514095315022295)
      ·
        refine ⟨19934501954271142972533443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13289667969514095315022295 19934501954271142972533443)
        ·
          refine ⟨29901752931406714458800165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19934501954271142972533443 29901752931406714458800165)
          ·
            refine ⟨5606578674638758961025031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29901752931406714458800165 5606578674638758961025031)
            ·
              refine ⟨8409868011958138441537547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5606578674638758961025031 8409868011958138441537547)
              ·
                refine ⟨12614802017937207662306321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8409868011958138441537547 12614802017937207662306321)
                ·
                  refine ⟨9461101513452905746729741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12614802017937207662306321 9461101513452905746729741)
                  ·
                    refine ⟨3547913067544839655023653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9461101513452905746729741 3547913067544839655023653)
                    ·
                      refine ⟨665233700164657435316935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3547913067544839655023653 665233700164657435316935)
                      ·
                        rfl

theorem cell23_1295538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_1295538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295538 prefixEnd_1295538 := by exact prefixLift 1295538
  have htrace : WordTrace (prefixWord ++ tailWord_1295538) baseStart_1295538 baseEnd_1295538 := by
    simpa [prefixWord, tailWord_1295538, baseEnd_1295538] using wordTrace_append hprefix tailTrace_1295538
  have hstable : (prefixWord ++ tailWord_1295538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295538).length < 2 ^ (prefixWord ++ tailWord_1295538).sum := by decide
  have hdescent : baseEnd_1295538 < baseStart_1295538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295548 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 1, 8]
def baseStart_1295548 : Nat := 118140960795 + 1295548 * 2 ^ 59
def prefixEnd_1295548 : Nat := 4983230072969 + 3 ^ 40 * 1295548 * 2
def baseEnd_1295548 : Nat := 221746278323734132063963

theorem tailTrace_1295548 : CollatzResearch.WordTrace tailWord_1295548 prefixEnd_1295548 221746278323734132063963 := by
  unfold tailWord_1295548
  simp only [CollatzResearch.WordTrace]
  refine ⟨23626258755229166413971649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31501678340305555218628865 23626258755229166413971649)
  ·
    refine ⟨17719694066421874810478737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23626258755229166413971649 17719694066421874810478737)
    ·
      refine ⟨13289770549816406107859053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17719694066421874810478737 13289770549816406107859053)
      ·
        refine ⟨4983663956181152290447145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13289770549816406107859053 4983663956181152290447145)
        ·
          refine ⟨3737747967135864217835359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4983663956181152290447145 3737747967135864217835359)
          ·
            refine ⟨5606621950703796326753039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3737747967135864217835359 5606621950703796326753039)
            ·
              refine ⟨8409932926055694490129559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5606621950703796326753039 8409932926055694490129559)
              ·
                refine ⟨12614899389083541735194339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8409932926055694490129559 12614899389083541735194339)
                ·
                  refine ⟨18922349083625312602791509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12614899389083541735194339 18922349083625312602791509)
                  ·
                    refine ⟨221746278323734132063963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18922349083625312602791509 221746278323734132063963)
                    ·
                      rfl

theorem cell23_1295548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_1295548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295548 prefixEnd_1295548 := by exact prefixLift 1295548
  have htrace : WordTrace (prefixWord ++ tailWord_1295548) baseStart_1295548 baseEnd_1295548 := by
    simpa [prefixWord, tailWord_1295548, baseEnd_1295548] using wordTrace_append hprefix tailTrace_1295548
  have hstable : (prefixWord ++ tailWord_1295548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295548).length < 2 ^ (prefixWord ++ tailWord_1295548).sum := by decide
  have hdescent : baseEnd_1295548 < baseStart_1295548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295576 : List Nat := [2, 1, 2, 2, 5, 2, 2, 1, 1, 3, 2]
def baseStart_1295576 : Nat := 118140960795 + 1295576 * 2 ^ 59
def prefixEnd_1295576 : Nat := 4983230072969 + 3 ^ 40 * 1295576 * 2
def baseEnd_1295576 : Nat := 665253212429528286641761

theorem tailTrace_1295576 : CollatzResearch.WordTrace tailWord_1295576 prefixEnd_1295576 665253212429528286641761 := by
  unfold tailWord_1295576
  simp only [CollatzResearch.WordTrace]
  refine ⟨23626769377178446804981291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31502359169571262406641721 23626769377178446804981291)
  ·
    refine ⟨35440154065767670207471937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23626769377178446804981291 35440154065767670207471937)
    ·
      refine ⟨26580115549325752655603953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35440154065767670207471937 26580115549325752655603953)
      ·
        refine ⟨19935086661994314491702965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26580115549325752655603953 19935086661994314491702965)
        ·
          refine ⟨1868914374561966983597153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19935086661994314491702965 1868914374561966983597153)
          ·
            refine ⟨1401685780921475237697865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1868914374561966983597153 1401685780921475237697865)
            ·
              refine ⟨1051264335691106428273399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1401685780921475237697865 1051264335691106428273399)
              ·
                refine ⟨1576896503536659642410099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1051264335691106428273399 1576896503536659642410099)
                ·
                  refine ⟨2365344755304989463615149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1576896503536659642410099 2365344755304989463615149)
                  ·
                    refine ⟨887004283239371048855681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2365344755304989463615149 887004283239371048855681)
                    ·
                      refine ⟨665253212429528286641761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 887004283239371048855681 665253212429528286641761)
                      ·
                        rfl

theorem cell23_1295576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 1, 3, 2].length) (baseStart_1295576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295576 prefixEnd_1295576 := by exact prefixLift 1295576
  have htrace : WordTrace (prefixWord ++ tailWord_1295576) baseStart_1295576 baseEnd_1295576 := by
    simpa [prefixWord, tailWord_1295576, baseEnd_1295576] using wordTrace_append hprefix tailTrace_1295576
  have hstable : (prefixWord ++ tailWord_1295576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295576).length < 2 ^ (prefixWord ++ tailWord_1295576).sum := by decide
  have hdescent : baseEnd_1295576 < baseStart_1295576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295589 : List Nat := [1, 3, 1, 4, 3, 1, 1, 1, 4, 2, 2]
def baseStart_1295589 : Nat := 118140960795 + 1295589 * 2 ^ 59
def prefixEnd_1295589 : Nat := 4983230072969 + 3 ^ 40 * 1295589 * 2
def baseEnd_1295589 : Nat := 665259887678036735779201

theorem tailTrace_1295589 : CollatzResearch.WordTrace tailWord_1295589 prefixEnd_1295589 665259887678036735779201 := by
  unfold tailWord_1295589
  simp only [CollatzResearch.WordTrace]
  refine ⟨47254012903309796830185821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31502675268873197886790547 47254012903309796830185821)
  ·
    refine ⟨17720254838741173811319683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47254012903309796830185821 17720254838741173811319683)
    ·
      refine ⟨26580382258111760716979525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17720254838741173811319683 26580382258111760716979525)
      ·
        refine ⟨4983821673395955134433661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26580382258111760716979525 4983821673395955134433661)
        ·
          refine ⟨1868933127523483175412623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4983821673395955134433661 1868933127523483175412623)
          ·
            refine ⟨2803399691285224763118935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1868933127523483175412623 2803399691285224763118935)
            ·
              refine ⟨4205099536927837144678403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2803399691285224763118935 4205099536927837144678403)
              ·
                refine ⟨6307649305391755717017605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4205099536927837144678403 6307649305391755717017605)
                ·
                  refine ⟨1182684244760954196940801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6307649305391755717017605 1182684244760954196940801)
                  ·
                    refine ⟨887013183570715647705601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1182684244760954196940801 887013183570715647705601)
                    ·
                      refine ⟨665259887678036735779201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 887013183570715647705601 665259887678036735779201)
                      ·
                        rfl

theorem cell23_1295589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_1295589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295589 prefixEnd_1295589 := by exact prefixLift 1295589
  have htrace : WordTrace (prefixWord ++ tailWord_1295589) baseStart_1295589 baseEnd_1295589 := by
    simpa [prefixWord, tailWord_1295589, baseEnd_1295589] using wordTrace_append hprefix tailTrace_1295589
  have hstable : (prefixWord ++ tailWord_1295589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295589).length < 2 ^ (prefixWord ++ tailWord_1295589).sum := by decide
  have hdescent : baseEnd_1295589 < baseStart_1295589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295595 : List Nat := [1, 1, 1, 1, 2, 6, 2, 4, 5]
def baseStart_1295595 : Nat := 118140960795 + 1295595 * 2 ^ 59
def prefixEnd_1295595 : Nat := 4983230072969 + 3 ^ 40 * 1295595 * 2
def baseEnd_1295595 : Nat := 73918107617995968033797

theorem tailTrace_1295595 : CollatzResearch.WordTrace tailWord_1295595 prefixEnd_1295595 73918107617995968033797 := by
  unfold tailWord_1295595
  simp only [CollatzResearch.WordTrace]
  refine ⟨47254231741288059854904239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31502821160858706569936159 47254231741288059854904239)
  ·
    refine ⟨70881347611932089782356359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47254231741288059854904239 70881347611932089782356359)
    ·
      refine ⟨106322021417898134673534539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70881347611932089782356359 106322021417898134673534539)
      ·
        refine ⟨159483032126847202010301809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106322021417898134673534539 159483032126847202010301809)
        ·
          refine ⟨119612274095135401507726357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159483032126847202010301809 119612274095135401507726357)
          ·
            refine ⟨5606825348209471945674673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 119612274095135401507726357 5606825348209471945674673)
            ·
              refine ⟨4205119011157103959256005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5606825348209471945674673 4205119011157103959256005)
              ·
                refine ⟨788459814591956992360501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4205119011157103959256005 788459814591956992360501)
                ·
                  refine ⟨73918107617995968033797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 788459814591956992360501 73918107617995968033797)
                  ·
                    rfl

theorem cell23_1295595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 5].length) (baseStart_1295595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295595 prefixEnd_1295595 := by exact prefixLift 1295595
  have htrace : WordTrace (prefixWord ++ tailWord_1295595) baseStart_1295595 baseEnd_1295595 := by
    simpa [prefixWord, tailWord_1295595, baseEnd_1295595] using wordTrace_append hprefix tailTrace_1295595
  have hstable : (prefixWord ++ tailWord_1295595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295595).length < 2 ^ (prefixWord ++ tailWord_1295595).sum := by decide
  have hdescent : baseEnd_1295595 < baseStart_1295595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295646 : List Nat := [4, 3, 2, 1, 3, 1, 1, 1, 7]
def baseStart_1295646 : Nat := 118140960795 + 1295646 * 2 ^ 59
def prefixEnd_1295646 : Nat := 4983230072969 + 3 ^ 40 * 1295646 * 2
def baseEnd_1295646 : Nat := 73921017341704779196271

theorem tailTrace_1295646 : CollatzResearch.WordTrace tailWord_1295646 prefixEnd_1295646 73921017341704779196271 := by
  unfold tailWord_1295646
  simp only [CollatzResearch.WordTrace]
  refine ⟨5907011483012911945626349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31504061242735530376673861 5907011483012911945626349)
  ·
    refine ⟨2215129306129841979609881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5907011483012911945626349 2215129306129841979609881)
    ·
      refine ⟨1661346979597381484707411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2215129306129841979609881 1661346979597381484707411)
      ·
        refine ⟨2492020469396072227061117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1661346979597381484707411 2492020469396072227061117)
        ·
          refine ⟨934507676023527085147919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2492020469396072227061117 934507676023527085147919)
          ·
            refine ⟨1401761514035290627721879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 934507676023527085147919 1401761514035290627721879)
            ·
              refine ⟨2102642271052935941582819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1401761514035290627721879 2102642271052935941582819)
              ·
                refine ⟨3153963406579403912374229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2102642271052935941582819 3153963406579403912374229)
                ·
                  refine ⟨73921017341704779196271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3153963406579403912374229 73921017341704779196271)
                  ·
                    rfl

theorem cell23_1295646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_1295646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295646 prefixEnd_1295646 := by exact prefixLift 1295646
  have htrace : WordTrace (prefixWord ++ tailWord_1295646) baseStart_1295646 baseEnd_1295646 := by
    simpa [prefixWord, tailWord_1295646, baseEnd_1295646] using wordTrace_append hprefix tailTrace_1295646
  have hstable : (prefixWord ++ tailWord_1295646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295646).length < 2 ^ (prefixWord ++ tailWord_1295646).sum := by decide
  have hdescent : baseEnd_1295646 < baseStart_1295646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295688 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 1, 1, 8]
def baseStart_1295688 : Nat := 118140960795 + 1295688 * 2 ^ 59
def prefixEnd_1295688 : Nat := 4983230072969 + 3 ^ 40 * 1295688 * 2
def baseEnd_1295688 : Nat := 665310722262831848441245

theorem tailTrace_1295688 : CollatzResearch.WordTrace tailWord_1295688 prefixEnd_1295688 665310722262831848441245 := by
  unfold tailWord_1295688
  simp only [CollatzResearch.WordTrace]
  refine ⟨23628811864975568369019859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31505082486634091158693145 23628811864975568369019859)
  ·
    refine ⟨35443217797463352553529789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23628811864975568369019859 35443217797463352553529789)
    ·
      refine ⟨13291206674048757207573671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35443217797463352553529789 13291206674048757207573671)
      ·
        refine ⟨19936810011073135811360507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13291206674048757207573671 19936810011073135811360507)
        ·
          refine ⟨29905215016609703717040761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19936810011073135811360507 29905215016609703717040761)
          ·
            refine ⟨22428911262457277787780571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29905215016609703717040761 22428911262457277787780571)
            ·
              refine ⟨33643366893685916681670857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22428911262457277787780571 33643366893685916681670857)
              ·
                refine ⟨25232525170264437511253143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33643366893685916681670857 25232525170264437511253143)
                ·
                  refine ⟨37848787755396656266879715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25232525170264437511253143 37848787755396656266879715)
                  ·
                    refine ⟨56773181633094984400319573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37848787755396656266879715 56773181633094984400319573)
                    ·
                      refine ⟨665310722262831848441245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 56773181633094984400319573 665310722262831848441245)
                      ·
                        rfl

theorem cell23_1295688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_1295688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295688 prefixEnd_1295688 := by exact prefixLift 1295688
  have htrace : WordTrace (prefixWord ++ tailWord_1295688) baseStart_1295688 baseEnd_1295688 := by
    simpa [prefixWord, tailWord_1295688, baseEnd_1295688] using wordTrace_append hprefix tailTrace_1295688
  have hstable : (prefixWord ++ tailWord_1295688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295688).length < 2 ^ (prefixWord ++ tailWord_1295688).sum := by decide
  have hdescent : baseEnd_1295688 < baseStart_1295688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295715 : List Nat := [1, 1, 1, 5, 2, 2, 1, 2, 3, 5]
def baseStart_1295715 : Nat := 118140960795 + 1295715 * 2 ^ 59
def prefixEnd_1295715 : Nat := 4983230072969 + 3 ^ 40 * 1295715 * 2
def baseEnd_1295715 : Nat := 221774862080167747601207

theorem tailTrace_1295715 : CollatzResearch.WordTrace tailWord_1295715 prefixEnd_1295715 221774862080167747601207 := by
  unfold tailWord_1295715
  simp only [CollatzResearch.WordTrace]
  refine ⟨47258608500853320349272599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31505739000568880232848399 47258608500853320349272599)
  ·
    refine ⟨70887912751279980523908899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47258608500853320349272599 70887912751279980523908899)
    ·
      refine ⟨106331869126919970785863349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70887912751279980523908899 106331869126919970785863349)
      ·
        refine ⟨9968612730648747261174689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106331869126919970785863349 9968612730648747261174689)
        ·
          refine ⟨7476459547986560445881017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9968612730648747261174689 7476459547986560445881017)
          ·
            refine ⟨5607344660989920334410763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7476459547986560445881017 5607344660989920334410763)
            ·
              refine ⟨8411016991484880501616145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5607344660989920334410763 8411016991484880501616145)
              ·
                refine ⟨6308262743613660376212109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8411016991484880501616145 6308262743613660376212109)
                ·
                  refine ⟨2365598528855122641079541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6308262743613660376212109 2365598528855122641079541)
                  ·
                    refine ⟨221774862080167747601207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2365598528855122641079541 221774862080167747601207)
                    ·
                      rfl

theorem cell23_1295715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 5].length) (baseStart_1295715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295715 prefixEnd_1295715 := by exact prefixLift 1295715
  have htrace : WordTrace (prefixWord ++ tailWord_1295715) baseStart_1295715 baseEnd_1295715 := by
    simpa [prefixWord, tailWord_1295715, baseEnd_1295715] using wordTrace_append hprefix tailTrace_1295715
  have hstable : (prefixWord ++ tailWord_1295715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295715).length < 2 ^ (prefixWord ++ tailWord_1295715).sum := by decide
  have hdescent : baseEnd_1295715 < baseStart_1295715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295735 : List Nat := [1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 4]
def baseStart_1295735 : Nat := 118140960795 + 1295735 * 2 ^ 59
def prefixEnd_1295735 : Nat := 4983230072969 + 3 ^ 40 * 1295735 * 2
def baseEnd_1295735 : Nat := 665334855853593164553529

theorem tailTrace_1295735 : CollatzResearch.WordTrace tailWord_1295735 prefixEnd_1295735 665334855853593164553529 := by
  unfold tailWord_1295735
  simp only [CollatzResearch.WordTrace]
  refine ⟨47259337960780863765000659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31506225307187242510000439 47259337960780863765000659)
  ·
    refine ⟨70889006941171295647500989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47259337960780863765000659 70889006941171295647500989)
    ·
      refine ⟨26583377602939235867812871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70889006941171295647500989 26583377602939235867812871)
      ·
        refine ⟨39875066404408853801719307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26583377602939235867812871 39875066404408853801719307)
        ·
          refine ⟨59812599606613280702578961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39875066404408853801719307 59812599606613280702578961)
          ·
            refine ⟨44859449704959960526934221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59812599606613280702578961 44859449704959960526934221)
            ·
              refine ⟨16822293639359985197600333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44859449704959960526934221 16822293639359985197600333)
              ·
                refine ⟨6308360114759994449100125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16822293639359985197600333 6308360114759994449100125)
                ·
                  refine ⟨2365635043034997918412547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6308360114759994449100125 2365635043034997918412547)
                  ·
                    refine ⟨3548452564552496877618821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2365635043034997918412547 3548452564552496877618821)
                    ·
                      refine ⟨665334855853593164553529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3548452564552496877618821 665334855853593164553529)
                      ·
                        rfl

theorem cell23_1295735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_1295735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295735 prefixEnd_1295735 := by exact prefixLift 1295735
  have htrace : WordTrace (prefixWord ++ tailWord_1295735) baseStart_1295735 baseEnd_1295735 := by
    simpa [prefixWord, tailWord_1295735, baseEnd_1295735] using wordTrace_append hprefix tailTrace_1295735
  have hstable : (prefixWord ++ tailWord_1295735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295735).length < 2 ^ (prefixWord ++ tailWord_1295735).sum := by decide
  have hdescent : baseEnd_1295735 < baseStart_1295735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295755 : List Nat := [1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 5]
def baseStart_1295755 : Nat := 118140960795 + 1295755 * 2 ^ 59
def prefixEnd_1295755 : Nat := 4983230072969 + 3 ^ 40 * 1295755 * 2
def baseEnd_1295755 : Nat := 665345125466683086303437

theorem tailTrace_1295755 : CollatzResearch.WordTrace tailWord_1295755 prefixEnd_1295755 665345125466683086303437 := by
  unfold tailWord_1295755
  simp only [CollatzResearch.WordTrace]
  refine ⟨47260067420708407180728719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31506711613805604787152479 47260067420708407180728719)
  ·
    refine ⟨70890101131062610771093079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47260067420708407180728719 70890101131062610771093079)
    ·
      refine ⟨106335151696593916156639619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70890101131062610771093079 106335151696593916156639619)
      ·
        refine ⟨159502727544890874234959429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106335151696593916156639619 159502727544890874234959429)
        ·
          refine ⟨29906761414667038919054893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159502727544890874234959429 29906761414667038919054893)
          ·
            refine ⟨11215035530500139594645585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29906761414667038919054893 11215035530500139594645585)
            ·
              refine ⟨8411276647875104695984189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11215035530500139594645585 8411276647875104695984189)
              ·
                refine ⟨3154228742953164260994071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8411276647875104695984189 3154228742953164260994071)
                ·
                  refine ⟨4731343114429746391491107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3154228742953164260994071 4731343114429746391491107)
                  ·
                    refine ⟨7097014671644619587236661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4731343114429746391491107 7097014671644619587236661)
                    ·
                      refine ⟨665345125466683086303437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7097014671644619587236661 665345125466683086303437)
                      ·
                        rfl

theorem cell23_1295755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 5].length) (baseStart_1295755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295755 prefixEnd_1295755 := by exact prefixLift 1295755
  have htrace : WordTrace (prefixWord ++ tailWord_1295755) baseStart_1295755 baseEnd_1295755 := by
    simpa [prefixWord, tailWord_1295755, baseEnd_1295755] using wordTrace_append hprefix tailTrace_1295755
  have hstable : (prefixWord ++ tailWord_1295755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295755).length < 2 ^ (prefixWord ++ tailWord_1295755).sum := by decide
  have hdescent : baseEnd_1295755 < baseStart_1295755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295765 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 3, 2, 4]
def baseStart_1295765 : Nat := 118140960795 + 1295765 * 2 ^ 59
def prefixEnd_1295765 : Nat := 4983230072969 + 3 ^ 40 * 1295765 * 2
def baseEnd_1295765 : Nat := 665350260273228047178391

theorem tailTrace_1295765 : CollatzResearch.WordTrace tailWord_1295765 prefixEnd_1295765 665350260273228047178391 := by
  unfold tailWord_1295765
  simp only [CollatzResearch.WordTrace]
  refine ⟨47260432150672178888592749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31506954767114785925728499 47260432150672178888592749)
  ·
    refine ⟨17722662056502067083222281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47260432150672178888592749 17722662056502067083222281)
    ·
      refine ⟨13291996542376550312416711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17722662056502067083222281 13291996542376550312416711)
      ·
        refine ⟨19937994813564825468625067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13291996542376550312416711 19937994813564825468625067)
        ·
          refine ⟨29906992220347238202937601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19937994813564825468625067 29906992220347238202937601)
          ·
            refine ⟨22430244165260428652203201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29906992220347238202937601 22430244165260428652203201)
            ·
              refine ⟨16822683123945321489152401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22430244165260428652203201 16822683123945321489152401)
              ·
                refine ⟨12617012342958991116864301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16822683123945321489152401 12617012342958991116864301)
                ·
                  refine ⟨4731379628609621668824113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12617012342958991116864301 4731379628609621668824113)
                  ·
                    refine ⟨3548534721457216251618085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4731379628609621668824113 3548534721457216251618085)
                    ·
                      refine ⟨665350260273228047178391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3548534721457216251618085 665350260273228047178391)
                      ·
                        rfl

theorem cell23_1295765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_1295765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295765 prefixEnd_1295765 := by exact prefixLift 1295765
  have htrace : WordTrace (prefixWord ++ tailWord_1295765) baseStart_1295765 baseEnd_1295765 := by
    simpa [prefixWord, tailWord_1295765, baseEnd_1295765] using wordTrace_append hprefix tailTrace_1295765
  have hstable : (prefixWord ++ tailWord_1295765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295765).length < 2 ^ (prefixWord ++ tailWord_1295765).sum := by decide
  have hdescent : baseEnd_1295765 < baseStart_1295765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295769 : List Nat := [1, 2, 1, 2, 1, 5, 1, 3, 3, 2, 2]
def baseStart_1295769 : Nat := 118140960795 + 1295769 * 2 ^ 59
def prefixEnd_1295769 : Nat := 4983230072969 + 3 ^ 40 * 1295769 * 2
def baseEnd_1295769 : Nat := 665352314195846031528373

theorem tailTrace_1295769 : CollatzResearch.WordTrace tailWord_1295769 prefixEnd_1295769 665352314195846031528373 := by
  unfold tailWord_1295769
  simp only [CollatzResearch.WordTrace]
  refine ⟨47260578042657687571738361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31507052028438458381158907 47260578042657687571738361)
  ·
    refine ⟨35445433531993265678803771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47260578042657687571738361 35445433531993265678803771)
    ·
      refine ⟨53168150297989898518205657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35445433531993265678803771 53168150297989898518205657)
      ·
        refine ⟨39876112723492423888654243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53168150297989898518205657 39876112723492423888654243)
        ·
          refine ⟨59814169085238635832981365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39876112723492423888654243 59814169085238635832981365)
          ·
            refine ⟨5607578351741122109342003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59814169085238635832981365 5607578351741122109342003)
            ·
              refine ⟨8411367527611683164013005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5607578351741122109342003 8411367527611683164013005)
              ·
                refine ⟨3154262822854381186504877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8411367527611683164013005 3154262822854381186504877)
                ·
                  refine ⟨1182848558570392944939329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3154262822854381186504877 1182848558570392944939329)
                  ·
                    refine ⟨887136418927794708704497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1182848558570392944939329 887136418927794708704497)
                    ·
                      refine ⟨665352314195846031528373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 887136418927794708704497 665352314195846031528373)
                      ·
                        rfl

theorem cell23_1295769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 2, 2].length) (baseStart_1295769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295769 prefixEnd_1295769 := by exact prefixLift 1295769
  have htrace : WordTrace (prefixWord ++ tailWord_1295769) baseStart_1295769 baseEnd_1295769 := by
    simpa [prefixWord, tailWord_1295769, baseEnd_1295769] using wordTrace_append hprefix tailTrace_1295769
  have hstable : (prefixWord ++ tailWord_1295769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295769).length < 2 ^ (prefixWord ++ tailWord_1295769).sum := by decide
  have hdescent : baseEnd_1295769 < baseStart_1295769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295779 : List Nat := [1, 1, 1, 4, 1, 3, 5, 1, 2, 4]
def baseStart_1295779 : Nat := 118140960795 + 1295779 * 2 ^ 59
def prefixEnd_1295779 : Nat := 4983230072969 + 3 ^ 40 * 1295779 * 2
def baseEnd_1295779 : Nat := 221785816334130330801109

theorem tailTrace_1295779 : CollatzResearch.WordTrace tailWord_1295779 prefixEnd_1295779 221785816334130330801109 := by
  unfold tailWord_1295779
  simp only [CollatzResearch.WordTrace]
  refine ⟨47260942772621459279602391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31507295181747639519734927 47260942772621459279602391)
  ·
    refine ⟨70891414158932188919403587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47260942772621459279602391 70891414158932188919403587)
    ·
      refine ⟨106337121238398283379105381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70891414158932188919403587 106337121238398283379105381)
      ·
        refine ⟨19938210232199678133582259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106337121238398283379105381 19938210232199678133582259)
        ·
          refine ⟨29907315348299517200373389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19938210232199678133582259 29907315348299517200373389)
          ·
            refine ⟨11215243255612318950140021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29907315348299517200373389 11215243255612318950140021)
            ·
              refine ⟨1051429055213654901575627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11215243255612318950140021 1051429055213654901575627)
              ·
                refine ⟨1577143582820482352363441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1051429055213654901575627 1577143582820482352363441)
                ·
                  refine ⟨1182857687115361764272581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1577143582820482352363441 1182857687115361764272581)
                  ·
                    refine ⟨221785816334130330801109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1182857687115361764272581 221785816334130330801109)
                    ·
                      rfl

theorem cell23_1295779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 2, 4].length) (baseStart_1295779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295779 prefixEnd_1295779 := by exact prefixLift 1295779
  have htrace : WordTrace (prefixWord ++ tailWord_1295779) baseStart_1295779 baseEnd_1295779 := by
    simpa [prefixWord, tailWord_1295779, baseEnd_1295779] using wordTrace_append hprefix tailTrace_1295779
  have hstable : (prefixWord ++ tailWord_1295779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295779).length < 2 ^ (prefixWord ++ tailWord_1295779).sum := by decide
  have hdescent : baseEnd_1295779 < baseStart_1295779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295815 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 5]
def baseStart_1295815 : Nat := 118140960795 + 1295815 * 2 ^ 59
def prefixEnd_1295815 : Nat := 4983230072969 + 3 ^ 40 * 1295815 * 2
def baseEnd_1295815 : Nat := 665375934305952851553161

theorem tailTrace_1295815 : CollatzResearch.WordTrace tailWord_1295815 prefixEnd_1295815 665375934305952851553161 := by
  unfold tailWord_1295815
  simp only [CollatzResearch.WordTrace]
  refine ⟨47262255800491037427912899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31508170533660691618608599 47262255800491037427912899)
  ·
    refine ⟨70893383700736556141869349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47262255800491037427912899 70893383700736556141869349)
    ·
      refine ⟨13292509443888104276600503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70893383700736556141869349 13292509443888104276600503)
      ·
        refine ⟨19938764165832156414900755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13292509443888104276600503 19938764165832156414900755)
        ·
          refine ⟨29908146248748234622351133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19938764165832156414900755 29908146248748234622351133)
          ·
            refine ⟨11215554843280587983381675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29908146248748234622351133 11215554843280587983381675)
            ·
              refine ⟨16823332264920881975072513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11215554843280587983381675 16823332264920881975072513)
              ·
                refine ⟨12617499198690661481304385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16823332264920881975072513 12617499198690661481304385)
                ·
                  refine ⟨9463124399017996110978289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12617499198690661481304385 9463124399017996110978289)
                  ·
                    refine ⟨7097343299263497083233717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9463124399017996110978289 7097343299263497083233717)
                    ·
                      refine ⟨665375934305952851553161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7097343299263497083233717 665375934305952851553161)
                      ·
                        rfl

theorem cell23_1295815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_1295815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295815 prefixEnd_1295815 := by exact prefixLift 1295815
  have htrace : WordTrace (prefixWord ++ tailWord_1295815) baseStart_1295815 baseEnd_1295815 := by
    simpa [prefixWord, tailWord_1295815, baseEnd_1295815] using wordTrace_append hprefix tailTrace_1295815
  have hstable : (prefixWord ++ tailWord_1295815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295815).length < 2 ^ (prefixWord ++ tailWord_1295815).sum := by decide
  have hdescent : baseEnd_1295815 < baseStart_1295815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295820 : List Nat := [2, 2, 1, 4, 2, 2, 3, 2, 1, 2, 2]
def baseStart_1295820 : Nat := 118140960795 + 1295820 * 2 ^ 59
def prefixEnd_1295820 : Nat := 4983230072969 + 3 ^ 40 * 1295820 * 2
def baseEnd_1295820 : Nat := 665378501709225331990639

theorem tailTrace_1295820 : CollatzResearch.WordTrace tailWord_1295820 prefixEnd_1295820 665378501709225331990639 := by
  unfold tailWord_1295820
  simp only [CollatzResearch.WordTrace]
  refine ⟨23631219082736461640922457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31508292110315282187896609 23631219082736461640922457)
  ·
    refine ⟨17723414312052346230691843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23631219082736461640922457 17723414312052346230691843)
    ·
      refine ⟨26585121468078519346037765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17723414312052346230691843 26585121468078519346037765)
      ·
        refine ⟨4984710275264722377382081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26585121468078519346037765 4984710275264722377382081)
        ·
          refine ⟨3738532706448541783036561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4984710275264722377382081 3738532706448541783036561)
          ·
            refine ⟨2803899529836406337277421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3738532706448541783036561 2803899529836406337277421)
            ·
              refine ⟨1051462323688652376479033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2803899529836406337277421 1051462323688652376479033)
              ·
                refine ⟨788596742766489282359275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1051462323688652376479033 788596742766489282359275)
                ·
                  refine ⟨1182895114149733923538913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 788596742766489282359275 1182895114149733923538913)
                  ·
                    refine ⟨887171335612300442654185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1182895114149733923538913 887171335612300442654185)
                    ·
                      refine ⟨665378501709225331990639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 887171335612300442654185 665378501709225331990639)
                      ·
                        rfl

theorem cell23_1295820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_1295820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295820 prefixEnd_1295820 := by exact prefixLift 1295820
  have htrace : WordTrace (prefixWord ++ tailWord_1295820) baseStart_1295820 baseEnd_1295820 := by
    simpa [prefixWord, tailWord_1295820, baseEnd_1295820] using wordTrace_append hprefix tailTrace_1295820
  have hstable : (prefixWord ++ tailWord_1295820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295820).length < 2 ^ (prefixWord ++ tailWord_1295820).sum := by decide
  have hdescent : baseEnd_1295820 < baseStart_1295820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295829 : List Nat := [1, 3, 2, 3, 1, 1, 2, 2, 3, 3, 2]
def baseStart_1295829 : Nat := 118140960795 + 1295829 * 2 ^ 59
def prefixEnd_1295829 : Nat := 4983230072969 + 3 ^ 40 * 1295829 * 2
def baseEnd_1295829 : Nat := 665383123035115796778097

theorem tailTrace_1295829 : CollatzResearch.WordTrace tailWord_1295829 prefixEnd_1295829 665383123035115796778097 := by
  unfold tailWord_1295829
  simp only [CollatzResearch.WordTrace]
  refine ⟨47262766422440317818922541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31508510948293545212615027 47262766422440317818922541)
  ·
    refine ⟨17723537408415119182095953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47262766422440317818922541 17723537408415119182095953)
    ·
      refine ⟨13292653056311339386571965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17723537408415119182095953 13292653056311339386571965)
      ·
        refine ⟨4984744896116752269964487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13292653056311339386571965 4984744896116752269964487)
        ·
          refine ⟨7477117344175128404946731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4984744896116752269964487 7477117344175128404946731)
          ·
            refine ⟨11215676016262692607420097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7477117344175128404946731 11215676016262692607420097)
            ·
              refine ⟨8411757012197019455565073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11215676016262692607420097 8411757012197019455565073)
              ·
                refine ⟨6308817759147764591673805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8411757012197019455565073 6308817759147764591673805)
                ·
                  refine ⟨2365806659680411721877677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6308817759147764591673805 2365806659680411721877677)
                  ·
                    refine ⟨887177497380154395704129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2365806659680411721877677 887177497380154395704129)
                    ·
                      refine ⟨665383123035115796778097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 887177497380154395704129 665383123035115796778097)
                      ·
                        rfl

theorem cell23_1295829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_1295829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295829 prefixEnd_1295829 := by exact prefixLift 1295829
  have htrace : WordTrace (prefixWord ++ tailWord_1295829) baseStart_1295829 baseEnd_1295829 := by
    simpa [prefixWord, tailWord_1295829, baseEnd_1295829] using wordTrace_append hprefix tailTrace_1295829
  have hstable : (prefixWord ++ tailWord_1295829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295829).length < 2 ^ (prefixWord ++ tailWord_1295829).sum := by decide
  have hdescent : baseEnd_1295829 < baseStart_1295829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295859 : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 4, 2, 2]
def baseStart_1295859 : Nat := 118140960795 + 1295859 * 2 ^ 59
def prefixEnd_1295859 : Nat := 4983230072969 + 3 ^ 40 * 1295859 * 2
def baseEnd_1295859 : Nat := 665398527454750679402959

theorem tailTrace_1295859 : CollatzResearch.WordTrace tailWord_1295859 prefixEnd_1295859 665398527454750679402959 := by
  unfold tailWord_1295859
  simp only [CollatzResearch.WordTrace]
  refine ⟨47263860612331632942514631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31509240408221088628343087 47263860612331632942514631)
  ·
    refine ⟨70895790918497449413771947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47263860612331632942514631 70895790918497449413771947)
    ·
      refine ⟨106343686377746174120657921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70895790918497449413771947 106343686377746174120657921)
      ·
        refine ⟨79757764783309630590493441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106343686377746174120657921 79757764783309630590493441)
        ·
          refine ⟨59818323587482222942870081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79757764783309630590493441 59818323587482222942870081)
          ·
            refine ⟨44863742690611667207152561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59818323587482222942870081 44863742690611667207152561)
            ·
              refine ⟨33647807017958750405364421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44863742690611667207152561 33647807017958750405364421)
              ·
                refine ⟨6308963815867265701005829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33647807017958750405364421 6308963815867265701005829)
                ·
                  refine ⟨1182930715475112318938593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6308963815867265701005829 1182930715475112318938593)
                  ·
                    refine ⟨887198036606334239203945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1182930715475112318938593 887198036606334239203945)
                    ·
                      refine ⟨665398527454750679402959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 887198036606334239203945 665398527454750679402959)
                      ·
                        rfl

theorem cell23_1295859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 2, 2].length) (baseStart_1295859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295859 prefixEnd_1295859 := by exact prefixLift 1295859
  have htrace : WordTrace (prefixWord ++ tailWord_1295859) baseStart_1295859 baseEnd_1295859 := by
    simpa [prefixWord, tailWord_1295859, baseEnd_1295859] using wordTrace_append hprefix tailTrace_1295859
  have hstable : (prefixWord ++ tailWord_1295859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295859).length < 2 ^ (prefixWord ++ tailWord_1295859).sum := by decide
  have hdescent : baseEnd_1295859 < baseStart_1295859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295870 : List Nat := [4, 2, 2, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_1295870 : Nat := 118140960795 + 1295870 * 2 ^ 59
def prefixEnd_1295870 : Nat := 4983230072969 + 3 ^ 40 * 1295870 * 2
def baseEnd_1295870 : Nat := 665404175741950136365409

theorem tailTrace_1295870 : CollatzResearch.WordTrace tailWord_1295870 prefixEnd_1295870 665404175741950136365409 := by
  unfold tailWord_1295870
  simp only [CollatzResearch.WordTrace]
  refine ⟨5908032726911472727645633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31509507876861187880776709 5908032726911472727645633)
  ·
    refine ⟨4431024545183604545734225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5908032726911472727645633 4431024545183604545734225)
    ·
      refine ⟨3323268408887703409300669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4431024545183604545734225 3323268408887703409300669)
      ·
        refine ⟨1246225653332888778487751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3323268408887703409300669 1246225653332888778487751)
        ·
          refine ⟨1869338479999333167731627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1246225653332888778487751 1869338479999333167731627)
          ·
            refine ⟨2804007719998999751597441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869338479999333167731627 2804007719998999751597441)
            ·
              refine ⟨2103005789999249813698081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2804007719998999751597441 2103005789999249813698081)
              ·
                refine ⟨1577254342499437360273561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2103005789999249813698081 1577254342499437360273561)
                ·
                  refine ⟨1182940756874578020205171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1577254342499437360273561 1182940756874578020205171)
                  ·
                    refine ⟨1774411135311867030307757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1182940756874578020205171 1774411135311867030307757)
                    ·
                      refine ⟨665404175741950136365409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1774411135311867030307757 665404175741950136365409)
                      ·
                        rfl

theorem cell23_1295870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_1295870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295870 prefixEnd_1295870 := by exact prefixLift 1295870
  have htrace : WordTrace (prefixWord ++ tailWord_1295870) baseStart_1295870 baseEnd_1295870 := by
    simpa [prefixWord, tailWord_1295870, baseEnd_1295870] using wordTrace_append hprefix tailTrace_1295870
  have hstable : (prefixWord ++ tailWord_1295870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295870).length < 2 ^ (prefixWord ++ tailWord_1295870).sum := by decide
  have hdescent : baseEnd_1295870 < baseStart_1295870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295952 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 3]
def baseStart_1295952 : Nat := 118140960795 + 1295952 * 2 ^ 59
def prefixEnd_1295952 : Nat := 4983230072969 + 3 ^ 40 * 1295952 * 2
def baseEnd_1295952 : Nat := 665446281155618815540031

theorem tailTrace_1295952 : CollatzResearch.WordTrace tailWord_1295952 prefixEnd_1295952 665446281155618815540031 := by
  unfold tailWord_1295952
  simp only [CollatzResearch.WordTrace]
  refine ⟨23633626300497354912825055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31511501733996473217100073 23633626300497354912825055)
  ·
    refine ⟨35450439450746032369237583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23633626300497354912825055 35450439450746032369237583)
    ·
      refine ⟨53175659176119048553856375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35450439450746032369237583 53175659176119048553856375)
      ·
        refine ⟨79763488764178572830784563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53175659176119048553856375 79763488764178572830784563)
        ·
          refine ⟨119645233146267859246176845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79763488764178572830784563 119645233146267859246176845)
          ·
            refine ⟨44866962429850447217316317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119645233146267859246176845 44866962429850447217316317)
            ·
              refine ⟨16825110911193917706493619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44866962429850447217316317 16825110911193917706493619)
              ·
                refine ⟨25237666366790876559740429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16825110911193917706493619 25237666366790876559740429)
                ·
                  refine ⟨9464124887546578709902661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25237666366790876559740429 9464124887546578709902661)
                  ·
                    refine ⟨1774523416414983508106749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9464124887546578709902661 1774523416414983508106749)
                    ·
                      refine ⟨665446281155618815540031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1774523416414983508106749 665446281155618815540031)
                      ·
                        rfl

theorem cell23_1295952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 3].length) (baseStart_1295952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295952 prefixEnd_1295952 := by exact prefixLift 1295952
  have htrace : WordTrace (prefixWord ++ tailWord_1295952) baseStart_1295952 baseEnd_1295952 := by
    simpa [prefixWord, tailWord_1295952, baseEnd_1295952] using wordTrace_append hprefix tailTrace_1295952
  have hstable : (prefixWord ++ tailWord_1295952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295952).length < 2 ^ (prefixWord ++ tailWord_1295952).sum := by decide
  have hdescent : baseEnd_1295952 < baseStart_1295952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295959 : List Nat := [1, 1, 3, 2, 2, 3, 2, 2, 3, 4]
def baseStart_1295959 : Nat := 118140960795 + 1295959 * 2 ^ 59
def prefixEnd_1295959 : Nat := 4983230072969 + 3 ^ 40 * 1295959 * 2
def baseEnd_1295959 : Nat := 221816625173400096050833

theorem tailTrace_1295959 : CollatzResearch.WordTrace tailWord_1295959 prefixEnd_1295959 221816625173400096050833 := by
  unfold tailWord_1295959
  simp only [CollatzResearch.WordTrace]
  refine ⟨47267507911969350021154931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31511671941312900014103287 47267507911969350021154931)
  ·
    refine ⟨70901261867954025031732397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47267507911969350021154931 70901261867954025031732397)
    ·
      refine ⟨26587973200482759386899649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70901261867954025031732397 26587973200482759386899649)
      ·
        refine ⟨19940979900362069540174737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26587973200482759386899649 19940979900362069540174737)
        ·
          refine ⟨14955734925271552155131053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19940979900362069540174737 14955734925271552155131053)
          ·
            refine ⟨5608400596976832058174145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14955734925271552155131053 5608400596976832058174145)
            ·
              refine ⟨4206300447732624043630609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5608400596976832058174145 4206300447732624043630609)
              ·
                refine ⟨3154725335799468032722957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4206300447732624043630609 3154725335799468032722957)
                ·
                  refine ⟨1183022000924800512271109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3154725335799468032722957 1183022000924800512271109)
                  ·
                    refine ⟨221816625173400096050833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1183022000924800512271109 221816625173400096050833)
                    ·
                      rfl

theorem cell23_1295959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 4].length) (baseStart_1295959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295959 prefixEnd_1295959 := by exact prefixLift 1295959
  have htrace : WordTrace (prefixWord ++ tailWord_1295959) baseStart_1295959 baseEnd_1295959 := by
    simpa [prefixWord, tailWord_1295959, baseEnd_1295959] using wordTrace_append hprefix tailTrace_1295959
  have hstable : (prefixWord ++ tailWord_1295959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295959).length < 2 ^ (prefixWord ++ tailWord_1295959).sum := by decide
  have hdescent : baseEnd_1295959 < baseStart_1295959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295969 : List Nat := [1, 2, 3, 1, 1, 3, 2, 3, 2, 2, 3]
def baseStart_1295969 : Nat := 118140960795 + 1295969 * 2 ^ 59
def prefixEnd_1295969 : Nat := 4983230072969 + 3 ^ 40 * 1295969 * 2
def baseEnd_1295969 : Nat := 665455010326745249027453

theorem tailTrace_1295969 : CollatzResearch.WordTrace tailWord_1295969 prefixEnd_1295969 665455010326745249027453 := by
  unfold tailWord_1295969
  simp only [CollatzResearch.WordTrace]
  refine ⟨47267872641933121729018961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31511915094622081152679307 47267872641933121729018961)
  ·
    refine ⟨35450904481449841296764221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47267872641933121729018961 35450904481449841296764221)
    ·
      refine ⟨13294089180543690486286583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35450904481449841296764221 13294089180543690486286583)
      ·
        refine ⟨19941133770815535729429875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13294089180543690486286583 19941133770815535729429875)
        ·
          refine ⟨29911700656223303594144813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19941133770815535729429875 29911700656223303594144813)
          ·
            refine ⟨11216887746083738847804305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29911700656223303594144813 11216887746083738847804305)
            ·
              refine ⟨8412665809562804135853229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11216887746083738847804305 8412665809562804135853229)
              ·
                refine ⟨3154749678586051550944961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8412665809562804135853229 3154749678586051550944961)
                ·
                  refine ⟨2366062258939538663208721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3154749678586051550944961 2366062258939538663208721)
                  ·
                    refine ⟨1774546694204653997406541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2366062258939538663208721 1774546694204653997406541)
                    ·
                      refine ⟨665455010326745249027453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1774546694204653997406541 665455010326745249027453)
                      ·
                        rfl

theorem cell23_1295969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_1295969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295969 prefixEnd_1295969 := by exact prefixLift 1295969
  have htrace : WordTrace (prefixWord ++ tailWord_1295969) baseStart_1295969 baseEnd_1295969 := by
    simpa [prefixWord, tailWord_1295969, baseEnd_1295969] using wordTrace_append hprefix tailTrace_1295969
  have hstable : (prefixWord ++ tailWord_1295969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295969).length < 2 ^ (prefixWord ++ tailWord_1295969).sum := by decide
  have hdescent : baseEnd_1295969 < baseStart_1295969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295972 : List Nat := [2, 3, 1, 1, 2, 3, 1, 2, 8]
def baseStart_1295972 : Nat := 118140960795 + 1295972 * 2 ^ 59
def prefixEnd_1295972 : Nat := 4983230072969 + 3 ^ 40 * 1295972 * 2
def baseEnd_1295972 : Nat := 73939616752078748587771

theorem tailTrace_1295972 : CollatzResearch.WordTrace tailWord_1295972 prefixEnd_1295972 73939616752078748587771 := by
  unfold tailWord_1295972
  simp only [CollatzResearch.WordTrace]
  refine ⟨23633991030461126620689085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31511988040614835494252113 23633991030461126620689085)
  ·
    refine ⟨8862746636422922482758407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23633991030461126620689085 8862746636422922482758407)
    ·
      refine ⟨13294119954634383724137611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8862746636422922482758407 13294119954634383724137611)
      ·
        refine ⟨19941179931951575586206417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13294119954634383724137611 19941179931951575586206417)
        ·
          refine ⟨14955884948963681689654813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19941179931951575586206417 14955884948963681689654813)
          ·
            refine ⟨5608456855861380633620555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14955884948963681689654813 5608456855861380633620555)
            ·
              refine ⟨8412685283792070950430833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5608456855861380633620555 8412685283792070950430833)
              ·
                refine ⟨6309513962844053212823125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8412685283792070950430833 6309513962844053212823125)
                ·
                  refine ⟨73939616752078748587771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6309513962844053212823125 73939616752078748587771)
                  ·
                    rfl

theorem cell23_1295972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_1295972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295972 prefixEnd_1295972 := by exact prefixLift 1295972
  have htrace : WordTrace (prefixWord ++ tailWord_1295972) baseStart_1295972 baseEnd_1295972 := by
    simpa [prefixWord, tailWord_1295972, baseEnd_1295972] using wordTrace_append hprefix tailTrace_1295972
  have hstable : (prefixWord ++ tailWord_1295972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295972).length < 2 ^ (prefixWord ++ tailWord_1295972).sum := by decide
  have hdescent : baseEnd_1295972 < baseStart_1295972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295986 : List Nat := [3, 2, 1, 2, 3, 2, 1, 2, 2, 2, 3]
def baseStart_1295986 : Nat := 118140960795 + 1295986 * 2 ^ 59
def prefixEnd_1295986 : Nat := 4983230072969 + 3 ^ 40 * 1295986 * 2
def baseEnd_1295986 : Nat := 665463739497871682514875

theorem tailTrace_1295986 : CollatzResearch.WordTrace tailWord_1295986 prefixEnd_1295986 665463739497871682514875 := by
  unfold tailWord_1295986
  simp only [CollatzResearch.WordTrace]
  refine ⟨11817123170717883408096953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31512328455247689088258541 11817123170717883408096953)
  ·
    refine ⟨8862842378038412556072715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11817123170717883408096953 8862842378038412556072715)
    ·
      refine ⟨13294263567057618834109073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8862842378038412556072715 13294263567057618834109073)
      ·
        refine ⟨9970697675293214125581805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13294263567057618834109073 9970697675293214125581805)
        ·
          refine ⟨3739011628234955297093177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9970697675293214125581805 3739011628234955297093177)
          ·
            refine ⟨2804258721176216472819883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3739011628234955297093177 2804258721176216472819883)
            ·
              refine ⟨4206388081764324709229825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2804258721176216472819883 4206388081764324709229825)
              ·
                refine ⟨3154791061323243531922369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4206388081764324709229825 3154791061323243531922369)
                ·
                  refine ⟨2366093295992432648941777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3154791061323243531922369 2366093295992432648941777)
                  ·
                    refine ⟨1774569971994324486706333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2366093295992432648941777 1774569971994324486706333)
                    ·
                      refine ⟨665463739497871682514875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1774569971994324486706333 665463739497871682514875)
                      ·
                        rfl

theorem cell23_1295986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_1295986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295986 prefixEnd_1295986 := by exact prefixLift 1295986
  have htrace : WordTrace (prefixWord ++ tailWord_1295986) baseStart_1295986 baseEnd_1295986 := by
    simpa [prefixWord, tailWord_1295986, baseEnd_1295986] using wordTrace_append hprefix tailTrace_1295986
  have hstable : (prefixWord ++ tailWord_1295986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295986).length < 2 ^ (prefixWord ++ tailWord_1295986).sum := by decide
  have hdescent : baseEnd_1295986 < baseStart_1295986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295989 : List Nat := [1, 3, 4, 2, 1, 1, 2, 1, 8]
def baseStart_1295989 : Nat := 118140960795 + 1295989 * 2 ^ 59
def prefixEnd_1295989 : Nat := 4983230072969 + 3 ^ 40 * 1295989 * 2
def baseEnd_1295989 : Nat := 73940586659981685641929

theorem tailTrace_1295989 : CollatzResearch.WordTrace tailWord_1295989 prefixEnd_1295989 73940586659981685641929 := by
  unfold tailWord_1295989
  simp only [CollatzResearch.WordTrace]
  refine ⟨47268602101860665144747021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31512401401240443429831347 47268602101860665144747021)
  ·
    refine ⟨17725725788197749429280133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47268602101860665144747021 17725725788197749429280133)
    ·
      refine ⟨3323573585287078017990025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17725725788197749429280133 3323573585287078017990025)
      ·
        refine ⟨2492680188965308513492519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3323573585287078017990025 2492680188965308513492519)
        ·
          refine ⟨3739020283447962770238779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2492680188965308513492519 3739020283447962770238779)
          ·
            refine ⟨5608530425171944155358169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3739020283447962770238779 5608530425171944155358169)
            ·
              refine ⟨4206397818878958116518627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5608530425171944155358169 4206397818878958116518627)
              ·
                refine ⟨6309596728318437174777941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4206397818878958116518627 6309596728318437174777941)
                ·
                  refine ⟨73940586659981685641929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6309596728318437174777941 73940586659981685641929)
                  ·
                    rfl

theorem cell23_1295989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 8].length) (baseStart_1295989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295989 prefixEnd_1295989 := by exact prefixLift 1295989
  have htrace : WordTrace (prefixWord ++ tailWord_1295989) baseStart_1295989 baseEnd_1295989 := by
    simpa [prefixWord, tailWord_1295989, baseEnd_1295989] using wordTrace_append hprefix tailTrace_1295989
  have hstable : (prefixWord ++ tailWord_1295989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295989).length < 2 ^ (prefixWord ++ tailWord_1295989).sum := by decide
  have hdescent : baseEnd_1295989 < baseStart_1295989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295993 : List Nat := [1, 2, 1, 3, 3, 1, 5, 2, 1, 4]
def baseStart_1295993 : Nat := 118140960795 + 1295993 * 2 ^ 59
def prefixEnd_1295993 : Nat := 4983230072969 + 3 ^ 40 * 1295993 * 2
def baseEnd_1295993 : Nat := 221822444620817718375781

theorem tailTrace_1295993 : CollatzResearch.WordTrace tailWord_1295993 prefixEnd_1295993 221822444620817718375781 := by
  unfold tailWord_1295993
  simp only [CollatzResearch.WordTrace]
  refine ⟨47268747993846173827892633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31512498662564115885261755 47268747993846173827892633)
  ·
    refine ⟨35451560995384630370919475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47268747993846173827892633 35451560995384630370919475)
    ·
      refine ⟨53177341493076945556379213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35451560995384630370919475 53177341493076945556379213)
      ·
        refine ⟨19941503059903854583642205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53177341493076945556379213 19941503059903854583642205)
        ·
          refine ⟨7478063647463945468865827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19941503059903854583642205 7478063647463945468865827)
          ·
            refine ⟨11217095471195918203298741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7478063647463945468865827 11217095471195918203298741)
            ·
              refine ⟨1051602700424617331559257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11217095471195918203298741 1051602700424617331559257)
              ·
                refine ⟨788702025318462998669443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1051602700424617331559257 788702025318462998669443)
                ·
                  refine ⟨1183053037977694498004165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 788702025318462998669443 1183053037977694498004165)
                  ·
                    refine ⟨221822444620817718375781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1183053037977694498004165 221822444620817718375781)
                    ·
                      rfl

theorem cell23_1295993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 1, 4].length) (baseStart_1295993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295993 prefixEnd_1295993 := by exact prefixLift 1295993
  have htrace : WordTrace (prefixWord ++ tailWord_1295993) baseStart_1295993 baseEnd_1295993 := by
    simpa [prefixWord, tailWord_1295993, baseEnd_1295993] using wordTrace_append hprefix tailTrace_1295993
  have hstable : (prefixWord ++ tailWord_1295993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295993).length < 2 ^ (prefixWord ++ tailWord_1295993).sum := by decide
  have hdescent : baseEnd_1295993 < baseStart_1295993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296009 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 3, 5, 2]
def baseStart_1296009 : Nat := 118140960795 + 1296009 * 2 ^ 59
def prefixEnd_1296009 : Nat := 4983230072969 + 3 ^ 40 * 1296009 * 2
def baseEnd_1296009 : Nat := 665475549552925092527269

theorem tailTrace_1296009 : CollatzResearch.WordTrace tailWord_1296009 prefixEnd_1296009 665475549552925092527269 := by
  unfold tailWord_1296009
  simp only [CollatzResearch.WordTrace]
  refine ⟨47269331561788208560475081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31512887707858805706983387 47269331561788208560475081)
  ·
    refine ⟨35451998671341156420356311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47269331561788208560475081 35451998671341156420356311)
    ·
      refine ⟨53177998007011734630534467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35451998671341156420356311 53177998007011734630534467)
      ·
        refine ⟨79766997010517601945801701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53177998007011734630534467 79766997010517601945801701)
        ·
          refine ⟨14956311939472050364837819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79766997010517601945801701 14956311939472050364837819)
          ·
            refine ⟨22434467909208075547256729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14956311939472050364837819 22434467909208075547256729)
            ·
              refine ⟨16825850931906056660442547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22434467909208075547256729 16825850931906056660442547)
              ·
                refine ⟨25238776397859084990663821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16825850931906056660442547 25238776397859084990663821)
                ·
                  refine ⟨9464541149197156871498933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25238776397859084990663821 9464541149197156871498933)
                  ·
                    refine ⟨887300732737233456703025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9464541149197156871498933 887300732737233456703025)
                    ·
                      refine ⟨665475549552925092527269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 887300732737233456703025 665475549552925092527269)
                      ·
                        rfl

theorem cell23_1296009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 5, 2].length) (baseStart_1296009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296009 prefixEnd_1296009 := by exact prefixLift 1296009
  have htrace : WordTrace (prefixWord ++ tailWord_1296009) baseStart_1296009 baseEnd_1296009 := by
    simpa [prefixWord, tailWord_1296009, baseEnd_1296009] using wordTrace_append hprefix tailTrace_1296009
  have hstable : (prefixWord ++ tailWord_1296009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296009).length < 2 ^ (prefixWord ++ tailWord_1296009).sum := by decide
  have hdescent : baseEnd_1296009 < baseStart_1296009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296040 : List Nat := [2, 1, 7, 1, 1, 1, 2, 2, 6]
def baseStart_1296040 : Nat := 118140960795 + 1296040 * 2 ^ 59
def prefixEnd_1296040 : Nat := 4983230072969 + 3 ^ 40 * 1296040 * 2
def baseEnd_1296040 : Nat := 73943496383690496804403

theorem tailTrace_1296040 : CollatzResearch.WordTrace tailWord_1296040 prefixEnd_1296040 73943496383690496804403 := by
  unfold tailWord_1296040
  simp only [CollatzResearch.WordTrace]
  refine ⟨23635231112337950427426787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31513641483117267236569049 23635231112337950427426787)
  ·
    refine ⟨35452846668506925641140181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23635231112337950427426787 35452846668506925641140181)
    ·
      refine ⟨830926093793131069714223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 35452846668506925641140181 830926093793131069714223)
      ·
        refine ⟨1246389140689696604571335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 830926093793131069714223 1246389140689696604571335)
        ·
          refine ⟨1869583711034544906857003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1246389140689696604571335 1869583711034544906857003)
          ·
            refine ⟨2804375566551817360285505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869583711034544906857003 2804375566551817360285505)
            ·
              refine ⟨2103281674913863020214129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2804375566551817360285505 2103281674913863020214129)
              ·
                refine ⟨1577461256185397265160597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2103281674913863020214129 1577461256185397265160597)
                ·
                  refine ⟨73943496383690496804403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1577461256185397265160597 73943496383690496804403)
                  ·
                    rfl

theorem cell23_1296040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 6].length) (baseStart_1296040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296040 prefixEnd_1296040 := by exact prefixLift 1296040
  have htrace : WordTrace (prefixWord ++ tailWord_1296040) baseStart_1296040 baseEnd_1296040 := by
    simpa [prefixWord, tailWord_1296040, baseEnd_1296040] using wordTrace_append hprefix tailTrace_1296040
  have hstable : (prefixWord ++ tailWord_1296040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296040).length < 2 ^ (prefixWord ++ tailWord_1296040).sum := by decide
  have hdescent : baseEnd_1296040 < baseStart_1296040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296050 : List Nat := [3, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3]
def baseStart_1296050 : Nat := 118140960795 + 1296050 * 2 ^ 59
def prefixEnd_1296050 : Nat := 4983230072969 + 3 ^ 40 * 1296050 * 2
def baseEnd_1296050 : Nat := 665496602259759432114581

theorem tailTrace_1296050 : CollatzResearch.WordTrace tailWord_1296050 prefixEnd_1296050 665496602259759432114581 := by
  unfold tailWord_1296050
  simp only [CollatzResearch.WordTrace]
  refine ⟨11817706738659918140679401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31513884636426448375145069 11817706738659918140679401)
  ·
    refine ⟨8863280053994938605509551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11817706738659918140679401 8863280053994938605509551)
    ·
      refine ⟨13294920080992407908264327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8863280053994938605509551 13294920080992407908264327)
      ·
        refine ⟨19942380121488611862396491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13294920080992407908264327 19942380121488611862396491)
        ·
          refine ⟨29913570182232917793594737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19942380121488611862396491 29913570182232917793594737)
          ·
            refine ⟨22435177636674688345196053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29913570182232917793594737 22435177636674688345196053)
            ·
              refine ⟨1051648951719126016181065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22435177636674688345196053 1051648951719126016181065)
              ·
                refine ⟨788736713789344512135799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1051648951719126016181065 788736713789344512135799)
                ·
                  refine ⟨1183105070684016768203699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 788736713789344512135799 1183105070684016768203699)
                  ·
                    refine ⟨1774657606026025152305549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1183105070684016768203699 1774657606026025152305549)
                    ·
                      refine ⟨665496602259759432114581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1774657606026025152305549 665496602259759432114581)
                      ·
                        rfl

theorem cell23_1296050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3].length) (baseStart_1296050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296050 prefixEnd_1296050 := by exact prefixLift 1296050
  have htrace : WordTrace (prefixWord ++ tailWord_1296050) baseStart_1296050 baseEnd_1296050 := by
    simpa [prefixWord, tailWord_1296050, baseEnd_1296050] using wordTrace_append hprefix tailTrace_1296050
  have hstable : (prefixWord ++ tailWord_1296050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296050).length < 2 ^ (prefixWord ++ tailWord_1296050).sum := by decide
  have hdescent : baseEnd_1296050 < baseStart_1296050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296056 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 7, 2, 2]
def baseStart_1296056 : Nat := 118140960795 + 1296056 * 2 ^ 59
def prefixEnd_1296056 : Nat := 4983230072969 + 3 ^ 40 * 1296056 * 2
def baseEnd_1296056 : Nat := 665499683143686408639553

theorem tailTrace_1296056 : CollatzResearch.WordTrace tailWord_1296056 prefixEnd_1296056 665499683143686408639553 := by
  unfold tailWord_1296056
  simp only [CollatzResearch.WordTrace]
  refine ⟨23635522896308967793718011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31514030528411957058290681 23635522896308967793718011)
  ·
    refine ⟨35453284344463451690577017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23635522896308967793718011 35453284344463451690577017)
    ·
      refine ⟨26589963258347588767932763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35453284344463451690577017 26589963258347588767932763)
      ·
        refine ⟨39884944887521383151899145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26589963258347588767932763 39884944887521383151899145)
        ·
          refine ⟨29913708665641037363924359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39884944887521383151899145 29913708665641037363924359)
          ·
            refine ⟨44870562998461556045886539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29913708665641037363924359 44870562998461556045886539)
            ·
              refine ⟨67305844497692334068829809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44870562998461556045886539 67305844497692334068829809)
              ·
                refine ⟨50479383373269250551622357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67305844497692334068829809 50479383373269250551622357)
                ·
                  refine ⟨1183110547810998059803649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 50479383373269250551622357 1183110547810998059803649)
                  ·
                    refine ⟨887332910858248544852737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1183110547810998059803649 887332910858248544852737)
                    ·
                      refine ⟨665499683143686408639553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 887332910858248544852737 665499683143686408639553)
                      ·
                        rfl

theorem cell23_1296056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 7, 2, 2].length) (baseStart_1296056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296056 prefixEnd_1296056 := by exact prefixLift 1296056
  have htrace : WordTrace (prefixWord ++ tailWord_1296056) baseStart_1296056 baseEnd_1296056 := by
    simpa [prefixWord, tailWord_1296056, baseEnd_1296056] using wordTrace_append hprefix tailTrace_1296056
  have hstable : (prefixWord ++ tailWord_1296056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296056).length < 2 ^ (prefixWord ++ tailWord_1296056).sum := by decide
  have hdescent : baseEnd_1296056 < baseStart_1296056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296077 : List Nat := [1, 6, 2, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_1296077 : Nat := 118140960795 + 1296077 * 2 ^ 59
def prefixEnd_1296077 : Nat := 4983230072969 + 3 ^ 40 * 1296077 * 2
def baseEnd_1296077 : Nat := 665510466237430826476957

theorem tailTrace_1296077 : CollatzResearch.WordTrace tailWord_1296077 prefixEnd_1296077 665510466237430826476957 := by
  unfold tailWord_1296077
  simp only [CollatzResearch.WordTrace]
  refine ⟨47271811725541856173950485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31514541150361237449300323 47271811725541856173950485)
  ·
    refine ⟨2215866174634774508153929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47271811725541856173950485 2215866174634774508153929)
    ·
      refine ⟨1661899630976080881115447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2215866174634774508153929 1661899630976080881115447)
      ·
        refine ⟨2492849446464121321673171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1661899630976080881115447 2492849446464121321673171)
        ·
          refine ⟨3739274169696181982509757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2492849446464121321673171 3739274169696181982509757)
          ·
            refine ⟨1402227813636068243441159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3739274169696181982509757 1402227813636068243441159)
            ·
              refine ⟨2103341720454102365161739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1402227813636068243441159 2103341720454102365161739)
              ·
                refine ⟨3155012580681153547742609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2103341720454102365161739 3155012580681153547742609)
                ·
                  refine ⟨2366259435510865160806957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3155012580681153547742609 2366259435510865160806957)
                  ·
                    refine ⟨887347288316574435302609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2366259435510865160806957 887347288316574435302609)
                    ·
                      refine ⟨665510466237430826476957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 887347288316574435302609 665510466237430826476957)
                      ·
                        rfl

theorem cell23_1296077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_1296077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296077 prefixEnd_1296077 := by exact prefixLift 1296077
  have htrace : WordTrace (prefixWord ++ tailWord_1296077) baseStart_1296077 baseEnd_1296077 := by
    simpa [prefixWord, tailWord_1296077, baseEnd_1296077] using wordTrace_append hprefix tailTrace_1296077
  have hstable : (prefixWord ++ tailWord_1296077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296077).length < 2 ^ (prefixWord ++ tailWord_1296077).sum := by decide
  have hdescent : baseEnd_1296077 < baseStart_1296077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296090 : List Nat := [3, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2]
def baseStart_1296090 : Nat := 118140960795 + 1296090 * 2 ^ 59
def prefixEnd_1296090 : Nat := 4983230072969 + 3 ^ 40 * 1296090 * 2
def baseEnd_1296090 : Nat := 665517141485939275614397

theorem tailTrace_1296090 : CollatzResearch.WordTrace tailWord_1296090 prefixEnd_1296090 665517141485939275614397 := by
  unfold tailWord_1296090
  simp only [CollatzResearch.WordTrace]
  refine ⟨11818071468623689848543431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31514857249663172929449149 11818071468623689848543431)
  ·
    refine ⟨17727107202935534772815147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11818071468623689848543431 17727107202935534772815147)
    ·
      refine ⟨26590660804403302159222721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17727107202935534772815147 26590660804403302159222721)
      ·
        refine ⟨19942995603302476619417041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26590660804403302159222721 19942995603302476619417041)
        ·
          refine ⟨14957246702476857464562781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19942995603302476619417041 14957246702476857464562781)
          ·
            refine ⟨5608967513428821549211043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14957246702476857464562781 5608967513428821549211043)
            ·
              refine ⟨8413451270143232323816565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5608967513428821549211043 8413451270143232323816565)
              ·
                refine ⟨788761056575928030357803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8413451270143232323816565 788761056575928030357803)
                ·
                  refine ⟨1183141584863892045536705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 788761056575928030357803 1183141584863892045536705)
                  ·
                    refine ⟨887356188647919034152529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1183141584863892045536705 887356188647919034152529)
                    ·
                      refine ⟨665517141485939275614397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 887356188647919034152529 665517141485939275614397)
                      ·
                        rfl

theorem cell23_1296090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2].length) (baseStart_1296090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296090 prefixEnd_1296090 := by exact prefixLift 1296090
  have htrace : WordTrace (prefixWord ++ tailWord_1296090) baseStart_1296090 baseEnd_1296090 := by
    simpa [prefixWord, tailWord_1296090, baseEnd_1296090] using wordTrace_append hprefix tailTrace_1296090
  have hstable : (prefixWord ++ tailWord_1296090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296090).length < 2 ^ (prefixWord ++ tailWord_1296090).sum := by decide
  have hdescent : baseEnd_1296090 < baseStart_1296090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296129 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_1296129 : Nat := 118140960795 + 1296129 * 2 ^ 59
def prefixEnd_1296129 : Nat := 4983230072969 + 3 ^ 40 * 1296129 * 2
def baseEnd_1296129 : Nat := 665537167231464623026717

theorem tailTrace_1296129 : CollatzResearch.WordTrace tailWord_1296129 prefixEnd_1296129 665537167231464623026717 := by
  unfold tailWord_1296129
  simp only [CollatzResearch.WordTrace]
  refine ⟨47273708321353469054843441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31515805547568979369895627 47273708321353469054843441)
  ·
    refine ⟨35455281241015101791132581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47273708321353469054843441 35455281241015101791132581)
    ·
      refine ⟨6647865232690331585837359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35455281241015101791132581 6647865232690331585837359)
      ·
        refine ⟨9971797849035497378756039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6647865232690331585837359 9971797849035497378756039)
        ·
          refine ⟨14957696773553246068134059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9971797849035497378756039 14957696773553246068134059)
          ·
            refine ⟨22436545160329869102201089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14957696773553246068134059 22436545160329869102201089)
            ·
              refine ⟨16827408870247401826650817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22436545160329869102201089 16827408870247401826650817)
              ·
                refine ⟨12620556652685551369988113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16827408870247401826650817 12620556652685551369988113)
                ·
                  refine ⟨9465417489514163527491085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12620556652685551369988113 9465417489514163527491085)
                  ·
                    refine ⟨3549531558567811322809157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9465417489514163527491085 3549531558567811322809157)
                    ·
                      refine ⟨665537167231464623026717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3549531558567811322809157 665537167231464623026717)
                      ·
                        rfl

theorem cell23_1296129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_1296129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296129 prefixEnd_1296129 := by exact prefixLift 1296129
  have htrace : WordTrace (prefixWord ++ tailWord_1296129) baseStart_1296129 baseEnd_1296129 := by
    simpa [prefixWord, tailWord_1296129, baseEnd_1296129] using wordTrace_append hprefix tailTrace_1296129
  have hstable : (prefixWord ++ tailWord_1296129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296129).length < 2 ^ (prefixWord ++ tailWord_1296129).sum := by decide
  have hdescent : baseEnd_1296129 < baseStart_1296129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296149 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 1, 3, 5]
def baseStart_1296149 : Nat := 118140960795 + 1296149 * 2 ^ 59
def prefixEnd_1296149 : Nat := 4983230072969 + 3 ^ 40 * 1296149 * 2
def baseEnd_1296149 : Nat := 665547436844554544776625

theorem tailTrace_1296149 : CollatzResearch.WordTrace tailWord_1296149 prefixEnd_1296149 665547436844554544776625 := by
  unfold tailWord_1296149
  simp only [CollatzResearch.WordTrace]
  refine ⟨47274437781281012470571501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31516291854187341647047667 47274437781281012470571501)
  ·
    refine ⟨17727914167980379676464313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47274437781281012470571501 17727914167980379676464313)
    ·
      refine ⟨13295935625985284757348235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17727914167980379676464313 13295935625985284757348235)
      ·
        refine ⟨19943903438977927136022353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13295935625985284757348235 19943903438977927136022353)
        ·
          refine ⟨14957927579233445352016765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19943903438977927136022353 14957927579233445352016765)
          ·
            refine ⟨5609222842212542007006287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14957927579233445352016765 5609222842212542007006287)
            ·
              refine ⟨8413834263318813010509431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5609222842212542007006287 8413834263318813010509431)
              ·
                refine ⟨12620751394978219515764147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8413834263318813010509431 12620751394978219515764147)
                ·
                  refine ⟨18931127092467329273646221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12620751394978219515764147 18931127092467329273646221)
                  ·
                    refine ⟨7099172659675248477617333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18931127092467329273646221 7099172659675248477617333)
                    ·
                      refine ⟨665547436844554544776625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7099172659675248477617333 665547436844554544776625)
                      ·
                        rfl

theorem cell23_1296149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_1296149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296149 prefixEnd_1296149 := by exact prefixLift 1296149
  have htrace : WordTrace (prefixWord ++ tailWord_1296149) baseStart_1296149 baseEnd_1296149 := by
    simpa [prefixWord, tailWord_1296149, baseEnd_1296149] using wordTrace_append hprefix tailTrace_1296149
  have hstable : (prefixWord ++ tailWord_1296149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296149).length < 2 ^ (prefixWord ++ tailWord_1296149).sum := by decide
  have hdescent : baseEnd_1296149 < baseStart_1296149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296158 : List Nat := [4, 3, 2, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_1296158 : Nat := 118140960795 + 1296158 * 2 ^ 59
def prefixEnd_1296158 : Nat := 4983230072969 + 3 ^ 40 * 1296158 * 2
def baseEnd_1296158 : Nat := 665552058170445009564085

theorem tailTrace_1296158 : CollatzResearch.WordTrace tailWord_1296158 prefixEnd_1296158 665552058170445009564085 := by
  unfold tailWord_1296158
  simp only [CollatzResearch.WordTrace]
  refine ⟨5909345754781050875956141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31516510692165604671766085 5909345754781050875956141)
  ·
    refine ⟨2216004658042894078483553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5909345754781050875956141 2216004658042894078483553)
    ·
      refine ⟨1662003493532170558862665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2216004658042894078483553 1662003493532170558862665)
      ·
        refine ⟨1246502620149127919146999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1662003493532170558862665 1246502620149127919146999)
        ·
          refine ⟨1869753930223691878720499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1246502620149127919146999 1869753930223691878720499)
          ·
            refine ⟨2804630895335537818080749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869753930223691878720499 2804630895335537818080749)
            ·
              refine ⟨1051736585750826681780281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2804630895335537818080749 1051736585750826681780281)
              ·
                refine ⟨788802439313120011335211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1051736585750826681780281 788802439313120011335211)
                ·
                  refine ⟨1183203658969680017002817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 788802439313120011335211 1183203658969680017002817)
                  ·
                    refine ⟨887402744227260012752113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1183203658969680017002817 887402744227260012752113)
                    ·
                      refine ⟨665552058170445009564085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 887402744227260012752113 665552058170445009564085)
                      ·
                        rfl

theorem cell23_1296158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_1296158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296158 prefixEnd_1296158 := by exact prefixLift 1296158
  have htrace : WordTrace (prefixWord ++ tailWord_1296158) baseStart_1296158 baseEnd_1296158 := by
    simpa [prefixWord, tailWord_1296158, baseEnd_1296158] using wordTrace_append hprefix tailTrace_1296158
  have hstable : (prefixWord ++ tailWord_1296158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296158).length < 2 ^ (prefixWord ++ tailWord_1296158).sum := by decide
  have hdescent : baseEnd_1296158 < baseStart_1296158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296163 : List Nat := [1, 1, 1, 4, 2, 1, 4, 1, 4, 2, 2]
def baseStart_1296163 : Nat := 118140960795 + 1296163 * 2 ^ 59
def prefixEnd_1296163 : Nat := 4983230072969 + 3 ^ 40 * 1296163 * 2
def baseEnd_1296163 : Nat := 665554625573717490001561

theorem tailTrace_1296163 : CollatzResearch.WordTrace tailWord_1296163 prefixEnd_1296163 665554625573717490001561 := by
  unfold tailWord_1296163
  simp only [CollatzResearch.WordTrace]
  refine ⟨47274948403230292861581143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31516632268820195241054095 47274948403230292861581143)
  ·
    refine ⟨70912422604845439292371715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47274948403230292861581143 70912422604845439292371715)
    ·
      refine ⟨106368633907268158938557573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70912422604845439292371715 106368633907268158938557573)
      ·
        refine ⟨19944118857612779800979545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106368633907268158938557573 19944118857612779800979545)
        ·
          refine ⟨14958089143209584850734659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19944118857612779800979545 14958089143209584850734659)
          ·
            refine ⟨22437133714814377276101989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14958089143209584850734659 22437133714814377276101989)
            ·
              refine ⟨4206962571527695739269123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22437133714814377276101989 4206962571527695739269123)
              ·
                refine ⟨6310443857291543608903685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4206962571527695739269123 6310443857291543608903685)
                ·
                  refine ⟨1183208223242164426669441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6310443857291543608903685 1183208223242164426669441)
                  ·
                    refine ⟨887406167431623320002081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1183208223242164426669441 887406167431623320002081)
                    ·
                      refine ⟨665554625573717490001561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 887406167431623320002081 665554625573717490001561)
                      ·
                        rfl

theorem cell23_1296163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 2, 2].length) (baseStart_1296163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296163 prefixEnd_1296163 := by exact prefixLift 1296163
  have htrace : WordTrace (prefixWord ++ tailWord_1296163) baseStart_1296163 baseEnd_1296163 := by
    simpa [prefixWord, tailWord_1296163, baseEnd_1296163] using wordTrace_append hprefix tailTrace_1296163
  have hstable : (prefixWord ++ tailWord_1296163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296163).length < 2 ^ (prefixWord ++ tailWord_1296163).sum := by decide
  have hdescent : baseEnd_1296163 < baseStart_1296163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296174 : List Nat := [4, 1, 3, 2, 2, 2, 2, 1, 2, 1, 3]
def baseStart_1296174 : Nat := 118140960795 + 1296174 * 2 ^ 59
def prefixEnd_1296174 : Nat := 4983230072969 + 3 ^ 40 * 1296174 * 2
def baseEnd_1296174 : Nat := 665560273860916946964011

theorem tailTrace_1296174 : CollatzResearch.WordTrace tailWord_1296174 prefixEnd_1296174 665560273860916946964011 := by
  unfold tailWord_1296174
  simp only [CollatzResearch.WordTrace]
  refine ⟨5909418700773805217528947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31516899737460294493487717 5909418700773805217528947)
  ·
    refine ⟨8864128051160707826293421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5909418700773805217528947 8864128051160707826293421)
    ·
      refine ⟨3324048019185265434860033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8864128051160707826293421 3324048019185265434860033)
      ·
        refine ⟨2493036014388949076145025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3324048019185265434860033 2493036014388949076145025)
        ·
          refine ⟨1869777010791711807108769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2493036014388949076145025 1869777010791711807108769)
          ·
            refine ⟨1402332758093783855331577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1869777010791711807108769 1402332758093783855331577)
            ·
              refine ⟨1051749568570337891498683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1402332758093783855331577 1051749568570337891498683)
              ·
                refine ⟨1577624352855506837248025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1051749568570337891498683 1577624352855506837248025)
                ·
                  refine ⟨1183218264641630127936019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1577624352855506837248025 1183218264641630127936019)
                  ·
                    refine ⟨1774827396962445191904029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1183218264641630127936019 1774827396962445191904029)
                    ·
                      refine ⟨665560273860916946964011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1774827396962445191904029 665560273860916946964011)
                      ·
                        rfl

theorem cell23_1296174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_1296174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296174 prefixEnd_1296174 := by exact prefixLift 1296174
  have htrace : WordTrace (prefixWord ++ tailWord_1296174) baseStart_1296174 baseEnd_1296174 := by
    simpa [prefixWord, tailWord_1296174, baseEnd_1296174] using wordTrace_append hprefix tailTrace_1296174
  have hstable : (prefixWord ++ tailWord_1296174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296174).length < 2 ^ (prefixWord ++ tailWord_1296174).sum := by decide
  have hdescent : baseEnd_1296174 < baseStart_1296174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296199 : List Nat := [1, 1, 4, 1, 2, 1, 2, 3, 1, 7]
def baseStart_1296199 : Nat := 118140960795 + 1296199 * 2 ^ 59
def prefixEnd_1296199 : Nat := 4983230072969 + 3 ^ 40 * 1296199 * 2
def baseEnd_1296199 : Nat := 221857703625759783050465

theorem tailTrace_1296199 : CollatzResearch.WordTrace tailWord_1296199 prefixEnd_1296199 221857703625759783050465 := by
  unfold tailWord_1296199
  simp only [CollatzResearch.WordTrace]
  refine ⟨47276261431099871009891651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31517507620733247339927767 47276261431099871009891651)
  ·
    refine ⟨70914392146649806514837477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47276261431099871009891651 70914392146649806514837477)
    ·
      refine ⟨13296448527496838721532027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70914392146649806514837477 13296448527496838721532027)
      ·
        refine ⟨19944672791245258082298041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13296448527496838721532027 19944672791245258082298041)
        ·
          refine ⟨14958504593433943561723531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19944672791245258082298041 14958504593433943561723531)
          ·
            refine ⟨22437756890150915342585297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14958504593433943561723531 22437756890150915342585297)
            ·
              refine ⟨16828317667613186506938973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22437756890150915342585297 16828317667613186506938973)
              ·
                refine ⟨6310619125354944940102115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16828317667613186506938973 6310619125354944940102115)
                ·
                  refine ⟨9465928688032417410153173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6310619125354944940102115 9465928688032417410153173)
                  ·
                    refine ⟨221857703625759783050465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9465928688032417410153173 221857703625759783050465)
                    ·
                      rfl

theorem cell23_1296199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_1296199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296199 prefixEnd_1296199 := by exact prefixLift 1296199
  have htrace : WordTrace (prefixWord ++ tailWord_1296199) baseStart_1296199 baseEnd_1296199 := by
    simpa [prefixWord, tailWord_1296199, baseEnd_1296199] using wordTrace_append hprefix tailTrace_1296199
  have hstable : (prefixWord ++ tailWord_1296199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296199).length < 2 ^ (prefixWord ++ tailWord_1296199).sum := by decide
  have hdescent : baseEnd_1296199 < baseStart_1296199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296220 : List Nat := [2, 2, 4, 2, 2, 1, 1, 4, 5]
def baseStart_1296220 : Nat := 118140960795 + 1296220 * 2 ^ 59
def prefixEnd_1296220 : Nat := 4983230072969 + 3 ^ 40 * 1296220 * 2
def baseEnd_1296220 : Nat := 73953765996780418554311

theorem tailTrace_1296220 : CollatzResearch.WordTrace tailWord_1296220 prefixEnd_1296220 73953765996780418554311 := by
  unfold tailWord_1296220
  simp only [CollatzResearch.WordTrace]
  refine ⟨23638513682011895798203057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31518018242682527730937409 23638513682011895798203057)
  ·
    refine ⟨17728885261508921848652293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23638513682011895798203057 17728885261508921848652293)
    ·
      refine ⟨3324165986532922846622305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17728885261508921848652293 3324165986532922846622305)
      ·
        refine ⟨2493124489899692134966729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3324165986532922846622305 2493124489899692134966729)
        ·
          refine ⟨1869843367424769101225047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2493124489899692134966729 1869843367424769101225047)
          ·
            refine ⟨2804765051137153651837571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869843367424769101225047 2804765051137153651837571)
            ·
              refine ⟨4207147576705730477756357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2804765051137153651837571 4207147576705730477756357)
              ·
                refine ⟨788840170632324464579317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4207147576705730477756357 788840170632324464579317)
                ·
                  refine ⟨73953765996780418554311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 788840170632324464579317 73953765996780418554311)
                  ·
                    rfl

theorem cell23_1296220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 5].length) (baseStart_1296220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296220 prefixEnd_1296220 := by exact prefixLift 1296220
  have htrace : WordTrace (prefixWord ++ tailWord_1296220) baseStart_1296220 baseEnd_1296220 := by
    simpa [prefixWord, tailWord_1296220, baseEnd_1296220] using wordTrace_append hprefix tailTrace_1296220
  have hstable : (prefixWord ++ tailWord_1296220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296220).length < 2 ^ (prefixWord ++ tailWord_1296220).sum := by decide
  have hdescent : baseEnd_1296220 < baseStart_1296220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296229 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 2, 8]
def baseStart_1296229 : Nat := 118140960795 + 1296229 * 2 ^ 59
def prefixEnd_1296229 : Nat := 4983230072969 + 3 ^ 40 * 1296229 * 2
def baseEnd_1296229 : Nat := 221862838432304743925419

theorem tailTrace_1296229 : CollatzResearch.WordTrace tailWord_1296229 prefixEnd_1296229 221862838432304743925419 := by
  unfold tailWord_1296229
  simp only [CollatzResearch.WordTrace]
  refine ⟨47277355620991186133483741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31518237080660790755655827 47277355620991186133483741)
  ·
    refine ⟨17729008357871694800056403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47277355620991186133483741 17729008357871694800056403)
    ·
      refine ⟨26593512536807542200084605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17729008357871694800056403 26593512536807542200084605)
      ·
        refine ⟨9972567201302828325031727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26593512536807542200084605 9972567201302828325031727)
        ·
          refine ⟨14958850801954242487547591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9972567201302828325031727 14958850801954242487547591)
          ·
            refine ⟨22438276202931363731321387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14958850801954242487547591 22438276202931363731321387)
            ·
              refine ⟨33657414304397045596982081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22438276202931363731321387 33657414304397045596982081)
              ·
                refine ⟨25243060728297784197736561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33657414304397045596982081 25243060728297784197736561)
                ·
                  refine ⟨18932295546223338148302421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25243060728297784197736561 18932295546223338148302421)
                  ·
                    refine ⟨221862838432304743925419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18932295546223338148302421 221862838432304743925419)
                    ·
                      rfl

theorem cell23_1296229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_1296229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296229 prefixEnd_1296229 := by exact prefixLift 1296229
  have htrace : WordTrace (prefixWord ++ tailWord_1296229) baseStart_1296229 baseEnd_1296229 := by
    simpa [prefixWord, tailWord_1296229, baseEnd_1296229] using wordTrace_append hprefix tailTrace_1296229
  have hstable : (prefixWord ++ tailWord_1296229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296229).length < 2 ^ (prefixWord ++ tailWord_1296229).sum := by decide
  have hdescent : baseEnd_1296229 < baseStart_1296229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296256 : List Nat := [2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 3]
def baseStart_1296256 : Nat := 118140960795 + 1296256 * 2 ^ 59
def prefixEnd_1296256 : Nat := 4983230072969 + 3 ^ 40 * 1296256 * 2
def baseEnd_1296256 : Nat := 665602379274585626138633

theorem tailTrace_1296256 : CollatzResearch.WordTrace tailWord_1296256 prefixEnd_1296256 665602379274585626138633 := by
  unfold tailWord_1296256
  simp only [CollatzResearch.WordTrace]
  refine ⟨23639170195946684872358311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31518893594595579829811081 23639170195946684872358311)
  ·
    refine ⟨35458755293920027308537467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23639170195946684872358311 35458755293920027308537467)
    ·
      refine ⟨53188132940880040962806201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35458755293920027308537467 53188132940880040962806201)
      ·
        refine ⟨39891099705660030722104651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53188132940880040962806201 39891099705660030722104651)
        ·
          refine ⟨59836649558490046083156977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39891099705660030722104651 59836649558490046083156977)
          ·
            refine ⟨44877487168867534562367733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59836649558490046083156977 44877487168867534562367733)
            ·
              refine ⟨4207264422081331365221975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44877487168867534562367733 4207264422081331365221975)
              ·
                refine ⟨6310896633121997047832963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4207264422081331365221975 6310896633121997047832963)
                ·
                  refine ⟨9466344949682995571749445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6310896633121997047832963 9466344949682995571749445)
                  ·
                    refine ⟨1774939678065561669703021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9466344949682995571749445 1774939678065561669703021)
                    ·
                      refine ⟨665602379274585626138633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1774939678065561669703021 665602379274585626138633)
                      ·
                        rfl

theorem cell23_1296256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 3].length) (baseStart_1296256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296256 prefixEnd_1296256 := by exact prefixLift 1296256
  have htrace : WordTrace (prefixWord ++ tailWord_1296256) baseStart_1296256 baseEnd_1296256 := by
    simpa [prefixWord, tailWord_1296256, baseEnd_1296256] using wordTrace_append hprefix tailTrace_1296256
  have hstable : (prefixWord ++ tailWord_1296256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296256).length < 2 ^ (prefixWord ++ tailWord_1296256).sum := by decide
  have hdescent : baseEnd_1296256 < baseStart_1296256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296303 : List Nat := [1, 1, 2, 1, 2, 2, 3, 4, 3, 1, 3]
def baseStart_1296303 : Nat := 118140960795 + 1296303 * 2 ^ 59
def prefixEnd_1296303 : Nat := 4983230072969 + 3 ^ 40 * 1296303 * 2
def baseEnd_1296303 : Nat := 665626512865346942250917

theorem tailTrace_1296303 : CollatzResearch.WordTrace tailWord_1296303 prefixEnd_1296303 665626512865346942250917 := by
  unfold tailWord_1296303
  simp only [CollatzResearch.WordTrace]
  refine ⟨47280054622723096771677563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31520036415148731181118375 47280054622723096771677563)
  ·
    refine ⟨70920081934084645157516345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47280054622723096771677563 70920081934084645157516345)
    ·
      refine ⟨53190061450563483868137259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70920081934084645157516345 53190061450563483868137259)
      ·
        refine ⟨79785092175845225802205889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53190061450563483868137259 79785092175845225802205889)
        ·
          refine ⟨59838819131883919351654417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79785092175845225802205889 59838819131883919351654417)
          ·
            refine ⟨44879114348912939513740813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59838819131883919351654417 44879114348912939513740813)
            ·
              refine ⟨16829667880842352317652805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44879114348912939513740813 16829667880842352317652805)
              ·
                refine ⟨3155562727657941059559901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16829667880842352317652805 3155562727657941059559901)
                ·
                  refine ⟨1183336022871727897334963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3155562727657941059559901 1183336022871727897334963)
                  ·
                    refine ⟨1775004034307591846002445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1183336022871727897334963 1775004034307591846002445)
                    ·
                      refine ⟨665626512865346942250917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1775004034307591846002445 665626512865346942250917)
                      ·
                        rfl

theorem cell23_1296303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 1, 3].length) (baseStart_1296303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296303 prefixEnd_1296303 := by exact prefixLift 1296303
  have htrace : WordTrace (prefixWord ++ tailWord_1296303) baseStart_1296303 baseEnd_1296303 := by
    simpa [prefixWord, tailWord_1296303, baseEnd_1296303] using wordTrace_append hprefix tailTrace_1296303
  have hstable : (prefixWord ++ tailWord_1296303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296303).length < 2 ^ (prefixWord ++ tailWord_1296303).sum := by decide
  have hdescent : baseEnd_1296303 < baseStart_1296303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296306 : List Nat := [3, 2, 1, 1, 1, 1, 1, 5, 3, 5]
def baseStart_1296306 : Nat := 118140960795 + 1296306 * 2 ^ 59
def prefixEnd_1296306 : Nat := 4983230072969 + 3 ^ 40 * 1296306 * 2
def baseEnd_1296306 : Nat := 221876017769103476837801

theorem tailTrace_1296306 : CollatzResearch.WordTrace tailWord_1296306 prefixEnd_1296306 221876017769103476837801 := by
  unfold tailWord_1296306
  simp only [CollatzResearch.WordTrace]
  refine ⟨11820041010428057071009193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31520109361141485522691181 11820041010428057071009193)
  ·
    refine ⟨8865030757821042803256895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11820041010428057071009193 8865030757821042803256895)
    ·
      refine ⟨13297546136731564204885343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8865030757821042803256895 13297546136731564204885343)
      ·
        refine ⟨19946319205097346307328015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13297546136731564204885343 19946319205097346307328015)
        ·
          refine ⟨29919478807646019460992023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19946319205097346307328015 29919478807646019460992023)
          ·
            refine ⟨44879218211469029191488035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29919478807646019460992023 44879218211469029191488035)
            ·
              refine ⟨67318827317203543787232053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44879218211469029191488035 67318827317203543787232053)
              ·
                refine ⟨6311140060987832230053005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67318827317203543787232053 6311140060987832230053005)
                ·
                  refine ⟨2366677522870437086269877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6311140060987832230053005 2366677522870437086269877)
                  ·
                    refine ⟨221876017769103476837801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2366677522870437086269877 221876017769103476837801)
                    ·
                      rfl

theorem cell23_1296306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_1296306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296306 prefixEnd_1296306 := by exact prefixLift 1296306
  have htrace : WordTrace (prefixWord ++ tailWord_1296306) baseStart_1296306 baseEnd_1296306 := by
    simpa [prefixWord, tailWord_1296306, baseEnd_1296306] using wordTrace_append hprefix tailTrace_1296306
  have hstable : (prefixWord ++ tailWord_1296306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296306).length < 2 ^ (prefixWord ++ tailWord_1296306).sum := by decide
  have hdescent : baseEnd_1296306 < baseStart_1296306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296313 : List Nat := [1, 2, 1, 4, 2, 1, 1, 3, 1, 5, 2]
def baseStart_1296313 : Nat := 118140960795 + 1296313 * 2 ^ 59
def prefixEnd_1296313 : Nat := 4983230072969 + 3 ^ 40 * 1296313 * 2
def baseEnd_1296313 : Nat := 665631647671891903125871

theorem tailTrace_1296313 : CollatzResearch.WordTrace tailWord_1296313 prefixEnd_1296313 665631647671891903125871 := by
  unfold tailWord_1296313
  simp only [CollatzResearch.WordTrace]
  refine ⟨47280419352686868479541593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31520279568457912319694395 47280419352686868479541593)
  ·
    refine ⟨35460314514515151359656195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47280419352686868479541593 35460314514515151359656195)
    ·
      refine ⟨53190471771772727039484293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35460314514515151359656195 53190471771772727039484293)
      ·
        refine ⟨9973213457207386319903305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53190471771772727039484293 9973213457207386319903305)
        ·
          refine ⟨7479910092905539739927479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9973213457207386319903305 7479910092905539739927479)
          ·
            refine ⟨11219865139358309609891219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7479910092905539739927479 11219865139358309609891219)
            ·
              refine ⟨16829797709037464414836829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11219865139358309609891219 16829797709037464414836829)
              ·
                refine ⟨6311174140889049155563811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16829797709037464414836829 6311174140889049155563811)
                ·
                  refine ⟨9466761211333573733345717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6311174140889049155563811 9466761211333573733345717)
                  ·
                    refine ⟨887508863562522537501161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9466761211333573733345717 887508863562522537501161)
                    ·
                      refine ⟨665631647671891903125871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 887508863562522537501161 665631647671891903125871)
                      ·
                        rfl

theorem cell23_1296313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_1296313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296313 prefixEnd_1296313 := by exact prefixLift 1296313
  have htrace : WordTrace (prefixWord ++ tailWord_1296313) baseStart_1296313 baseEnd_1296313 := by
    simpa [prefixWord, tailWord_1296313, baseEnd_1296313] using wordTrace_append hprefix tailTrace_1296313
  have hstable : (prefixWord ++ tailWord_1296313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296313).length < 2 ^ (prefixWord ++ tailWord_1296313).sum := by decide
  have hdescent : baseEnd_1296313 < baseStart_1296313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296356 : List Nat := [2, 3, 1, 1, 1, 1, 3, 3, 1, 1, 6]
def baseStart_1296356 : Nat := 118140960795 + 1296356 * 2 ^ 59
def prefixEnd_1296356 : Nat := 4983230072969 + 3 ^ 40 * 1296356 * 2
def baseEnd_1296356 : Nat := 665653727340035234888173

theorem tailTrace_1296356 : CollatzResearch.WordTrace tailWord_1296356 prefixEnd_1296356 665653727340035234888173 := by
  unfold tailWord_1296356
  simp only [CollatzResearch.WordTrace]
  refine ⟨23640993845765543411678461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31521325127687391215571281 23640993845765543411678461)
  ·
    refine ⟨8865372692162078779379423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23640993845765543411678461 8865372692162078779379423)
    ·
      refine ⟨13298059038243118169069135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8865372692162078779379423 13298059038243118169069135)
      ·
        refine ⟨19947088557364677253603703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13298059038243118169069135 19947088557364677253603703)
        ·
          refine ⟨29920632836047015880405555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19947088557364677253603703 29920632836047015880405555)
          ·
            refine ⟨44880949254070523820608333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29920632836047015880405555 44880949254070523820608333)
            ·
              refine ⟨16830355970276446432728125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44880949254070523820608333 16830355970276446432728125)
              ·
                refine ⟨6311383488853667412273047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16830355970276446432728125 6311383488853667412273047)
                ·
                  refine ⟨9467075233280501118409571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6311383488853667412273047 9467075233280501118409571)
                  ·
                    refine ⟨14200612849920751677614357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9467075233280501118409571 14200612849920751677614357)
                    ·
                      refine ⟨665653727340035234888173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14200612849920751677614357 665653727340035234888173)
                      ·
                        rfl

theorem cell23_1296356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_1296356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296356 prefixEnd_1296356 := by exact prefixLift 1296356
  have htrace : WordTrace (prefixWord ++ tailWord_1296356) baseStart_1296356 baseEnd_1296356 := by
    simpa [prefixWord, tailWord_1296356, baseEnd_1296356] using wordTrace_append hprefix tailTrace_1296356
  have hstable : (prefixWord ++ tailWord_1296356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296356).length < 2 ^ (prefixWord ++ tailWord_1296356).sum := by decide
  have hdescent : baseEnd_1296356 < baseStart_1296356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296360 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 5, 2, 2]
def baseStart_1296360 : Nat := 118140960795 + 1296360 * 2 ^ 59
def prefixEnd_1296360 : Nat := 4983230072969 + 3 ^ 40 * 1296360 * 2
def baseEnd_1296360 : Nat := 665655781262653219238155

theorem tailTrace_1296360 : CollatzResearch.WordTrace tailWord_1296360 prefixEnd_1296360 665655781262653219238155 := by
  unfold tailWord_1296360
  simp only [CollatzResearch.WordTrace]
  refine ⟨23641066791758297753251267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31521422389011063671001689 23641066791758297753251267)
  ·
    refine ⟨35461600187637446629876901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23641066791758297753251267 35461600187637446629876901)
    ·
      refine ⟨6649050035182021243101919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35461600187637446629876901 6649050035182021243101919)
      ·
        refine ⟨9973575052773031864652879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6649050035182021243101919 9973575052773031864652879)
        ·
          refine ⟨14960362579159547796979319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9973575052773031864652879 14960362579159547796979319)
          ·
            refine ⟨22440543868739321695468979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14960362579159547796979319 22440543868739321695468979)
            ·
              refine ⟨33660815803108982543203469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22440543868739321695468979 33660815803108982543203469)
              ·
                refine ⟨12622805926165868453701301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33660815803108982543203469 12622805926165868453701301)
                ·
                  refine ⟨1183388055578050167534497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12622805926165868453701301 1183388055578050167534497)
                  ·
                    refine ⟨887541041683537625650873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1183388055578050167534497 887541041683537625650873)
                    ·
                      refine ⟨665655781262653219238155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 887541041683537625650873 665655781262653219238155)
                      ·
                        rfl

theorem cell23_1296360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_1296360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296360 prefixEnd_1296360 := by exact prefixLift 1296360
  have htrace : WordTrace (prefixWord ++ tailWord_1296360) baseStart_1296360 baseEnd_1296360 := by
    simpa [prefixWord, tailWord_1296360, baseEnd_1296360] using wordTrace_append hprefix tailTrace_1296360
  have hstable : (prefixWord ++ tailWord_1296360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296360).length < 2 ^ (prefixWord ++ tailWord_1296360).sum := by decide
  have hdescent : baseEnd_1296360 < baseStart_1296360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296388 : List Nat := [2, 3, 2, 4, 1, 2, 2, 2, 1, 1, 3]
def baseStart_1296388 : Nat := 118140960795 + 1296388 * 2 ^ 59
def prefixEnd_1296388 : Nat := 4983230072969 + 3 ^ 40 * 1296388 * 2
def baseEnd_1296388 : Nat := 665670158720979109688027

theorem tailTrace_1296388 : CollatzResearch.WordTrace tailWord_1296388 prefixEnd_1296388 665670158720979109688027 := by
  unfold tailWord_1296388
  simp only [CollatzResearch.WordTrace]
  refine ⟨23641577413707578144260909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31522103218276770859014545 23641577413707578144260909)
  ·
    refine ⟨8865591530140341804097841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23641577413707578144260909 8865591530140341804097841)
    ·
      refine ⟨6649193647605256353073381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8865591530140341804097841 6649193647605256353073381)
      ·
        refine ⟨1246723808925985566201259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6649193647605256353073381 1246723808925985566201259)
        ·
          refine ⟨1870085713388978349301889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1246723808925985566201259 1870085713388978349301889)
          ·
            refine ⟨1402564285041733761976417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1870085713388978349301889 1402564285041733761976417)
            ·
              refine ⟨1051923213781300321482313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1402564285041733761976417 1051923213781300321482313)
              ·
                refine ⟨788942410335975241111735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1051923213781300321482313 788942410335975241111735)
                ·
                  refine ⟨1183413615503962861667603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 788942410335975241111735 1183413615503962861667603)
                  ·
                    refine ⟨1775120423255944292501405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1183413615503962861667603 1775120423255944292501405)
                    ·
                      refine ⟨665670158720979109688027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1775120423255944292501405 665670158720979109688027)
                      ·
                        rfl

theorem cell23_1296388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_1296388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296388 prefixEnd_1296388 := by exact prefixLift 1296388
  have htrace : WordTrace (prefixWord ++ tailWord_1296388) baseStart_1296388 baseEnd_1296388 := by
    simpa [prefixWord, tailWord_1296388, baseEnd_1296388] using wordTrace_append hprefix tailTrace_1296388
  have hstable : (prefixWord ++ tailWord_1296388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296388).length < 2 ^ (prefixWord ++ tailWord_1296388).sum := by decide
  have hdescent : baseEnd_1296388 < baseStart_1296388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296396 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 1, 9]
def baseStart_1296396 : Nat := 118140960795 + 1296396 * 2 ^ 59
def prefixEnd_1296396 : Nat := 4983230072969 + 3 ^ 40 * 1296396 * 2
def baseEnd_1296396 : Nat := 221891422188738359462663

theorem tailTrace_1296396 : CollatzResearch.WordTrace tailWord_1296396 prefixEnd_1296396 221891422188738359462663 := by
  unfold tailWord_1296396
  simp only [CollatzResearch.WordTrace]
  refine ⟨23641723305693086827406521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31522297740924115769875361 23641723305693086827406521)
  ·
    refine ⟨17731292479269815120554891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23641723305693086827406521 17731292479269815120554891)
    ·
      refine ⟨26596938718904722680832337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17731292479269815120554891 26596938718904722680832337)
      ·
        refine ⟨19947704039178542010624253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26596938718904722680832337 19947704039178542010624253)
        ·
          refine ⟨7480389014691953253984095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19947704039178542010624253 7480389014691953253984095)
          ·
            refine ⟨11220583522037929880976143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7480389014691953253984095 11220583522037929880976143)
            ·
              refine ⟨16830875283056894821464215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11220583522037929880976143 16830875283056894821464215)
              ·
                refine ⟨25246312924585342232196323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16830875283056894821464215 25246312924585342232196323)
                ·
                  refine ⟨37869469386878013348294485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25246312924585342232196323 37869469386878013348294485)
                  ·
                    refine ⟨221891422188738359462663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 37869469386878013348294485 221891422188738359462663)
                    ·
                      rfl

theorem cell23_1296396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_1296396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296396 prefixEnd_1296396 := by exact prefixLift 1296396
  have htrace : WordTrace (prefixWord ++ tailWord_1296396) baseStart_1296396 baseEnd_1296396 := by
    simpa [prefixWord, tailWord_1296396, baseEnd_1296396] using wordTrace_append hprefix tailTrace_1296396
  have hstable : (prefixWord ++ tailWord_1296396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296396).length < 2 ^ (prefixWord ++ tailWord_1296396).sum := by decide
  have hdescent : baseEnd_1296396 < baseStart_1296396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296410 : List Nat := [3, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3]
def baseStart_1296410 : Nat := 118140960795 + 1296410 * 2 ^ 59
def prefixEnd_1296410 : Nat := 4983230072969 + 3 ^ 40 * 1296410 * 2
def baseEnd_1296410 : Nat := 665681455295378023612925

theorem tailTrace_1296410 : CollatzResearch.WordTrace tailWord_1296410 prefixEnd_1296410 665681455295378023612925 := by
  unfold tailWord_1296410
  simp only [CollatzResearch.WordTrace]
  refine ⟨11820989308333863511455671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31522638155556969363881789 11820989308333863511455671)
  ·
    refine ⟨17731483962500795267183507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11820989308333863511455671 17731483962500795267183507)
    ·
      refine ⟨26597225943751192900775261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17731483962500795267183507 26597225943751192900775261)
      ·
        refine ⟨9973959728906697337790723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26597225943751192900775261 9973959728906697337790723)
        ·
          refine ⟨14960939593360046006686085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9973959728906697337790723 14960939593360046006686085)
          ·
            refine ⟨2805176173755008626253641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14960939593360046006686085 2805176173755008626253641)
            ·
              refine ⟨2103882130316256469690231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2805176173755008626253641 2103882130316256469690231)
              ·
                refine ⟨3155823195474384704535347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2103882130316256469690231 3155823195474384704535347)
                ·
                  refine ⟨4733734793211577056803021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3155823195474384704535347 4733734793211577056803021)
                  ·
                    refine ⟨1775150547454341396301133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4733734793211577056803021 1775150547454341396301133)
                    ·
                      refine ⟨665681455295378023612925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1775150547454341396301133 665681455295378023612925)
                      ·
                        rfl

theorem cell23_1296410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_1296410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296410 prefixEnd_1296410 := by exact prefixLift 1296410
  have htrace : WordTrace (prefixWord ++ tailWord_1296410) baseStart_1296410 baseEnd_1296410 := by
    simpa [prefixWord, tailWord_1296410, baseEnd_1296410] using wordTrace_append hprefix tailTrace_1296410
  have hstable : (prefixWord ++ tailWord_1296410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296410).length < 2 ^ (prefixWord ++ tailWord_1296410).sum := by decide
  have hdescent : baseEnd_1296410 < baseStart_1296410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296483 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 3]
def baseStart_1296483 : Nat := 118140960795 + 1296483 * 2 ^ 59
def prefixEnd_1296483 : Nat := 4983230072969 + 3 ^ 40 * 1296483 * 2
def baseEnd_1296483 : Nat := 665718939383156238000089

theorem tailTrace_1296483 : CollatzResearch.WordTrace tailWord_1296483 prefixEnd_1296483 665718939383156238000089 := by
  unfold tailWord_1296483
  simp only [CollatzResearch.WordTrace]
  refine ⟨47286619762070987513230103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31524413174713991675486735 47286619762070987513230103)
  ·
    refine ⟨70929929643106481269845155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47286619762070987513230103 70929929643106481269845155)
    ·
      refine ⟨106394894464659721904767733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70929929643106481269845155 106394894464659721904767733)
      ·
        refine ⟨9974521356061848928571975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106394894464659721904767733 9974521356061848928571975)
        ·
          refine ⟨14961782034092773392857963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9974521356061848928571975 14961782034092773392857963)
          ·
            refine ⟨22442673051139160089286945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14961782034092773392857963 22442673051139160089286945)
            ·
              refine ⟨16832004788354370066965209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22442673051139160089286945 16832004788354370066965209)
              ·
                refine ⟨12624003591265777550223907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16832004788354370066965209 12624003591265777550223907)
                ·
                  refine ⟨18936005386898666325335861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12624003591265777550223907 18936005386898666325335861)
                  ·
                    refine ⟨1775250505021749968000237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18936005386898666325335861 1775250505021749968000237)
                    ·
                      refine ⟨665718939383156238000089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1775250505021749968000237 665718939383156238000089)
                      ·
                        rfl

theorem cell23_1296483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_1296483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296483 prefixEnd_1296483 := by exact prefixLift 1296483
  have htrace : WordTrace (prefixWord ++ tailWord_1296483) baseStart_1296483 baseEnd_1296483 := by
    simpa [prefixWord, tailWord_1296483, baseEnd_1296483] using wordTrace_append hprefix tailTrace_1296483
  have hstable : (prefixWord ++ tailWord_1296483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296483).length < 2 ^ (prefixWord ++ tailWord_1296483).sum := by decide
  have hdescent : baseEnd_1296483 < baseStart_1296483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296503 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 4, 5]
def baseStart_1296503 : Nat := 118140960795 + 1296503 * 2 ^ 59
def prefixEnd_1296503 : Nat := 4983230072969 + 3 ^ 40 * 1296503 * 2
def baseEnd_1296503 : Nat := 221909736332082053249999

theorem tailTrace_1296503 : CollatzResearch.WordTrace tailWord_1296503 prefixEnd_1296503 221909736332082053249999 := by
  unfold tailWord_1296503
  simp only [CollatzResearch.WordTrace]
  refine ⟨47287349221998530928958163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31524899481332353952638775 47287349221998530928958163)
  ·
    refine ⟨70931023832997796393437245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47287349221998530928958163 70931023832997796393437245)
    ·
      refine ⟨26599133937374173647538967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70931023832997796393437245 26599133937374173647538967)
      ·
        refine ⟨39898700906061260471308451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26599133937374173647538967 39898700906061260471308451)
        ·
          refine ⟨59848051359091890706962677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39898700906061260471308451 59848051359091890706962677)
          ·
            refine ⟨5610754814914864753777751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59848051359091890706962677 5610754814914864753777751)
            ·
              refine ⟨8416132222372297130666627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5610754814914864753777751 8416132222372297130666627)
              ·
                refine ⟨12624198333558445695999941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8416132222372297130666627 12624198333558445695999941)
                ·
                  refine ⟨2367037187542208567999989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12624198333558445695999941 2367037187542208567999989)
                  ·
                    refine ⟨221909736332082053249999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2367037187542208567999989 221909736332082053249999)
                    ·
                      rfl

theorem cell23_1296503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 5].length) (baseStart_1296503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296503 prefixEnd_1296503 := by exact prefixLift 1296503
  have htrace : WordTrace (prefixWord ++ tailWord_1296503) baseStart_1296503 baseEnd_1296503 := by
    simpa [prefixWord, tailWord_1296503, baseEnd_1296503] using wordTrace_append hprefix tailTrace_1296503
  have hstable : (prefixWord ++ tailWord_1296503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296503).length < 2 ^ (prefixWord ++ tailWord_1296503).sum := by decide
  have hdescent : baseEnd_1296503 < baseStart_1296503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296557 : List Nat := [1, 5, 2, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_1296557 : Nat := 118140960795 + 1296557 * 2 ^ 59
def prefixEnd_1296557 : Nat := 4983230072969 + 3 ^ 40 * 1296557 * 2
def baseEnd_1296557 : Nat := 665756936951588948474749

theorem tailTrace_1296557 : CollatzResearch.WordTrace tailWord_1296557 prefixEnd_1296557 665756936951588948474749 := by
  unfold tailWord_1296557
  simp only [CollatzResearch.WordTrace]
  refine ⟨47289318763802898151423925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31526212509201932100949283 47289318763802898151423925)
  ·
    refine ⟨4433373634106521701695993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47289318763802898151423925 4433373634106521701695993)
    ·
      refine ⟨3325030225579891276271995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4433373634106521701695993 3325030225579891276271995)
      ·
        refine ⟨4987545338369836914407993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3325030225579891276271995 4987545338369836914407993)
        ·
          refine ⟨3740659003777377685805995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4987545338369836914407993 3740659003777377685805995)
          ·
            refine ⟨5610988505666066528708993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3740659003777377685805995 5610988505666066528708993)
            ·
              refine ⟨4208241379249549896531745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5610988505666066528708993 4208241379249549896531745)
              ·
                refine ⟨3156181034437162422398809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4208241379249549896531745 3156181034437162422398809)
                ·
                  refine ⟨2367135775827871816799107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3156181034437162422398809 2367135775827871816799107)
                  ·
                    refine ⟨3550703663741807725198661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2367135775827871816799107 3550703663741807725198661)
                    ·
                      refine ⟨665756936951588948474749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3550703663741807725198661 665756936951588948474749)
                      ·
                        rfl

theorem cell23_1296557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_1296557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296557 prefixEnd_1296557 := by exact prefixLift 1296557
  have htrace : WordTrace (prefixWord ++ tailWord_1296557) baseStart_1296557 baseEnd_1296557 := by
    simpa [prefixWord, tailWord_1296557, baseEnd_1296557] using wordTrace_append hprefix tailTrace_1296557
  have hstable : (prefixWord ++ tailWord_1296557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296557).length < 2 ^ (prefixWord ++ tailWord_1296557).sum := by decide
  have hdescent : baseEnd_1296557 < baseStart_1296557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296558 : List Nat := [4, 1, 4, 2, 1, 2, 2, 2, 5]
def baseStart_1296558 : Nat := 118140960795 + 1296558 * 2 ^ 59
def prefixEnd_1296558 : Nat := 4983230072969 + 3 ^ 40 * 1296558 * 2
def baseEnd_1296558 : Nat := 73973050048027049395805

theorem tailTrace_1296558 : CollatzResearch.WordTrace tailWord_1296558 prefixEnd_1296558 73973050048027049395805 := by
  unfold tailWord_1296558
  simp only [CollatzResearch.WordTrace]
  refine ⟨5911169404599909415276291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31526236824532850214806885 5911169404599909415276291)
  ·
    refine ⟨8866754106899864122914437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5911169404599909415276291 8866754106899864122914437)
    ·
      refine ⟨1662516395043724523046457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8866754106899864122914437 1662516395043724523046457)
      ·
        refine ⟨1246887296282793392284843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1662516395043724523046457 1246887296282793392284843)
        ·
          refine ⟨1870330944424190088427265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1246887296282793392284843 1870330944424190088427265)
          ·
            refine ⟨1402748208318142566320449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1870330944424190088427265 1402748208318142566320449)
            ·
              refine ⟨1052061156238606924740337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1402748208318142566320449 1052061156238606924740337)
              ·
                refine ⟨789045867178955193555253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1052061156238606924740337 789045867178955193555253)
                ·
                  refine ⟨73973050048027049395805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 789045867178955193555253 73973050048027049395805)
                  ·
                    rfl

theorem cell23_1296558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 5].length) (baseStart_1296558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296558 prefixEnd_1296558 := by exact prefixLift 1296558
  have htrace : WordTrace (prefixWord ++ tailWord_1296558) baseStart_1296558 baseEnd_1296558 := by
    simpa [prefixWord, tailWord_1296558, baseEnd_1296558] using wordTrace_append hprefix tailTrace_1296558
  have hstable : (prefixWord ++ tailWord_1296558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296558).length < 2 ^ (prefixWord ++ tailWord_1296558).sum := by decide
  have hdescent : baseEnd_1296558 < baseStart_1296558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296574 : List Nat := [4, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2]
def baseStart_1296574 : Nat := 118140960795 + 1296574 * 2 ^ 59
def prefixEnd_1296574 : Nat := 4983230072969 + 3 ^ 40 * 1296574 * 2
def baseEnd_1296574 : Nat := 665765666122715381962171

theorem tailTrace_1296574 : CollatzResearch.WordTrace tailWord_1296574 prefixEnd_1296574 665765666122715381962171 := by
  unfold tailWord_1296574
  simp only [CollatzResearch.WordTrace]
  refine ⟨5911242350592663756849097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31526625869827540036528517 5911242350592663756849097)
  ·
    refine ⟨4433431762944497817636823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5911242350592663756849097 4433431762944497817636823)
    ·
      refine ⟨6650147644416746726455235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4433431762944497817636823 6650147644416746726455235)
      ·
        refine ⟨9975221466625120089682853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6650147644416746726455235 9975221466625120089682853)
        ·
          refine ⟨1870354024992210016815535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9975221466625120089682853 1870354024992210016815535)
          ·
            refine ⟨2805531037488315025223303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1870354024992210016815535 2805531037488315025223303)
            ·
              refine ⟨4208296556232472537834955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2805531037488315025223303 4208296556232472537834955)
              ·
                refine ⟨6312444834348708806752433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4208296556232472537834955 6312444834348708806752433)
                ·
                  refine ⟨4734333625761531605064325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6312444834348708806752433 4734333625761531605064325)
                  ·
                    refine ⟨887687554830287175949561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4734333625761531605064325 887687554830287175949561)
                    ·
                      refine ⟨665765666122715381962171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 887687554830287175949561 665765666122715381962171)
                      ·
                        rfl

theorem cell23_1296574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_1296574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296574 prefixEnd_1296574 := by exact prefixLift 1296574
  have htrace : WordTrace (prefixWord ++ tailWord_1296574) baseStart_1296574 baseEnd_1296574 := by
    simpa [prefixWord, tailWord_1296574, baseEnd_1296574] using wordTrace_append hprefix tailTrace_1296574
  have hstable : (prefixWord ++ tailWord_1296574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296574).length < 2 ^ (prefixWord ++ tailWord_1296574).sum := by decide
  have hdescent : baseEnd_1296574 < baseStart_1296574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296594 : List Nat := [3, 2, 2, 2, 1, 4, 1, 1, 2, 2, 3]
def baseStart_1296594 : Nat := 118140960795 + 1296594 * 2 ^ 59
def prefixEnd_1296594 : Nat := 4983230072969 + 3 ^ 40 * 1296594 * 2
def baseEnd_1296594 : Nat := 665775935735805303712079

theorem tailTrace_1296594 : CollatzResearch.WordTrace tailWord_1296594 prefixEnd_1296594 665775935735805303712079 := by
  unfold tailWord_1296594
  simp only [CollatzResearch.WordTrace]
  refine ⟨11822667066167213367630209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31527112176445902313680557 11822667066167213367630209)
  ·
    refine ⟨8867000299625410025722657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11822667066167213367630209 8867000299625410025722657)
    ·
      refine ⟨6650250224719057519291993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8867000299625410025722657 6650250224719057519291993)
      ·
        refine ⟨4987687668539293139468995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6650250224719057519291993 4987687668539293139468995)
        ·
          refine ⟨7481531502808939709203493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4987687668539293139468995 7481531502808939709203493)
          ·
            refine ⟨1402787156776676195475655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7481531502808939709203493 1402787156776676195475655)
            ·
              refine ⟨2104180735165014293213483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1402787156776676195475655 2104180735165014293213483)
              ·
                refine ⟨3156271102747521439820225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2104180735165014293213483 3156271102747521439820225)
                ·
                  refine ⟨2367203327060641079865169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3156271102747521439820225 2367203327060641079865169)
                  ·
                    refine ⟨1775402495295480809898877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2367203327060641079865169 1775402495295480809898877)
                    ·
                      refine ⟨665775935735805303712079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1775402495295480809898877 665775935735805303712079)
                      ·
                        rfl

theorem cell23_1296594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_1296594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296594 prefixEnd_1296594 := by exact prefixLift 1296594
  have htrace : WordTrace (prefixWord ++ tailWord_1296594) baseStart_1296594 baseEnd_1296594 := by
    simpa [prefixWord, tailWord_1296594, baseEnd_1296594] using wordTrace_append hprefix tailTrace_1296594
  have hstable : (prefixWord ++ tailWord_1296594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296594).length < 2 ^ (prefixWord ++ tailWord_1296594).sum := by decide
  have hdescent : baseEnd_1296594 < baseStart_1296594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296640 : List Nat := [2, 1, 1, 2, 1, 1, 7, 1, 1, 6]
def baseStart_1296640 : Nat := 118140960795 + 1296640 * 2 ^ 59
def prefixEnd_1296640 : Nat := 4983230072969 + 3 ^ 40 * 1296640 * 2
def baseEnd_1296640 : Nat := 221933185281970707912289

theorem tailTrace_1296640 : CollatzResearch.WordTrace tailWord_1296640 prefixEnd_1296640 221933185281970707912289 := by
  unfold tailWord_1296640
  simp only [CollatzResearch.WordTrace]
  refine ⟨23646173011251101663347687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31528230681668135551130249 23646173011251101663347687)
  ·
    refine ⟨35469259516876652495021531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23646173011251101663347687 35469259516876652495021531)
    ·
      refine ⟨53203889275314978742532297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35469259516876652495021531 53203889275314978742532297)
      ·
        refine ⟨39902916956486234056899223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53203889275314978742532297 39902916956486234056899223)
        ·
          refine ⟨59854375434729351085348835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39902916956486234056899223 59854375434729351085348835)
          ·
            refine ⟨89781563152094026628023253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59854375434729351085348835 89781563152094026628023253)
            ·
              refine ⟨2104255386377203749094295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 89781563152094026628023253 2104255386377203749094295)
              ·
                refine ⟨3156383079565805623641443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2104255386377203749094295 3156383079565805623641443)
                ·
                  refine ⟨4734574619348708435462165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3156383079565805623641443 4734574619348708435462165)
                  ·
                    refine ⟨221933185281970707912289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4734574619348708435462165 221933185281970707912289)
                    ·
                      rfl

theorem cell23_1296640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 1, 6].length) (baseStart_1296640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296640 prefixEnd_1296640 := by exact prefixLift 1296640
  have htrace : WordTrace (prefixWord ++ tailWord_1296640) baseStart_1296640 baseEnd_1296640 := by
    simpa [prefixWord, tailWord_1296640, baseEnd_1296640] using wordTrace_append hprefix tailTrace_1296640
  have hstable : (prefixWord ++ tailWord_1296640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296640).length < 2 ^ (prefixWord ++ tailWord_1296640).sum := by decide
  have hdescent : baseEnd_1296640 < baseStart_1296640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296644 : List Nat := [2, 3, 2, 2, 3, 1, 2, 2, 1, 5]
def baseStart_1296644 : Nat := 118140960795 + 1296644 * 2 ^ 59
def prefixEnd_1296644 : Nat := 4983230072969 + 3 ^ 40 * 1296644 * 2
def baseEnd_1296644 : Nat := 221933869922843369362283

theorem tailTrace_1296644 : CollatzResearch.WordTrace tailWord_1296644 prefixEnd_1296644 221933869922843369362283 := by
  unfold tailWord_1296644
  simp only [CollatzResearch.WordTrace]
  refine ⟨23646245957243856004920493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31528327942991808006560657 23646245957243856004920493)
  ·
    refine ⟨8867342233966446001845185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23646245957243856004920493 8867342233966446001845185)
    ·
      refine ⟨6650506675474834501383889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8867342233966446001845185 6650506675474834501383889)
      ·
        refine ⟨4987880006606125876037917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6650506675474834501383889 4987880006606125876037917)
        ·
          refine ⟨1870455002477297203514219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4987880006606125876037917 1870455002477297203514219)
          ·
            refine ⟨2805682503715945805271329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1870455002477297203514219 2805682503715945805271329)
            ·
              refine ⟨2104261877786959353953497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2805682503715945805271329 2104261877786959353953497)
              ·
                refine ⟨1578196408340219515465123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2104261877786959353953497 1578196408340219515465123)
                ·
                  refine ⟨2367294612510329273197685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1578196408340219515465123 2367294612510329273197685)
                  ·
                    refine ⟨221933869922843369362283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2367294612510329273197685 221933869922843369362283)
                    ·
                      rfl

theorem cell23_1296644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_1296644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296644 prefixEnd_1296644 := by exact prefixLift 1296644
  have htrace : WordTrace (prefixWord ++ tailWord_1296644) baseStart_1296644 baseEnd_1296644 := by
    simpa [prefixWord, tailWord_1296644, baseEnd_1296644] using wordTrace_append hprefix tailTrace_1296644
  have hstable : (prefixWord ++ tailWord_1296644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296644).length < 2 ^ (prefixWord ++ tailWord_1296644).sum := by decide
  have hdescent : baseEnd_1296644 < baseStart_1296644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296667 : List Nat := [1, 1, 1, 1, 1, 1, 8, 3, 1, 2, 3]
def baseStart_1296667 : Nat := 118140960795 + 1296667 * 2 ^ 59
def prefixEnd_1296667 : Nat := 4983230072969 + 3 ^ 40 * 1296667 * 2
def baseEnd_1296667 : Nat := 665813419823583518099243

theorem tailTrace_1296667 : CollatzResearch.WordTrace tailWord_1296667 prefixEnd_1296667 665813419823583518099243 := by
  unfold tailWord_1296667
  simp only [CollatzResearch.WordTrace]
  refine ⟨47293330793404386937928255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31528887195602924625285503 47293330793404386937928255)
  ·
    refine ⟨70939996190106580406892383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47293330793404386937928255 70939996190106580406892383)
    ·
      refine ⟨106409994285159870610338575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70939996190106580406892383 106409994285159870610338575)
      ·
        refine ⟨159614991427739805915507863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106409994285159870610338575 159614991427739805915507863)
        ·
          refine ⟨239422487141609708873261795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159614991427739805915507863 239422487141609708873261795)
          ·
            refine ⟨359133730712414563309892693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239422487141609708873261795 359133730712414563309892693)
            ·
              refine ⟨4208598406786108163787805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 359133730712414563309892693 4208598406786108163787805)
              ·
                refine ⟨1578224402544790561420427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4208598406786108163787805 1578224402544790561420427)
                ·
                  refine ⟨2367336603817185842130641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1578224402544790561420427 2367336603817185842130641)
                  ·
                    refine ⟨1775502452862889381597981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2367336603817185842130641 1775502452862889381597981)
                    ·
                      refine ⟨665813419823583518099243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1775502452862889381597981 665813419823583518099243)
                      ·
                        rfl

theorem cell23_1296667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 2, 3].length) (baseStart_1296667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296667 prefixEnd_1296667 := by exact prefixLift 1296667
  have htrace : WordTrace (prefixWord ++ tailWord_1296667) baseStart_1296667 baseEnd_1296667 := by
    simpa [prefixWord, tailWord_1296667, baseEnd_1296667] using wordTrace_append hprefix tailTrace_1296667
  have hstable : (prefixWord ++ tailWord_1296667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296667).length < 2 ^ (prefixWord ++ tailWord_1296667).sum := by decide
  have hdescent : baseEnd_1296667 < baseStart_1296667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296730 : List Nat := [3, 1, 1, 2, 1, 2, 1, 4, 2, 6]
def baseStart_1296730 : Nat := 118140960795 + 1296730 * 2 ^ 59
def prefixEnd_1296730 : Nat := 4983230072969 + 3 ^ 40 * 1296730 * 2
def baseEnd_1296730 : Nat := 221948589701605590537151

theorem tailTrace_1296730 : CollatzResearch.WordTrace tailWord_1296730 prefixEnd_1296730 221948589701605590537151 := by
  unfold tailWord_1296730
  simp only [CollatzResearch.WordTrace]
  refine ⟨11823907148044037174367911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31530419061450765798314429 11823907148044037174367911)
  ·
    refine ⟨17735860722066055761551867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11823907148044037174367911 17735860722066055761551867)
    ·
      refine ⟨26603791083099083642327801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17735860722066055761551867 26603791083099083642327801)
      ·
        refine ⟨19952843312324312731745851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26603791083099083642327801 19952843312324312731745851)
        ·
          refine ⟨29929264968486469097618777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19952843312324312731745851 29929264968486469097618777)
          ·
            refine ⟨22446948726364851823214083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29929264968486469097618777 22446948726364851823214083)
            ·
              refine ⟨33670423089547277734821125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22446948726364851823214083 33670423089547277734821125)
              ·
                refine ⟨6313204329290114575278961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33670423089547277734821125 6313204329290114575278961)
                ·
                  refine ⟨4734903246967585931459221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6313204329290114575278961 4734903246967585931459221)
                  ·
                    refine ⟨221948589701605590537151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4734903246967585931459221 221948589701605590537151)
                    ·
                      rfl

theorem cell23_1296730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_1296730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296730 prefixEnd_1296730 := by exact prefixLift 1296730
  have htrace : WordTrace (prefixWord ++ tailWord_1296730) baseStart_1296730 baseEnd_1296730 := by
    simpa [prefixWord, tailWord_1296730, baseEnd_1296730] using wordTrace_append hprefix tailTrace_1296730
  have hstable : (prefixWord ++ tailWord_1296730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296730).length < 2 ^ (prefixWord ++ tailWord_1296730).sum := by decide
  have hdescent : baseEnd_1296730 < baseStart_1296730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296754 : List Nat := [3, 2, 1, 2, 1, 3, 1, 3, 1, 4, 2]
def baseStart_1296754 : Nat := 118140960795 + 1296754 * 2 ^ 59
def prefixEnd_1296754 : Nat := 4983230072969 + 3 ^ 40 * 1296754 * 2
def baseEnd_1296754 : Nat := 665858092640524677711343

theorem tailTrace_1296754 : CollatzResearch.WordTrace tailWord_1296754 prefixEnd_1296754 665858092640524677711343 := by
  unfold tailWord_1296754
  simp only [CollatzResearch.WordTrace]
  refine ⟨11824125986022300199086329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31531002629392800530896877 11824125986022300199086329)
  ·
    refine ⟨8868094489516725149314747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11824125986022300199086329 8868094489516725149314747)
    ·
      refine ⟨13302141734275087723972121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8868094489516725149314747 13302141734275087723972121)
      ·
        refine ⟨9976606300706315792979091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13302141734275087723972121 9976606300706315792979091)
        ·
          refine ⟨14964909451059473689468637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9976606300706315792979091 14964909451059473689468637)
          ·
            refine ⟨5611841044147302633550739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14964909451059473689468637 5611841044147302633550739)
            ·
              refine ⟨8417761566220953950326109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5611841044147302633550739 8417761566220953950326109)
              ·
                refine ⟨3156660587332857731372291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8417761566220953950326109 3156660587332857731372291)
                ·
                  refine ⟨4734990880999286597058437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3156660587332857731372291 4734990880999286597058437)
                  ·
                    refine ⟨887810790187366236948457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4734990880999286597058437 887810790187366236948457)
                    ·
                      refine ⟨665858092640524677711343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 887810790187366236948457 665858092640524677711343)
                      ·
                        rfl

theorem cell23_1296754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_1296754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296754 prefixEnd_1296754 := by exact prefixLift 1296754
  have htrace : WordTrace (prefixWord ++ tailWord_1296754) baseStart_1296754 baseEnd_1296754 := by
    simpa [prefixWord, tailWord_1296754, baseEnd_1296754] using wordTrace_append hprefix tailTrace_1296754
  have hstable : (prefixWord ++ tailWord_1296754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296754).length < 2 ^ (prefixWord ++ tailWord_1296754).sum := by decide
  have hdescent : baseEnd_1296754 < baseStart_1296754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296788 : List Nat := [2, 4, 2, 1, 3, 1, 1, 1, 4, 2, 2]
def baseStart_1296788 : Nat := 118140960795 + 1296788 * 2 ^ 59
def prefixEnd_1296788 : Nat := 4983230072969 + 3 ^ 40 * 1296788 * 2
def baseEnd_1296788 : Nat := 665875550982777544686187

theorem tailTrace_1296788 : CollatzResearch.WordTrace tailWord_1296788 prefixEnd_1296788 665875550982777544686187 := by
  unfold tailWord_1296788
  simp only [CollatzResearch.WordTrace]
  refine ⟨23648872012983012301541509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31531829350644016402055345 23648872012983012301541509)
  ·
    refine ⟨4434163502434314806539033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23648872012983012301541509 4434163502434314806539033)
    ·
      refine ⟨3325622626825736104904275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4434163502434314806539033 3325622626825736104904275)
      ·
        refine ⟨4988433940238604157356413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3325622626825736104904275 4988433940238604157356413)
        ·
          refine ⟨1870662727589476559008655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4988433940238604157356413 1870662727589476559008655)
          ·
            refine ⟨2805994091384214838512983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1870662727589476559008655 2805994091384214838512983)
            ·
              refine ⟨4208991137076322257769475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2805994091384214838512983 4208991137076322257769475)
              ·
                refine ⟨6313486705614483386654213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4208991137076322257769475 6313486705614483386654213)
                ·
                  refine ⟨1183778757302715634997665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6313486705614483386654213 1183778757302715634997665)
                  ·
                    refine ⟨887834067977036726248249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1183778757302715634997665 887834067977036726248249)
                    ·
                      refine ⟨665875550982777544686187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 887834067977036726248249 665875550982777544686187)
                      ·
                        rfl

theorem cell23_1296788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_1296788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296788 prefixEnd_1296788 := by exact prefixLift 1296788
  have htrace : WordTrace (prefixWord ++ tailWord_1296788) baseStart_1296788 baseEnd_1296788 := by
    simpa [prefixWord, tailWord_1296788, baseEnd_1296788] using wordTrace_append hprefix tailTrace_1296788
  have hstable : (prefixWord ++ tailWord_1296788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296788).length < 2 ^ (prefixWord ++ tailWord_1296788).sum := by decide
  have hdescent : baseEnd_1296788 < baseStart_1296788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296794 : List Nat := [3, 1, 1, 4, 1, 2, 2, 4, 5]
def baseStart_1296794 : Nat := 118140960795 + 1296794 * 2 ^ 59
def prefixEnd_1296794 : Nat := 4983230072969 + 3 ^ 40 * 1296794 * 2
def baseEnd_1296794 : Nat := 73986514651856057912351

theorem tailTrace_1296794 : CollatzResearch.WordTrace tailWord_1296794 prefixEnd_1296794 73986514651856057912351 := by
  unfold tailWord_1296794
  simp only [CollatzResearch.WordTrace]
  refine ⟨11824490715986071906950359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31531975242629525085200957 11824490715986071906950359)
  ·
    refine ⟨17736736073979107860425539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11824490715986071906950359 17736736073979107860425539)
    ·
      refine ⟨26605104110968661790638309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17736736073979107860425539 26605104110968661790638309)
      ·
        refine ⟨4988457020806624085744683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26605104110968661790638309 4988457020806624085744683)
        ·
          refine ⟨7482685531209936128617025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4988457020806624085744683 7482685531209936128617025)
          ·
            refine ⟨5612014148407452096462769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7482685531209936128617025 5612014148407452096462769)
            ·
              refine ⟨4209010611305589072347077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5612014148407452096462769 4209010611305589072347077)
              ·
                refine ⟨789189489619797951065077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4209010611305589072347077 789189489619797951065077)
                ·
                  refine ⟨73986514651856057912351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 789189489619797951065077 73986514651856057912351)
                  ·
                    rfl

theorem cell23_1296794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 5].length) (baseStart_1296794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296794 prefixEnd_1296794 := by exact prefixLift 1296794
  have htrace : WordTrace (prefixWord ++ tailWord_1296794) baseStart_1296794 baseEnd_1296794 := by
    simpa [prefixWord, tailWord_1296794, baseEnd_1296794] using wordTrace_append hprefix tailTrace_1296794
  have hstable : (prefixWord ++ tailWord_1296794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296794).length < 2 ^ (prefixWord ++ tailWord_1296794).sum := by decide
  have hdescent : baseEnd_1296794 < baseStart_1296794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296807 : List Nat := [1, 1, 6, 1, 1, 2, 1, 2, 1, 7]
def baseStart_1296807 : Nat := 118140960795 + 1296807 * 2 ^ 59
def prefixEnd_1296807 : Nat := 4983230072969 + 3 ^ 40 * 1296807 * 2
def baseEnd_1296807 : Nat := 221961769038404323449533

theorem tailTrace_1296807 : CollatzResearch.WordTrace tailWord_1296807 prefixEnd_1296807 221961769038404323449533 := by
  unfold tailWord_1296807
  simp only [CollatzResearch.WordTrace]
  refine ⟨47298437012897190848024675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31532291341931460565349783 47298437012897190848024675)
  ·
    refine ⟨70947655519345786272037013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47298437012897190848024675 70947655519345786272037013)
    ·
      refine ⟨3325671352469333731501735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 70947655519345786272037013 3325671352469333731501735)
      ·
        refine ⟨4988507028704000597252603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3325671352469333731501735 4988507028704000597252603)
        ·
          refine ⟨7482760543056000895878905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4988507028704000597252603 7482760543056000895878905)
          ·
            refine ⟨5612070407292000671909179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7482760543056000895878905 5612070407292000671909179)
            ·
              refine ⟨8418105610938001007863769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5612070407292000671909179 8418105610938001007863769)
              ·
                refine ⟨6313579208203500755897827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8418105610938001007863769 6313579208203500755897827)
                ·
                  refine ⟨9470368812305251133846741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6313579208203500755897827 9470368812305251133846741)
                  ·
                    refine ⟨221961769038404323449533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9470368812305251133846741 221961769038404323449533)
                    ·
                      rfl

theorem cell23_1296807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_1296807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296807 prefixEnd_1296807 := by exact prefixLift 1296807
  have htrace : WordTrace (prefixWord ++ tailWord_1296807) baseStart_1296807 baseEnd_1296807 := by
    simpa [prefixWord, tailWord_1296807, baseEnd_1296807] using wordTrace_append hprefix tailTrace_1296807
  have hstable : (prefixWord ++ tailWord_1296807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296807).length < 2 ^ (prefixWord ++ tailWord_1296807).sum := by decide
  have hdescent : baseEnd_1296807 < baseStart_1296807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296904 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 3, 5, 2]
def baseStart_1296904 : Nat := 118140960795 + 1296904 * 2 ^ 59
def prefixEnd_1296904 : Nat := 4983230072969 + 3 ^ 40 * 1296904 * 2
def baseEnd_1296904 : Nat := 665935114738699090835653

theorem tailTrace_1296904 : CollatzResearch.WordTrace tailWord_1296904 prefixEnd_1296904 665935114738699090835653 := by
  unfold tailWord_1296904
  simp only [CollatzResearch.WordTrace]
  refine ⟨23650987446772888207152883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31534649929030517609537177 23650987446772888207152883)
  ·
    refine ⟨35476481170159332310729325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23650987446772888207152883 35476481170159332310729325)
    ·
      refine ⟨13303680438809749616523497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35476481170159332310729325 13303680438809749616523497)
      ·
        refine ⟨9977760329107312212392623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13303680438809749616523497 9977760329107312212392623)
        ·
          refine ⟨14966640493660968318588935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9977760329107312212392623 14966640493660968318588935)
          ·
            refine ⟨22449960740491452477883403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14966640493660968318588935 22449960740491452477883403)
            ·
              refine ⟨33674941110737178716825105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22449960740491452477883403 33674941110737178716825105)
              ·
                refine ⟨25256205833052884037618829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33674941110737178716825105 25256205833052884037618829)
                ·
                  refine ⟨9471077187394831514107061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25256205833052884037618829 9471077187394831514107061)
                  ·
                    refine ⟨887913486318265454447537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9471077187394831514107061 887913486318265454447537)
                    ·
                      refine ⟨665935114738699090835653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 887913486318265454447537 665935114738699090835653)
                      ·
                        rfl

theorem cell23_1296904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_1296904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296904 prefixEnd_1296904 := by exact prefixLift 1296904
  have htrace : WordTrace (prefixWord ++ tailWord_1296904) baseStart_1296904 baseEnd_1296904 := by
    simpa [prefixWord, tailWord_1296904, baseEnd_1296904] using wordTrace_append hprefix tailTrace_1296904
  have hstable : (prefixWord ++ tailWord_1296904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296904).length < 2 ^ (prefixWord ++ tailWord_1296904).sum := by decide
  have hdescent : baseEnd_1296904 < baseStart_1296904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296928 : List Nat := [2, 1, 1, 6, 2, 1, 1, 2, 3, 1, 3]
def baseStart_1296928 : Nat := 118140960795 + 1296928 * 2 ^ 59
def prefixEnd_1296928 : Nat := 4983230072969 + 3 ^ 40 * 1296928 * 2
def baseEnd_1296928 : Nat := 665947438274406996935543

theorem tailTrace_1296928 : CollatzResearch.WordTrace tailWord_1296928 prefixEnd_1296928 665947438274406996935543 := by
  unfold tailWord_1296928
  simp only [CollatzResearch.WordTrace]
  refine ⟨23651425122729414256589719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31535233496972552342119625 23651425122729414256589719)
  ·
    refine ⟨35477137684094121384884579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23651425122729414256589719 35477137684094121384884579)
    ·
      refine ⟨53215706526141182077326869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35477137684094121384884579 53215706526141182077326869)
      ·
        refine ⟨2494486243412867909874697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53215706526141182077326869 2494486243412867909874697)
        ·
          refine ⟨1870864682559650932406023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2494486243412867909874697 1870864682559650932406023)
          ·
            refine ⟨2806297023839476398609035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1870864682559650932406023 2806297023839476398609035)
            ·
              refine ⟨4209445535759214597913553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2806297023839476398609035 4209445535759214597913553)
              ·
                refine ⟨3157084151819410948435165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4209445535759214597913553 3157084151819410948435165)
                ·
                  refine ⟨1183906556932279105663187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3157084151819410948435165 1183906556932279105663187)
                  ·
                    refine ⟨1775859835398418658494781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1183906556932279105663187 1775859835398418658494781)
                    ·
                      refine ⟨665947438274406996935543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1775859835398418658494781 665947438274406996935543)
                      ·
                        rfl

theorem cell23_1296928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_1296928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296928 prefixEnd_1296928 := by exact prefixLift 1296928
  have htrace : WordTrace (prefixWord ++ tailWord_1296928) baseStart_1296928 baseEnd_1296928 := by
    simpa [prefixWord, tailWord_1296928, baseEnd_1296928] using wordTrace_append hprefix tailTrace_1296928
  have hstable : (prefixWord ++ tailWord_1296928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296928).length < 2 ^ (prefixWord ++ tailWord_1296928).sum := by decide
  have hdescent : baseEnd_1296928 < baseStart_1296928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296938 : List Nat := [3, 1, 4, 1, 1, 2, 3, 1, 2, 3, 2]
def baseStart_1296938 : Nat := 118140960795 + 1296938 * 2 ^ 59
def prefixEnd_1296938 : Nat := 4983230072969 + 3 ^ 40 * 1296938 * 2
def baseEnd_1296938 : Nat := 665952573080951957810497

theorem tailTrace_1296938 : CollatzResearch.WordTrace tailWord_1296938 prefixEnd_1296938 665952573080951957810497 := by
  unfold tailWord_1296938
  simp only [CollatzResearch.WordTrace]
  refine ⟨11825803743855650055260867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31535476650281733480695645 11825803743855650055260867)
  ·
    refine ⟨17738705615783475082891301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11825803743855650055260867 17738705615783475082891301)
    ·
      refine ⟨3326007302959401578042119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17738705615783475082891301 3326007302959401578042119)
      ·
        refine ⟨4989010954439102367063179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3326007302959401578042119 4989010954439102367063179)
        ·
          refine ⟨7483516431658653550594769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4989010954439102367063179 7483516431658653550594769)
          ·
            refine ⟨5612637323743990162946077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7483516431658653550594769 5612637323743990162946077)
            ·
              refine ⟨2104738996403996311104779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5612637323743990162946077 2104738996403996311104779)
              ·
                refine ⟨3157108494605994466657169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2104738996403996311104779 3157108494605994466657169)
                ·
                  refine ⟨2367831370954495849992877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3157108494605994466657169 2367831370954495849992877)
                  ·
                    refine ⟨887936764107935943747329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2367831370954495849992877 887936764107935943747329)
                    ·
                      refine ⟨665952573080951957810497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 887936764107935943747329 665952573080951957810497)
                      ·
                        rfl

theorem cell23_1296938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_1296938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296938 prefixEnd_1296938 := by exact prefixLift 1296938
  have htrace : WordTrace (prefixWord ++ tailWord_1296938) baseStart_1296938 baseEnd_1296938 := by
    simpa [prefixWord, tailWord_1296938, baseEnd_1296938] using wordTrace_append hprefix tailTrace_1296938
  have hstable : (prefixWord ++ tailWord_1296938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296938).length < 2 ^ (prefixWord ++ tailWord_1296938).sum := by decide
  have hdescent : baseEnd_1296938 < baseStart_1296938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296951 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 5, 2, 2]
def baseStart_1296951 : Nat := 118140960795 + 1296951 * 2 ^ 59
def prefixEnd_1296951 : Nat := 4983230072969 + 3 ^ 40 * 1296951 * 2
def baseEnd_1296951 : Nat := 665959248329460406947937

theorem tailTrace_1296951 : CollatzResearch.WordTrace tailWord_1296951 prefixEnd_1296951 665959248329460406947937 := by
  unfold tailWord_1296951
  simp only [CollatzResearch.WordTrace]
  refine ⟨47303689124375503441266707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31535792749583668960844471 47303689124375503441266707)
  ·
    refine ⟨70955533686563255161900061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47303689124375503441266707 70955533686563255161900061)
    ·
      refine ⟨26608325132461220685712523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70955533686563255161900061 26608325132461220685712523)
      ·
        refine ⟨39912487698691831028568785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26608325132461220685712523 39912487698691831028568785)
        ·
          refine ⟨29934365774018873271426589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39912487698691831028568785 29934365774018873271426589)
          ·
            refine ⟨11225387165257077476784971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29934365774018873271426589 11225387165257077476784971)
            ·
              refine ⟨16838080747885616215177457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11225387165257077476784971 16838080747885616215177457)
              ·
                refine ⟨12628560560914212161383093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16838080747885616215177457 12628560560914212161383093)
                ·
                  refine ⟨1183927552585707390129665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12628560560914212161383093 1183927552585707390129665)
                  ·
                    refine ⟨887945664439280542597249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1183927552585707390129665 887945664439280542597249)
                    ·
                      refine ⟨665959248329460406947937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 887945664439280542597249 665959248329460406947937)
                      ·
                        rfl

theorem cell23_1296951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 2, 2].length) (baseStart_1296951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296951 prefixEnd_1296951 := by exact prefixLift 1296951
  have htrace : WordTrace (prefixWord ++ tailWord_1296951) baseStart_1296951 baseEnd_1296951 := by
    simpa [prefixWord, tailWord_1296951, baseEnd_1296951] using wordTrace_append hprefix tailTrace_1296951
  have hstable : (prefixWord ++ tailWord_1296951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296951).length < 2 ^ (prefixWord ++ tailWord_1296951).sum := by decide
  have hdescent : baseEnd_1296951 < baseStart_1296951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296961 : List Nat := [1, 2, 5, 1, 1, 3, 1, 1, 4, 4]
def baseStart_1296961 : Nat := 118140960795 + 1296961 * 2 ^ 59
def prefixEnd_1296961 : Nat := 4983230072969 + 3 ^ 40 * 1296961 * 2
def baseEnd_1296961 : Nat := 221988127712001789274297

theorem tailTrace_1296961 : CollatzResearch.WordTrace tailWord_1296961 prefixEnd_1296961 221988127712001789274297 := by
  unfold tailWord_1296961
  simp only [CollatzResearch.WordTrace]
  refine ⟨47304053854339275149130737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31536035902892850099420491 47304053854339275149130737)
  ·
    refine ⟨35478040390754456361848053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47304053854339275149130737 35478040390754456361848053)
    ·
      refine ⟨3326066286633230283923255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35478040390754456361848053 3326066286633230283923255)
      ·
        refine ⟨4989099429949845425884883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3326066286633230283923255 4989099429949845425884883)
        ·
          refine ⟨7483649144924768138827325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4989099429949845425884883 7483649144924768138827325)
          ·
            refine ⟨2806368429346788052060247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7483649144924768138827325 2806368429346788052060247)
            ·
              refine ⟨4209552644020182078090371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2806368429346788052060247 4209552644020182078090371)
              ·
                refine ⟨6314328966030273117135557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4209552644020182078090371 6314328966030273117135557)
                ·
                  refine ⟨1183936681130676209462917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6314328966030273117135557 1183936681130676209462917)
                  ·
                    refine ⟨221988127712001789274297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1183936681130676209462917 221988127712001789274297)
                    ·
                      rfl

theorem cell23_1296961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_1296961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296961 prefixEnd_1296961 := by exact prefixLift 1296961
  have htrace : WordTrace (prefixWord ++ tailWord_1296961) baseStart_1296961 baseEnd_1296961 := by
    simpa [prefixWord, tailWord_1296961, baseEnd_1296961] using wordTrace_append hprefix tailTrace_1296961
  have hstable : (prefixWord ++ tailWord_1296961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296961).length < 2 ^ (prefixWord ++ tailWord_1296961).sum := by decide
  have hdescent : baseEnd_1296961 < baseStart_1296961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296978 : List Nat := [3, 2, 2, 1, 2, 1, 5, 1, 2, 4]
def baseStart_1296978 : Nat := 118140960795 + 1296978 * 2 ^ 59
def prefixEnd_1296978 : Nat := 4983230072969 + 3 ^ 40 * 1296978 * 2
def baseEnd_1296978 : Nat := 221991037435710600436771

theorem tailTrace_1296978 : CollatzResearch.WordTrace tailWord_1296978 prefixEnd_1296978 221991037435710600436771 := by
  unfold tailWord_1296978
  simp only [CollatzResearch.WordTrace]
  refine ⟨11826168473819421763124897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31536449263518458034999725 11826168473819421763124897)
  ·
    refine ⟨8869626355364566322343673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11826168473819421763124897 8869626355364566322343673)
    ·
      refine ⟨6652219766523424741757755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8869626355364566322343673 6652219766523424741757755)
      ·
        refine ⟨9978329649785137112636633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6652219766523424741757755 9978329649785137112636633)
        ·
          refine ⟨7483747237338852834477475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9978329649785137112636633 7483747237338852834477475)
          ·
            refine ⟨11225620856008279251716213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7483747237338852834477475 11225620856008279251716213)
            ·
              refine ⟨1052401955250776179848395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11225620856008279251716213 1052401955250776179848395)
              ·
                refine ⟨1578602932876164269772593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1052401955250776179848395 1578602932876164269772593)
                ·
                  refine ⟨1183952199657123202329445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1578602932876164269772593 1183952199657123202329445)
                  ·
                    refine ⟨221991037435710600436771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1183952199657123202329445 221991037435710600436771)
                    ·
                      rfl

theorem cell23_1296978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_1296978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1296978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1296978 prefixEnd_1296978 := by exact prefixLift 1296978
  have htrace : WordTrace (prefixWord ++ tailWord_1296978) baseStart_1296978 baseEnd_1296978 := by
    simpa [prefixWord, tailWord_1296978, baseEnd_1296978] using wordTrace_append hprefix tailTrace_1296978
  have hstable : (prefixWord ++ tailWord_1296978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296978).length < 2 ^ (prefixWord ++ tailWord_1296978).sum := by decide
  have hdescent : baseEnd_1296978 < baseStart_1296978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297075 : List Nat := [1, 1, 1, 2, 3, 5, 2, 2, 2, 2, 2]
def baseStart_1297075 : Nat := 118140960795 + 1297075 * 2 ^ 59
def prefixEnd_1297075 : Nat := 4983230072969 + 3 ^ 40 * 1297075 * 2
def baseEnd_1297075 : Nat := 666022919930617921797367

theorem tailTrace_1297075 : CollatzResearch.WordTrace tailWord_1297075 prefixEnd_1297075 666022919930617921797367 := by
  unfold tailWord_1297075
  simp only [CollatzResearch.WordTrace]
  refine ⟨47308211775926272618780679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31538807850617515079187119 47308211775926272618780679)
  ·
    refine ⟨70962317663889408928171019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47308211775926272618780679 70962317663889408928171019)
    ·
      refine ⟨106443476495834113392256529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70962317663889408928171019 106443476495834113392256529)
      ·
        refine ⟨79832607371875585044192397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106443476495834113392256529 79832607371875585044192397)
        ·
          refine ⟨29937227764453344391572149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79832607371875585044192397 29937227764453344391572149)
          ·
            refine ⟨2806615102917501036709889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29937227764453344391572149 2806615102917501036709889)
            ·
              refine ⟨2104961327188125777532417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2806615102917501036709889 2104961327188125777532417)
              ·
                refine ⟨1578720995391094333149313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2104961327188125777532417 1578720995391094333149313)
                ·
                  refine ⟨1184040746543320749861985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1578720995391094333149313 1184040746543320749861985)
                  ·
                    refine ⟨888030559907490562396489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1184040746543320749861985 888030559907490562396489)
                    ·
                      refine ⟨666022919930617921797367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 888030559907490562396489 666022919930617921797367)
                      ·
                        rfl

theorem cell23_1297075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 2, 2].length) (baseStart_1297075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297075 prefixEnd_1297075 := by exact prefixLift 1297075
  have htrace : WordTrace (prefixWord ++ tailWord_1297075) baseStart_1297075 baseEnd_1297075 := by
    simpa [prefixWord, tailWord_1297075, baseEnd_1297075] using wordTrace_append hprefix tailTrace_1297075
  have hstable : (prefixWord ++ tailWord_1297075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297075).length < 2 ^ (prefixWord ++ tailWord_1297075).sum := by decide
  have hdescent : baseEnd_1297075 < baseStart_1297075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297111 : List Nat := [1, 1, 3, 2, 1, 4, 3, 1, 2, 5]
def baseStart_1297111 : Nat := 118140960795 + 1297111 * 2 ^ 59
def prefixEnd_1297111 : Nat := 4983230072969 + 3 ^ 40 * 1297111 * 2
def baseEnd_1297111 : Nat := 222013801744726593649067

theorem tailTrace_1297111 : CollatzResearch.WordTrace tailWord_1297111 prefixEnd_1297111 222013801744726593649067 := by
  unfold tailWord_1297111
  simp only [CollatzResearch.WordTrace]
  refine ⟨47309524803795850767091187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31539683202530567178060791 47309524803795850767091187)
  ·
    refine ⟨70964287205693776150636781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47309524803795850767091187 70964287205693776150636781)
    ·
      refine ⟨26611607702135166056488793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70964287205693776150636781 26611607702135166056488793)
      ·
        refine ⟨19958705776601374542366595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26611607702135166056488793 19958705776601374542366595)
        ·
          refine ⟨29938058664902061813549893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19958705776601374542366595 29938058664902061813549893)
          ·
            refine ⟨5613385999669136590040605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29938058664902061813549893 5613385999669136590040605)
            ·
              refine ⟨2105019749875926221265227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5613385999669136590040605 2105019749875926221265227)
              ·
                refine ⟨3157529624813889331897841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2105019749875926221265227 3157529624813889331897841)
                ·
                  refine ⟨2368147218610416998923381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3157529624813889331897841 2368147218610416998923381)
                  ·
                    refine ⟨222013801744726593649067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2368147218610416998923381 222013801744726593649067)
                    ·
                      rfl

theorem cell23_1297111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 5].length) (baseStart_1297111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297111 prefixEnd_1297111 := by exact prefixLift 1297111
  have htrace : WordTrace (prefixWord ++ tailWord_1297111) baseStart_1297111 baseEnd_1297111 := by
    simpa [prefixWord, tailWord_1297111, baseEnd_1297111] using wordTrace_append hprefix tailTrace_1297111
  have hstable : (prefixWord ++ tailWord_1297111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297111).length < 2 ^ (prefixWord ++ tailWord_1297111).sum := by decide
  have hdescent : baseEnd_1297111 < baseStart_1297111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297144 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 2, 1, 6]
def baseStart_1297144 : Nat := 118140960795 + 1297144 * 2 ^ 59
def prefixEnd_1297144 : Nat := 4983230072969 + 3 ^ 40 * 1297144 * 2
def baseEnd_1297144 : Nat := 666058350095778151834549

theorem tailTrace_1297144 : CollatzResearch.WordTrace tailWord_1297144 prefixEnd_1297144 666058350095778151834549 := by
  unfold tailWord_1297144
  simp only [CollatzResearch.WordTrace]
  refine ⟨23655364206338148701521243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31540485608450864935361657 23655364206338148701521243)
  ·
    refine ⟨35483046309507223052281865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23655364206338148701521243 35483046309507223052281865)
    ·
      refine ⟨26612284732130417289211399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35483046309507223052281865 26612284732130417289211399)
      ·
        refine ⟨39918427098195625933817099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26612284732130417289211399 39918427098195625933817099)
        ·
          refine ⟨59877640647293438900725649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39918427098195625933817099 59877640647293438900725649)
          ·
            refine ⟨44908230485470079175544237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59877640647293438900725649 44908230485470079175544237)
            ·
              refine ⟨16840586432051279690829089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44908230485470079175544237 16840586432051279690829089)
              ·
                refine ⟨12630439824038459768121817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16840586432051279690829089 12630439824038459768121817)
                ·
                  refine ⟨9472829868028844826091363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12630439824038459768121817 9472829868028844826091363)
                  ·
                    refine ⟨14209244802043267239137045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9472829868028844826091363 14209244802043267239137045)
                    ·
                      refine ⟨666058350095778151834549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14209244802043267239137045 666058350095778151834549)
                      ·
                        rfl

theorem cell23_1297144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_1297144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297144 prefixEnd_1297144 := by exact prefixLift 1297144
  have htrace : WordTrace (prefixWord ++ tailWord_1297144) baseStart_1297144 baseEnd_1297144 := by
    simpa [prefixWord, tailWord_1297144, baseEnd_1297144] using wordTrace_append hprefix tailTrace_1297144
  have hstable : (prefixWord ++ tailWord_1297144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297144).length < 2 ^ (prefixWord ++ tailWord_1297144).sum := by decide
  have hdescent : baseEnd_1297144 < baseStart_1297144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297148 : List Nat := [2, 2, 2, 1, 3, 2, 2, 1, 2, 4, 2]
def baseStart_1297148 : Nat := 118140960795 + 1297148 * 2 ^ 59
def prefixEnd_1297148 : Nat := 4983230072969 + 3 ^ 40 * 1297148 * 2
def baseEnd_1297148 : Nat := 666060404018396136184531

theorem tailTrace_1297148 : CollatzResearch.WordTrace tailWord_1297148 prefixEnd_1297148 666060404018396136184531 := by
  unfold tailWord_1297148
  simp only [CollatzResearch.WordTrace]
  refine ⟨23655437152330903043094049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31540582869774537390792065 23655437152330903043094049)
  ·
    refine ⟨17741577864248177282320537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23655437152330903043094049 17741577864248177282320537)
    ·
      refine ⟨13306183398186132961740403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17741577864248177282320537 13306183398186132961740403)
      ·
        refine ⟨19959275097279199442610605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13306183398186132961740403 19959275097279199442610605)
        ·
          refine ⟨7484728161479699790978977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19959275097279199442610605 7484728161479699790978977)
          ·
            refine ⟨5613546121109774843234233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7484728161479699790978977 5613546121109774843234233)
            ·
              refine ⟨4210159590832331132425675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5613546121109774843234233 4210159590832331132425675)
              ·
                refine ⟨6315239386248496698638513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4210159590832331132425675 6315239386248496698638513)
                ·
                  refine ⟨4736429539686372523978885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6315239386248496698638513 4736429539686372523978885)
                  ·
                    refine ⟨888080538691194848246041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4736429539686372523978885 888080538691194848246041)
                    ·
                      refine ⟨666060404018396136184531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 888080538691194848246041 666060404018396136184531)
                      ·
                        rfl

theorem cell23_1297148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 2, 4, 2].length) (baseStart_1297148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297148 prefixEnd_1297148 := by exact prefixLift 1297148
  have htrace : WordTrace (prefixWord ++ tailWord_1297148) baseStart_1297148 baseEnd_1297148 := by
    simpa [prefixWord, tailWord_1297148, baseEnd_1297148] using wordTrace_append hprefix tailTrace_1297148
  have hstable : (prefixWord ++ tailWord_1297148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297148).length < 2 ^ (prefixWord ++ tailWord_1297148).sum := by decide
  have hdescent : baseEnd_1297148 < baseStart_1297148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297192 : List Nat := [2, 1, 5, 1, 1, 1, 5, 2, 1, 4]
def baseStart_1297192 : Nat := 118140960795 + 1297192 * 2 ^ 59
def prefixEnd_1297192 : Nat := 4983230072969 + 3 ^ 40 * 1297192 * 2
def baseEnd_1297192 : Nat := 222027665722397988011443

theorem tailTrace_1297192 : CollatzResearch.WordTrace tailWord_1297192 prefixEnd_1297192 222027665722397988011443 := by
  unfold tailWord_1297192
  simp only [CollatzResearch.WordTrace]
  refine ⟨23656239558251200800394915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31541652744334934400526553 23656239558251200800394915)
  ·
    refine ⟨35484359337376801200592373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23656239558251200800394915 35484359337376801200592373)
    ·
      refine ⟨3326658687879075112555535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35484359337376801200592373 3326658687879075112555535)
      ·
        refine ⟨4989988031818612668833303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3326658687879075112555535 4989988031818612668833303)
        ·
          refine ⟨7484982047727919003249955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4989988031818612668833303 7484982047727919003249955)
          ·
            refine ⟨11227473071591878504874933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7484982047727919003249955 11227473071591878504874933)
            ·
              refine ⟨1052575600461738609832025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11227473071591878504874933 1052575600461738609832025)
              ·
                refine ⟨789431700346303957374019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1052575600461738609832025 789431700346303957374019)
                ·
                  refine ⟨1184147550519455936061029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 789431700346303957374019 1184147550519455936061029)
                  ·
                    refine ⟨222027665722397988011443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1184147550519455936061029 222027665722397988011443)
                    ·
                      rfl

theorem cell23_1297192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_1297192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297192 prefixEnd_1297192 := by exact prefixLift 1297192
  have htrace : WordTrace (prefixWord ++ tailWord_1297192) baseStart_1297192 baseEnd_1297192 := by
    simpa [prefixWord, tailWord_1297192, baseEnd_1297192] using wordTrace_append hprefix tailTrace_1297192
  have hstable : (prefixWord ++ tailWord_1297192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297192).length < 2 ^ (prefixWord ++ tailWord_1297192).sum := by decide
  have hdescent : baseEnd_1297192 < baseStart_1297192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297201 : List Nat := [1, 2, 2, 3, 2, 1, 2, 2, 3, 5]
def baseStart_1297201 : Nat := 118140960795 + 1297201 * 2 ^ 59
def prefixEnd_1297201 : Nat := 4983230072969 + 3 ^ 40 * 1297201 * 2
def baseEnd_1297201 : Nat := 222029206164361476273929

theorem tailTrace_1297201 : CollatzResearch.WordTrace tailWord_1297201 prefixEnd_1297201 222029206164361476273929 := by
  unfold tailWord_1297201
  simp only [CollatzResearch.WordTrace]
  refine ⟨47312807373469796137867457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31541871582313197425244971 47312807373469796137867457)
  ·
    refine ⟨35484605530102347103400593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47312807373469796137867457 35484605530102347103400593)
    ·
      refine ⟨26613454147576760327550445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35484605530102347103400593 26613454147576760327550445)
      ·
        refine ⟨9980045305341285122831417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26613454147576760327550445 9980045305341285122831417)
        ·
          refine ⟨7485033979005963842123563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9980045305341285122831417 7485033979005963842123563)
          ·
            refine ⟨11227550968508945763185345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7485033979005963842123563 11227550968508945763185345)
            ·
              refine ⟨8420663226381709322389009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11227550968508945763185345 8420663226381709322389009)
              ·
                refine ⟨6315497419786281991791757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8420663226381709322389009 6315497419786281991791757)
                ·
                  refine ⟨2368311532419855746921909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6315497419786281991791757 2368311532419855746921909)
                  ·
                    refine ⟨222029206164361476273929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2368311532419855746921909 222029206164361476273929)
                    ·
                      rfl

theorem cell23_1297201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 5].length) (baseStart_1297201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297201 prefixEnd_1297201 := by exact prefixLift 1297201
  have htrace : WordTrace (prefixWord ++ tailWord_1297201) baseStart_1297201 baseEnd_1297201 := by
    simpa [prefixWord, tailWord_1297201, baseEnd_1297201] using wordTrace_append hprefix tailTrace_1297201
  have hstable : (prefixWord ++ tailWord_1297201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297201).length < 2 ^ (prefixWord ++ tailWord_1297201).sum := by decide
  have hdescent : baseEnd_1297201 < baseStart_1297201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297205 : List Nat := [1, 3, 3, 1, 3, 3, 2, 1, 6]
def baseStart_1297205 : Nat := 118140960795 + 1297205 * 2 ^ 59
def prefixEnd_1297205 : Nat := 4983230072969 + 3 ^ 40 * 1297205 * 2
def baseEnd_1297205 : Nat := 74009963601744712574641

theorem tailTrace_1297205 : CollatzResearch.WordTrace tailWord_1297205 prefixEnd_1297205 74009963601744712574641 := by
  unfold tailWord_1297205
  simp only [CollatzResearch.WordTrace]
  refine ⟨47312953265455304821013069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31541968843636869880675379 47312953265455304821013069)
  ·
    refine ⟨17742357474545739307879901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47312953265455304821013069 17742357474545739307879901)
    ·
      refine ⟨6653384052954652240454963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17742357474545739307879901 6653384052954652240454963)
      ·
        refine ⟨9980076079431978360682445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6653384052954652240454963 9980076079431978360682445)
        ·
          refine ⟨3742528529786991885255917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9980076079431978360682445 3742528529786991885255917)
          ·
            refine ⟨1403448198670121956970969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3742528529786991885255917 1403448198670121956970969)
            ·
              refine ⟨1052586149002591467728227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1403448198670121956970969 1052586149002591467728227)
              ·
                refine ⟨1578879223503887201592341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1052586149002591467728227 1578879223503887201592341)
                ·
                  refine ⟨74009963601744712574641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1578879223503887201592341 74009963601744712574641)
                  ·
                    rfl

theorem cell23_1297205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 6].length) (baseStart_1297205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297205 prefixEnd_1297205 := by exact prefixLift 1297205
  have htrace : WordTrace (prefixWord ++ tailWord_1297205) baseStart_1297205 baseEnd_1297205 := by
    simpa [prefixWord, tailWord_1297205, baseEnd_1297205] using wordTrace_append hprefix tailTrace_1297205
  have hstable : (prefixWord ++ tailWord_1297205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297205).length < 2 ^ (prefixWord ++ tailWord_1297205).sum := by decide
  have hdescent : baseEnd_1297205 < baseStart_1297205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297208 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 4, 3, 2]
def baseStart_1297208 : Nat := 118140960795 + 1297208 * 2 ^ 59
def prefixEnd_1297208 : Nat := 4983230072969 + 3 ^ 40 * 1297208 * 2
def baseEnd_1297208 : Nat := 666091212857665901434255

theorem tailTrace_1297208 : CollatzResearch.WordTrace tailWord_1297208 prefixEnd_1297208 666091212857665901434255 := by
  unfold tailWord_1297208
  simp only [CollatzResearch.WordTrace]
  refine ⟨23656531342222218166686139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31542041789629624222248185 23656531342222218166686139)
  ·
    refine ⟨35484797013333327250029209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23656531342222218166686139 35484797013333327250029209)
    ·
      refine ⟨26613597759999995437521907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35484797013333327250029209 26613597759999995437521907)
      ·
        refine ⟨39920396639999993156282861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26613597759999995437521907 39920396639999993156282861)
        ·
          refine ⟨14970148739999997433606073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39920396639999993156282861 14970148739999997433606073)
          ·
            refine ⟨11227611554999998075204555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14970148739999997433606073 11227611554999998075204555)
            ·
              refine ⟨16841417332499997112806833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11227611554999998075204555 16841417332499997112806833)
              ·
                refine ⟨12631062999374997834605125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16841417332499997112806833 12631062999374997834605125)
                ·
                  refine ⟨2368324312382812093988461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12631062999374997834605125 2368324312382812093988461)
                  ·
                    refine ⟨888121617143554535245673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2368324312382812093988461 888121617143554535245673)
                    ·
                      refine ⟨666091212857665901434255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 888121617143554535245673 666091212857665901434255)
                      ·
                        rfl

theorem cell23_1297208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 4, 3, 2].length) (baseStart_1297208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297208 prefixEnd_1297208 := by exact prefixLift 1297208
  have htrace : WordTrace (prefixWord ++ tailWord_1297208) baseStart_1297208 baseEnd_1297208 := by
    simpa [prefixWord, tailWord_1297208, baseEnd_1297208] using wordTrace_append hprefix tailTrace_1297208
  have hstable : (prefixWord ++ tailWord_1297208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297208).length < 2 ^ (prefixWord ++ tailWord_1297208).sum := by decide
  have hdescent : baseEnd_1297208 < baseStart_1297208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297225 : List Nat := [1, 2, 1, 1, 2, 6, 2, 1, 2, 3, 2]
def baseStart_1297225 : Nat := 118140960795 + 1297225 * 2 ^ 59
def prefixEnd_1297225 : Nat := 4983230072969 + 3 ^ 40 * 1297225 * 2
def baseEnd_1297225 : Nat := 666099942028792334921677

theorem tailTrace_1297225 : CollatzResearch.WordTrace tailWord_1297225 prefixEnd_1297225 666099942028792334921677 := by
  unfold tailWord_1297225
  simp only [CollatzResearch.WordTrace]
  refine ⟨47313682725382848236741129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31542455150255232157827419 47313682725382848236741129)
  ·
    refine ⟨35485262044037136177555847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47313682725382848236741129 35485262044037136177555847)
    ·
      refine ⟨53227893066055704266333771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35485262044037136177555847 53227893066055704266333771)
      ·
        refine ⟨79841839599083556399500657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53227893066055704266333771 79841839599083556399500657)
        ·
          refine ⟨59881379699312667299625493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79841839599083556399500657 59881379699312667299625493)
          ·
            refine ⟨2806939673405281279669945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 59881379699312667299625493 2806939673405281279669945)
            ·
              refine ⟨2105204755053960959752459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2806939673405281279669945 2105204755053960959752459)
              ·
                refine ⟨3157807132580941439628689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2105204755053960959752459 3157807132580941439628689)
                ·
                  refine ⟨2368355349435706079721517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3157807132580941439628689 2368355349435706079721517)
                  ·
                    refine ⟨888133256038389779895569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2368355349435706079721517 888133256038389779895569)
                    ·
                      refine ⟨666099942028792334921677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 888133256038389779895569 666099942028792334921677)
                      ·
                        rfl

theorem cell23_1297225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 3, 2].length) (baseStart_1297225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297225 prefixEnd_1297225 := by exact prefixLift 1297225
  have htrace : WordTrace (prefixWord ++ tailWord_1297225) baseStart_1297225 baseEnd_1297225 := by
    simpa [prefixWord, tailWord_1297225, baseEnd_1297225] using wordTrace_append hprefix tailTrace_1297225
  have hstable : (prefixWord ++ tailWord_1297225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297225).length < 2 ^ (prefixWord ++ tailWord_1297225).sum := by decide
  have hdescent : baseEnd_1297225 < baseStart_1297225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297289 : List Nat := [1, 2, 1, 1, 5, 3, 2, 3, 1, 2, 2]
def baseStart_1297289 : Nat := 118140960795 + 1297289 * 2 ^ 59
def prefixEnd_1297289 : Nat := 4983230072969 + 3 ^ 40 * 1297289 * 2
def baseEnd_1297289 : Nat := 666132804790680084521383

theorem tailTrace_1297289 : CollatzResearch.WordTrace tailWord_1297289 prefixEnd_1297289 666132804790680084521383 := by
  unfold tailWord_1297289
  simp only [CollatzResearch.WordTrace]
  refine ⟨47316016997150987167070921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31544011331433991444713947 47316016997150987167070921)
  ·
    refine ⟨35487012747863240375303191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47316016997150987167070921 35487012747863240375303191)
    ·
      refine ⟨53230519121794860562954787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35487012747863240375303191 53230519121794860562954787)
      ·
        refine ⟨79845778682692290844432181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53230519121794860562954787 79845778682692290844432181)
        ·
          refine ⟨7485541751502402266665517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79845778682692290844432181 7485541751502402266665517)
          ·
            refine ⟨2807078156813400849999569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7485541751502402266665517 2807078156813400849999569)
            ·
              refine ⟨2105308617610050637499677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2807078156813400849999569 2105308617610050637499677)
              ·
                refine ⟨789490731603768989062379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2105308617610050637499677 789490731603768989062379)
                ·
                  refine ⟨1184236097405653483593569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 789490731603768989062379 1184236097405653483593569)
                  ·
                    refine ⟨888177073054240112695177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1184236097405653483593569 888177073054240112695177)
                    ·
                      refine ⟨666132804790680084521383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 888177073054240112695177 666132804790680084521383)
                      ·
                        rfl

theorem cell23_1297289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 1, 2, 2].length) (baseStart_1297289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297289 prefixEnd_1297289 := by exact prefixLift 1297289
  have htrace : WordTrace (prefixWord ++ tailWord_1297289) baseStart_1297289 baseEnd_1297289 := by
    simpa [prefixWord, tailWord_1297289, baseEnd_1297289] using wordTrace_append hprefix tailTrace_1297289
  have hstable : (prefixWord ++ tailWord_1297289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297289).length < 2 ^ (prefixWord ++ tailWord_1297289).sum := by decide
  have hdescent : baseEnd_1297289 < baseStart_1297289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297321 : List Nat := [1, 2, 1, 1, 1, 1, 5, 3, 2, 6]
def baseStart_1297321 : Nat := 118140960795 + 1297321 * 2 ^ 59
def prefixEnd_1297321 : Nat := 4983230072969 + 3 ^ 40 * 1297321 * 2
def baseEnd_1297321 : Nat := 222049745390541319773745

theorem tailTrace_1297321 : CollatzResearch.WordTrace tailWord_1297321 prefixEnd_1297321 222049745390541319773745 := by
  unfold tailWord_1297321
  simp only [CollatzResearch.WordTrace]
  refine ⟨47317184133035056632235817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31544789422023371088157211 47317184133035056632235817)
  ·
    refine ⟨35487888099776292474176863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47317184133035056632235817 35487888099776292474176863)
    ·
      refine ⟨53231832149664438711265295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35487888099776292474176863 53231832149664438711265295)
      ·
        refine ⟨79847748224496658066897943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53231832149664438711265295 79847748224496658066897943)
        ·
          refine ⟨119771622336744987100346915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79847748224496658066897943 119771622336744987100346915)
          ·
            refine ⟨179657433505117480650520373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119771622336744987100346915 179657433505117480650520373)
            ·
              refine ⟨16842884391104763810986285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 179657433505117480650520373 16842884391104763810986285)
              ·
                refine ⟨6316081646664286429119857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16842884391104763810986285 6316081646664286429119857)
                ·
                  refine ⟨4737061234998214821839893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6316081646664286429119857 4737061234998214821839893)
                  ·
                    refine ⟨222049745390541319773745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4737061234998214821839893 222049745390541319773745)
                    ·
                      rfl

theorem cell23_1297321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 6].length) (baseStart_1297321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297321 prefixEnd_1297321 := by exact prefixLift 1297321
  have htrace : WordTrace (prefixWord ++ tailWord_1297321) baseStart_1297321 baseEnd_1297321 := by
    simpa [prefixWord, tailWord_1297321, baseEnd_1297321] using wordTrace_append hprefix tailTrace_1297321
  have hstable : (prefixWord ++ tailWord_1297321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297321).length < 2 ^ (prefixWord ++ tailWord_1297321).sum := by decide
  have hdescent : baseEnd_1297321 < baseStart_1297321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297351 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 9]
def baseStart_1297351 : Nat := 118140960795 + 1297351 * 2 ^ 59
def prefixEnd_1297351 : Nat := 4983230072969 + 3 ^ 40 * 1297351 * 2
def baseEnd_1297351 : Nat := 74018293399028760216233

theorem tailTrace_1297351 : CollatzResearch.WordTrace tailWord_1297351 prefixEnd_1297351 74018293399028760216233 := by
  unfold tailWord_1297351
  simp only [CollatzResearch.WordTrace]
  refine ⟨47318278322926371755827907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31545518881950914503885271 47318278322926371755827907)
  ·
    refine ⟨70977417484389557633741861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47318278322926371755827907 70977417484389557633741861)
    ·
      refine ⟨13308265778323042056326599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70977417484389557633741861 13308265778323042056326599)
      ·
        refine ⟨19962398667484563084489899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13308265778323042056326599 19962398667484563084489899)
        ·
          refine ⟨29943598001226844626734849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19962398667484563084489899 29943598001226844626734849)
          ·
            refine ⟨22457698500920133470051137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29943598001226844626734849 22457698500920133470051137)
            ·
              refine ⟨16843273875690100102538353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22457698500920133470051137 16843273875690100102538353)
              ·
                refine ⟨12632455406767575076903765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16843273875690100102538353 12632455406767575076903765)
                ·
                  refine ⟨74018293399028760216233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12632455406767575076903765 74018293399028760216233)
                  ·
                    rfl

theorem cell23_1297351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 9].length) (baseStart_1297351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297351 prefixEnd_1297351 := by exact prefixLift 1297351
  have htrace : WordTrace (prefixWord ++ tailWord_1297351) baseStart_1297351 baseEnd_1297351 := by
    simpa [prefixWord, tailWord_1297351, baseEnd_1297351] using wordTrace_append hprefix tailTrace_1297351
  have hstable : (prefixWord ++ tailWord_1297351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297351).length < 2 ^ (prefixWord ++ tailWord_1297351).sum := by decide
  have hdescent : baseEnd_1297351 < baseStart_1297351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297357 : List Nat := [1, 6, 3, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_1297357 : Nat := 118140960795 + 1297357 * 2 ^ 59
def prefixEnd_1297357 : Nat := 4983230072969 + 3 ^ 40 * 1297357 * 2
def baseEnd_1297357 : Nat := 666167721475185818471071

theorem tailTrace_1297357 : CollatzResearch.WordTrace tailWord_1297357 prefixEnd_1297357 666167721475185818471071 := by
  unfold tailWord_1297357
  simp only [CollatzResearch.WordTrace]
  refine ⟨47318497160904634780546325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31545664773936423187030883 47318497160904634780546325)
  ·
    refine ⟨2218054554417404755338109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47318497160904634780546325 2218054554417404755338109)
    ·
      refine ⟨831770457906526783251791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2218054554417404755338109 831770457906526783251791)
      ·
        refine ⟨1247655686859790174877687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 831770457906526783251791 1247655686859790174877687)
        ·
          refine ⟨1871483530289685262316531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1247655686859790174877687 1871483530289685262316531)
          ·
            refine ⟨2807225295434527893474797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1871483530289685262316531 2807225295434527893474797)
            ·
              refine ⟨1052709485787947960053049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2807225295434527893474797 1052709485787947960053049)
              ·
                refine ⟨789532114340960970039787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1052709485787947960053049 789532114340960970039787)
                ·
                  refine ⟨1184298171511441455059681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 789532114340960970039787 1184298171511441455059681)
                  ·
                    refine ⟨888223628633581091294761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1184298171511441455059681 888223628633581091294761)
                    ·
                      refine ⟨666167721475185818471071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 888223628633581091294761 666167721475185818471071)
                      ·
                        rfl

theorem cell23_1297357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_1297357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297357 prefixEnd_1297357 := by exact prefixLift 1297357
  have htrace : WordTrace (prefixWord ++ tailWord_1297357) baseStart_1297357 baseEnd_1297357 := by
    simpa [prefixWord, tailWord_1297357, baseEnd_1297357] using wordTrace_append hprefix tailTrace_1297357
  have hstable : (prefixWord ++ tailWord_1297357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297357).length < 2 ^ (prefixWord ++ tailWord_1297357).sum := by decide
  have hdescent : baseEnd_1297357 < baseStart_1297357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297361 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 1, 2, 7]
def baseStart_1297361 : Nat := 118140960795 + 1297361 * 2 ^ 59
def prefixEnd_1297361 : Nat := 4983230072969 + 3 ^ 40 * 1297361 * 2
def baseEnd_1297361 : Nat := 666169775397803802821051

theorem tailTrace_1297361 : CollatzResearch.WordTrace tailWord_1297361 prefixEnd_1297361 666169775397803802821051 := by
  unfold tailWord_1297361
  simp only [CollatzResearch.WordTrace]
  refine ⟨47318643052890143463691937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31545762035260095642461291 47318643052890143463691937)
  ·
    refine ⟨35488982289667607597768953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47318643052890143463691937 35488982289667607597768953)
    ·
      refine ⟨26616736717250705698326715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35488982289667607597768953 26616736717250705698326715)
      ·
        refine ⟨39925105075876058547490073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26616736717250705698326715 39925105075876058547490073)
        ·
          refine ⟨29943828806907043910617555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39925105075876058547490073 29943828806907043910617555)
          ·
            refine ⟨44915743210360565865926333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29943828806907043910617555 44915743210360565865926333)
            ·
              refine ⟨16843403703885212199722375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44915743210360565865926333 16843403703885212199722375)
              ·
                refine ⟨25265105555827818299583563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16843403703885212199722375 25265105555827818299583563)
                ·
                  refine ⟨37897658333741727449375345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25265105555827818299583563 37897658333741727449375345)
                  ·
                    refine ⟨28423243750306295587031509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37897658333741727449375345 28423243750306295587031509)
                    ·
                      refine ⟨666169775397803802821051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28423243750306295587031509 666169775397803802821051)
                      ·
                        rfl

theorem cell23_1297361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_1297361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297361 prefixEnd_1297361 := by exact prefixLift 1297361
  have htrace : WordTrace (prefixWord ++ tailWord_1297361) baseStart_1297361 baseEnd_1297361 := by
    simpa [prefixWord, tailWord_1297361, baseEnd_1297361] using wordTrace_append hprefix tailTrace_1297361
  have hstable : (prefixWord ++ tailWord_1297361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297361).length < 2 ^ (prefixWord ++ tailWord_1297361).sum := by decide
  have hdescent : baseEnd_1297361 < baseStart_1297361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297368 : List Nat := [2, 1, 2, 2, 2, 3, 3, 1, 7]
def baseStart_1297368 : Nat := 118140960795 + 1297368 * 2 ^ 59
def prefixEnd_1297368 : Nat := 4983230072969 + 3 ^ 40 * 1297368 * 2
def baseEnd_1297368 : Nat := 74019263306931697270391

theorem tailTrace_1297368 : CollatzResearch.WordTrace tailWord_1297368 prefixEnd_1297368 74019263306931697270391 := by
  unfold tailWord_1297368
  simp only [CollatzResearch.WordTrace]
  refine ⟨23659449181932391829598379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31545932242576522439464505 23659449181932391829598379)
  ·
    refine ⟨35489173772898587744397569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23659449181932391829598379 35489173772898587744397569)
    ·
      refine ⟨26616880329673940808298177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35489173772898587744397569 26616880329673940808298177)
      ·
        refine ⟨19962660247255455606223633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26616880329673940808298177 19962660247255455606223633)
        ·
          refine ⟨14971995185441591704667725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19962660247255455606223633 14971995185441591704667725)
          ·
            refine ⟨5614498194540596889250397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14971995185441591704667725 5614498194540596889250397)
            ·
              refine ⟨2105436822952723833468899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5614498194540596889250397 2105436822952723833468899)
              ·
                refine ⟨3158155234429085750203349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2105436822952723833468899 3158155234429085750203349)
                ·
                  refine ⟨74019263306931697270391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3158155234429085750203349 74019263306931697270391)
                  ·
                    rfl

theorem cell23_1297368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 7].length) (baseStart_1297368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297368 prefixEnd_1297368 := by exact prefixLift 1297368
  have htrace : WordTrace (prefixWord ++ tailWord_1297368) baseStart_1297368 baseEnd_1297368 := by
    simpa [prefixWord, tailWord_1297368, baseEnd_1297368] using wordTrace_append hprefix tailTrace_1297368
  have hstable : (prefixWord ++ tailWord_1297368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297368).length < 2 ^ (prefixWord ++ tailWord_1297368).sum := by decide
  have hdescent : baseEnd_1297368 < baseStart_1297368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297445 : List Nat := [1, 3, 1, 2, 2, 2, 3, 2, 3, 4]
def baseStart_1297445 : Nat := 118140960795 + 1297445 * 2 ^ 59
def prefixEnd_1297445 : Nat := 4983230072969 + 3 ^ 40 * 1297445 * 2
def baseEnd_1297445 : Nat := 222070969257593824723555

theorem tailTrace_1297445 : CollatzResearch.WordTrace tailWord_1297445 prefixEnd_1297445 222070969257593824723555 := by
  unfold tailWord_1297445
  simp only [CollatzResearch.WordTrace]
  refine ⟨47321706784585825809749789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31547804523057217206499859 47321706784585825809749789)
  ·
    refine ⟨17745640044219684678656171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47321706784585825809749789 17745640044219684678656171)
    ·
      refine ⟨26618460066329527017984257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17745640044219684678656171 26618460066329527017984257)
      ·
        refine ⟨19963845049747145263488193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26618460066329527017984257 19963845049747145263488193)
        ·
          refine ⟨14972883787310358947616145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19963845049747145263488193 14972883787310358947616145)
          ·
            refine ⟨11229662840482769210712109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14972883787310358947616145 11229662840482769210712109)
            ·
              refine ⟨4211123565181038454017041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11229662840482769210712109 4211123565181038454017041)
              ·
                refine ⟨3158342673885778840512781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4211123565181038454017041 3158342673885778840512781)
                ·
                  refine ⟨1184378502707167065192293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3158342673885778840512781 1184378502707167065192293)
                  ·
                    refine ⟨222070969257593824723555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1184378502707167065192293 222070969257593824723555)
                    ·
                      rfl

theorem cell23_1297445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 4].length) (baseStart_1297445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297445 prefixEnd_1297445 := by exact prefixLift 1297445
  have htrace : WordTrace (prefixWord ++ tailWord_1297445) baseStart_1297445 baseEnd_1297445 := by
    simpa [prefixWord, tailWord_1297445, baseEnd_1297445] using wordTrace_append hprefix tailTrace_1297445
  have hstable : (prefixWord ++ tailWord_1297445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297445).length < 2 ^ (prefixWord ++ tailWord_1297445).sum := by decide
  have hdescent : baseEnd_1297445 < baseStart_1297445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297458 : List Nat := [3, 2, 1, 1, 2, 2, 2, 2, 8]
def baseStart_1297458 : Nat := 118140960795 + 1297458 * 2 ^ 59
def prefixEnd_1297458 : Nat := 4983230072969 + 3 ^ 40 * 1297458 * 2
def baseEnd_1297458 : Nat := 74024398113476658145345

theorem tailTrace_1297458 : CollatzResearch.WordTrace tailWord_1297458 prefixEnd_1297458 74024398113476658145345 := by
  unfold tailWord_1297458
  simp only [CollatzResearch.WordTrace]
  refine ⟨11830545233384682257493257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31548120622359152686648685 11830545233384682257493257)
  ·
    refine ⟨8872908925038511693119943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11830545233384682257493257 8872908925038511693119943)
    ·
      refine ⟨13309363387557767539679915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8872908925038511693119943 13309363387557767539679915)
      ·
        refine ⟨19964045081336651309519873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13309363387557767539679915 19964045081336651309519873)
        ·
          refine ⟨14973033811002488482139905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19964045081336651309519873 14973033811002488482139905)
          ·
            refine ⟨11229775358251866361604929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14973033811002488482139905 11229775358251866361604929)
            ·
              refine ⟨8422331518688899771203697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11229775358251866361604929 8422331518688899771203697)
              ·
                refine ⟨6316748639016674828402773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8422331518688899771203697 6316748639016674828402773)
                ·
                  refine ⟨74024398113476658145345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6316748639016674828402773 74024398113476658145345)
                  ·
                    rfl

theorem cell23_1297458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_1297458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297458 prefixEnd_1297458 := by exact prefixLift 1297458
  have htrace : WordTrace (prefixWord ++ tailWord_1297458) baseStart_1297458 baseEnd_1297458 := by
    simpa [prefixWord, tailWord_1297458, baseEnd_1297458] using wordTrace_append hprefix tailTrace_1297458
  have hstable : (prefixWord ++ tailWord_1297458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297458).length < 2 ^ (prefixWord ++ tailWord_1297458).sum := by decide
  have hdescent : baseEnd_1297458 < baseStart_1297458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297488 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 5, 5]
def baseStart_1297488 : Nat := 118140960795 + 1297488 * 2 ^ 59
def prefixEnd_1297488 : Nat := 4983230072969 + 3 ^ 40 * 1297488 * 2
def baseEnd_1297488 : Nat := 222078329146974935310989

theorem tailTrace_1297488 : CollatzResearch.WordTrace tailWord_1297488 prefixEnd_1297488 222078329146974935310989 := by
  unfold tailWord_1297488
  simp only [CollatzResearch.WordTrace]
  refine ⟨23661637561715022076782559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31548850082286696102376745 23661637561715022076782559)
  ·
    refine ⟨35492456342572533115173839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23661637561715022076782559 35492456342572533115173839)
    ·
      refine ⟨53238684513858799672760759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35492456342572533115173839 53238684513858799672760759)
      ·
        refine ⟨79858026770788199509141139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53238684513858799672760759 79858026770788199509141139)
        ·
          refine ⟨119787040156182299263711709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79858026770788199509141139 119787040156182299263711709)
          ·
            refine ⟨44920140058568362223891891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119787040156182299263711709 44920140058568362223891891)
            ·
              refine ⟨67380210087852543335837837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44920140058568362223891891 67380210087852543335837837)
              ·
                refine ⟨25267578782944703750939189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67380210087852543335837837 25267578782944703750939189)
                ·
                  refine ⟨2368835510901065976650549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25267578782944703750939189 2368835510901065976650549)
                  ·
                    refine ⟨222078329146974935310989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2368835510901065976650549 222078329146974935310989)
                    ·
                      rfl

theorem cell23_1297488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 5, 5].length) (baseStart_1297488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297488 prefixEnd_1297488 := by exact prefixLift 1297488
  have htrace : WordTrace (prefixWord ++ tailWord_1297488) baseStart_1297488 baseEnd_1297488 := by
    simpa [prefixWord, tailWord_1297488, baseEnd_1297488] using wordTrace_append hprefix tailTrace_1297488
  have hstable : (prefixWord ++ tailWord_1297488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297488).length < 2 ^ (prefixWord ++ tailWord_1297488).sum := by decide
  have hdescent : baseEnd_1297488 < baseStart_1297488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297505 : List Nat := [1, 2, 3, 1, 1, 2, 3, 4, 1, 5]
def baseStart_1297505 : Nat := 118140960795 + 1297505 * 2 ^ 59
def prefixEnd_1297505 : Nat := 4983230072969 + 3 ^ 40 * 1297505 * 2
def baseEnd_1297505 : Nat := 222081238870683746473463

theorem tailTrace_1297505 : CollatzResearch.WordTrace tailWord_1297505 prefixEnd_1297505 222081238870683746473463 := by
  unfold tailWord_1297505
  simp only [CollatzResearch.WordTrace]
  refine ⟨47323895164368456056933969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31549263442912304037955979 47323895164368456056933969)
  ·
    refine ⟨35492921373276342042700477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47323895164368456056933969 35492921373276342042700477)
    ·
      refine ⟨13309845514978628266012679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35492921373276342042700477 13309845514978628266012679)
      ·
        refine ⟨19964768272467942399019019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13309845514978628266012679 19964768272467942399019019)
        ·
          refine ⟨29947152408701913598528529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19964768272467942399019019 29947152408701913598528529)
          ·
            refine ⟨22460364306526435198896397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29947152408701913598528529 22460364306526435198896397)
            ·
              refine ⟨8422636614947413199586149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22460364306526435198896397 8422636614947413199586149)
              ·
                refine ⟨1579244365302639974922403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8422636614947413199586149 1579244365302639974922403)
                ·
                  refine ⟨2368866547953959962383605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1579244365302639974922403 2368866547953959962383605)
                  ·
                    refine ⟨222081238870683746473463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2368866547953959962383605 222081238870683746473463)
                    ·
                      rfl

theorem cell23_1297505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_1297505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297505 prefixEnd_1297505 := by exact prefixLift 1297505
  have htrace : WordTrace (prefixWord ++ tailWord_1297505) baseStart_1297505 baseEnd_1297505 := by
    simpa [prefixWord, tailWord_1297505, baseEnd_1297505] using wordTrace_append hprefix tailTrace_1297505
  have hstable : (prefixWord ++ tailWord_1297505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297505).length < 2 ^ (prefixWord ++ tailWord_1297505).sum := by decide
  have hdescent : baseEnd_1297505 < baseStart_1297505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297529 : List Nat := [1, 2, 1, 3, 5, 1, 1, 2, 2, 3, 2]
def baseStart_1297529 : Nat := 118140960795 + 1297529 * 2 ^ 59
def prefixEnd_1297529 : Nat := 4983230072969 + 3 ^ 40 * 1297529 * 2
def baseEnd_1297529 : Nat := 666256040147759145520279

theorem tailTrace_1297529 : CollatzResearch.WordTrace tailWord_1297529 prefixEnd_1297529 666256040147759145520279 := by
  unfold tailWord_1297529
  simp only [CollatzResearch.WordTrace]
  refine ⟨47324770516281508155807641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31549847010854338770538427 47324770516281508155807641)
  ·
    refine ⟨35493577887211131116855731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47324770516281508155807641 35493577887211131116855731)
    ·
      refine ⟨53240366830816696675283597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35493577887211131116855731 53240366830816696675283597)
      ·
        refine ⟨19965137561556261253231349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53240366830816696675283597 19965137561556261253231349)
        ·
          refine ⟨1871731646395899492490439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19965137561556261253231349 1871731646395899492490439)
          ·
            refine ⟨2807597469593849238735659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1871731646395899492490439 2807597469593849238735659)
            ·
              refine ⟨4211396204390773858103489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2807597469593849238735659 4211396204390773858103489)
              ·
                refine ⟨3158547153293080393577617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4211396204390773858103489 3158547153293080393577617)
                ·
                  refine ⟨2368910364969810295183213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3158547153293080393577617 2368910364969810295183213)
                  ·
                    refine ⟨888341386863678860693705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2368910364969810295183213 888341386863678860693705)
                    ·
                      refine ⟨666256040147759145520279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 888341386863678860693705 666256040147759145520279)
                      ·
                        rfl

theorem cell23_1297529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 3, 2].length) (baseStart_1297529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297529 prefixEnd_1297529 := by exact prefixLift 1297529
  have htrace : WordTrace (prefixWord ++ tailWord_1297529) baseStart_1297529 baseEnd_1297529 := by
    simpa [prefixWord, tailWord_1297529, baseEnd_1297529] using wordTrace_append hprefix tailTrace_1297529
  have hstable : (prefixWord ++ tailWord_1297529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297529).length < 2 ^ (prefixWord ++ tailWord_1297529).sum := by decide
  have hdescent : baseEnd_1297529 < baseStart_1297529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297545 : List Nat := [1, 2, 1, 1, 4, 3, 2, 2, 1, 1, 5]
def baseStart_1297545 : Nat := 118140960795 + 1297545 * 2 ^ 59
def prefixEnd_1297545 : Nat := 4983230072969 + 3 ^ 40 * 1297545 * 2
def baseEnd_1297545 : Nat := 666264255838231082920205

theorem tailTrace_1297545 : CollatzResearch.WordTrace tailWord_1297545 prefixEnd_1297545 666264255838231082920205 := by
  unfold tailWord_1297545
  simp only [CollatzResearch.WordTrace]
  refine ⟨47325354084223542888390089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31550236056149028592260059 47325354084223542888390089)
  ·
    refine ⟨35494015563167657166292567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47325354084223542888390089 35494015563167657166292567)
    ·
      refine ⟨53241023344751485749438851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35494015563167657166292567 53241023344751485749438851)
      ·
        refine ⟨79861535017127228624158277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53241023344751485749438851 79861535017127228624158277)
        ·
          refine ⟨14974037815711355367029677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79861535017127228624158277 14974037815711355367029677)
          ·
            refine ⟨5615264180891758262636129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14974037815711355367029677 5615264180891758262636129)
            ·
              refine ⟨4211448135668818696977097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5615264180891758262636129 4211448135668818696977097)
              ·
                refine ⟨3158586101751614022732823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4211448135668818696977097 3158586101751614022732823)
                ·
                  refine ⟨4737879152627421034099235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3158586101751614022732823 4737879152627421034099235)
                  ·
                    refine ⟨7106818728941131551148853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4737879152627421034099235 7106818728941131551148853)
                    ·
                      refine ⟨666264255838231082920205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7106818728941131551148853 666264255838231082920205)
                      ·
                        rfl

theorem cell23_1297545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 1, 5].length) (baseStart_1297545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297545 prefixEnd_1297545 := by exact prefixLift 1297545
  have htrace : WordTrace (prefixWord ++ tailWord_1297545) baseStart_1297545 baseEnd_1297545 := by
    simpa [prefixWord, tailWord_1297545, baseEnd_1297545] using wordTrace_append hprefix tailTrace_1297545
  have hstable : (prefixWord ++ tailWord_1297545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297545).length < 2 ^ (prefixWord ++ tailWord_1297545).sum := by decide
  have hdescent : baseEnd_1297545 < baseStart_1297545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297559 : List Nat := [1, 1, 3, 3, 3, 3, 1, 2, 1, 1, 4]
def baseStart_1297559 : Nat := 118140960795 + 1297559 * 2 ^ 59
def prefixEnd_1297559 : Nat := 4983230072969 + 3 ^ 40 * 1297559 * 2
def baseEnd_1297559 : Nat := 666271444567394028145141

theorem tailTrace_1297559 : CollatzResearch.WordTrace tailWord_1297559 prefixEnd_1297559 666271444567394028145141 := by
  unfold tailWord_1297559
  simp only [CollatzResearch.WordTrace]
  refine ⟨47325864706172823279399731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31550576470781882186266487 47325864706172823279399731)
  ·
    refine ⟨70988797059259234919099597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47325864706172823279399731 70988797059259234919099597)
    ·
      refine ⟨26620798897222213094662349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70988797059259234919099597 26620798897222213094662349)
      ·
        refine ⟨9982799586458329910498381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26620798897222213094662349 9982799586458329910498381)
        ·
          refine ⟨3743549844921873716436893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9982799586458329910498381 3743549844921873716436893)
          ·
            refine ⟨1403831191845702643663835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3743549844921873716436893 1403831191845702643663835)
            ·
              refine ⟨2105746787768553965495753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1403831191845702643663835 2105746787768553965495753)
              ·
                refine ⟨1579310090826415474121815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2105746787768553965495753 1579310090826415474121815)
                ·
                  refine ⟨2368965136239623211182723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1579310090826415474121815 2368965136239623211182723)
                  ·
                    refine ⟨3553447704359434816774085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2368965136239623211182723 3553447704359434816774085)
                    ·
                      refine ⟨666271444567394028145141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3553447704359434816774085 666271444567394028145141)
                      ·
                        rfl

theorem cell23_1297559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_1297559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297559 prefixEnd_1297559 := by exact prefixLift 1297559
  have htrace : WordTrace (prefixWord ++ tailWord_1297559) baseStart_1297559 baseEnd_1297559 := by
    simpa [prefixWord, tailWord_1297559, baseEnd_1297559] using wordTrace_append hprefix tailTrace_1297559
  have hstable : (prefixWord ++ tailWord_1297559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297559).length < 2 ^ (prefixWord ++ tailWord_1297559).sum := by decide
  have hdescent : baseEnd_1297559 < baseStart_1297559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297572 : List Nat := [2, 3, 1, 2, 3, 2, 1, 2, 1, 2, 4]
def baseStart_1297572 : Nat := 118140960795 + 1297572 * 2 ^ 59
def prefixEnd_1297572 : Nat := 4983230072969 + 3 ^ 40 * 1297572 * 2
def baseEnd_1297572 : Nat := 666278119815902477282581

theorem tailTrace_1297572 : CollatzResearch.WordTrace tailWord_1297572 prefixEnd_1297572 666278119815902477282581 := by
  unfold tailWord_1297572
  simp only [CollatzResearch.WordTrace]
  refine ⟨23663169427562863249811485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31550892570083817666415313 23663169427562863249811485)
  ·
    refine ⟨8873688535336073718679307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23663169427562863249811485 8873688535336073718679307)
    ·
      refine ⟨13310532803004110578018961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8873688535336073718679307 13310532803004110578018961)
      ·
        refine ⟨9982899602253082933514221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13310532803004110578018961 9982899602253082933514221)
        ·
          refine ⟨3743587350844906100067833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9982899602253082933514221 3743587350844906100067833)
          ·
            refine ⟨2807690513133679575050875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3743587350844906100067833 2807690513133679575050875)
            ·
              refine ⟨4211535769700519362576313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2807690513133679575050875 4211535769700519362576313)
              ·
                refine ⟨3158651827275389521932235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4211535769700519362576313 3158651827275389521932235)
                ·
                  refine ⟨4737977740913084282898353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3158651827275389521932235 4737977740913084282898353)
                  ·
                    refine ⟨3553483305684813212173765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4737977740913084282898353 3553483305684813212173765)
                    ·
                      refine ⟨666278119815902477282581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3553483305684813212173765 666278119815902477282581)
                      ·
                        rfl

theorem cell23_1297572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_1297572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297572 prefixEnd_1297572 := by exact prefixLift 1297572
  have htrace : WordTrace (prefixWord ++ tailWord_1297572) baseStart_1297572 baseEnd_1297572 := by
    simpa [prefixWord, tailWord_1297572, baseEnd_1297572] using wordTrace_append hprefix tailTrace_1297572
  have hstable : (prefixWord ++ tailWord_1297572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297572).length < 2 ^ (prefixWord ++ tailWord_1297572).sum := by decide
  have hdescent : baseEnd_1297572 < baseStart_1297572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297593 : List Nat := [1, 2, 1, 4, 1, 3, 4, 2, 1, 2, 2]
def baseStart_1297593 : Nat := 118140960795 + 1297593 * 2 ^ 59
def prefixEnd_1297593 : Nat := 4983230072969 + 3 ^ 40 * 1297593 * 2
def baseEnd_1297593 : Nat := 666288902909646895119985

theorem tailTrace_1297593 : CollatzResearch.WordTrace tailWord_1297593 prefixEnd_1297593 666288902909646895119985 := by
  unfold tailWord_1297593
  simp only [CollatzResearch.WordTrace]
  refine ⟨47327104788049647086137433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31551403192033098057424955 47327104788049647086137433)
  ·
    refine ⟨35495328591037235314603075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47327104788049647086137433 35495328591037235314603075)
    ·
      refine ⟨53242992886555852971904613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35495328591037235314603075 53242992886555852971904613)
      ·
        refine ⟨9983061166229222432232115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53242992886555852971904613 9983061166229222432232115)
        ·
          refine ⟨14974591749343833648348173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9983061166229222432232115 14974591749343833648348173)
          ·
            refine ⟨5615471906003937618130565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14974591749343833648348173 5615471906003937618130565)
            ·
              refine ⟨1052900982375738303399481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5615471906003937618130565 1052900982375738303399481)
              ·
                refine ⟨789675736781803727549611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1052900982375738303399481 789675736781803727549611)
                ·
                  refine ⟨1184513605172705591324417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 789675736781803727549611 1184513605172705591324417)
                  ·
                    refine ⟨888385203879529193493313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1184513605172705591324417 888385203879529193493313)
                    ·
                      refine ⟨666288902909646895119985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 888385203879529193493313 666288902909646895119985)
                      ·
                        rfl

theorem cell23_1297593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_1297593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297593 prefixEnd_1297593 := by exact prefixLift 1297593
  have htrace : WordTrace (prefixWord ++ tailWord_1297593) baseStart_1297593 baseEnd_1297593 := by
    simpa [prefixWord, tailWord_1297593, baseEnd_1297593] using wordTrace_append hprefix tailTrace_1297593
  have hstable : (prefixWord ++ tailWord_1297593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297593).length < 2 ^ (prefixWord ++ tailWord_1297593).sum := by decide
  have hdescent : baseEnd_1297593 < baseStart_1297593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297636 : List Nat := [2, 3, 1, 1, 1, 2, 6, 1, 1, 3, 2]
def baseStart_1297636 : Nat := 118140960795 + 1297636 * 2 ^ 59
def prefixEnd_1297636 : Nat := 4983230072969 + 3 ^ 40 * 1297636 * 2
def baseEnd_1297636 : Nat := 666310982577790226882287

theorem tailTrace_1297636 : CollatzResearch.WordTrace tailWord_1297636 prefixEnd_1297636 666310982577790226882287 := by
  unfold tailWord_1297636
  simp only [CollatzResearch.WordTrace]
  refine ⟨23664336563446932714976381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31552448751262576953301841 23664336563446932714976381)
  ·
    refine ⟨8874126211292599768116143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23664336563446932714976381 8874126211292599768116143)
    ·
      refine ⟨13311189316938899652174215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8874126211292599768116143 13311189316938899652174215)
      ·
        refine ⟨19966783975408349478261323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13311189316938899652174215 19966783975408349478261323)
        ·
          refine ⟨29950175963112524217391985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19966783975408349478261323 29950175963112524217391985)
          ·
            refine ⟨22462631972334393163043989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29950175963112524217391985 22462631972334393163043989)
            ·
              refine ⟨1052935873703174679517687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22462631972334393163043989 1052935873703174679517687)
              ·
                refine ⟨1579403810554762019276531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1052935873703174679517687 1579403810554762019276531)
                ·
                  refine ⟨2369105715832143028914797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1579403810554762019276531 2369105715832143028914797)
                  ·
                    refine ⟨888414643437053635843049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2369105715832143028914797 888414643437053635843049)
                    ·
                      refine ⟨666310982577790226882287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 888414643437053635843049 666310982577790226882287)
                      ·
                        rfl

theorem cell23_1297636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 1, 3, 2].length) (baseStart_1297636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297636 prefixEnd_1297636 := by exact prefixLift 1297636
  have htrace : WordTrace (prefixWord ++ tailWord_1297636) baseStart_1297636 baseEnd_1297636 := by
    simpa [prefixWord, tailWord_1297636, baseEnd_1297636] using wordTrace_append hprefix tailTrace_1297636
  have hstable : (prefixWord ++ tailWord_1297636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297636).length < 2 ^ (prefixWord ++ tailWord_1297636).sum := by decide
  have hdescent : baseEnd_1297636 < baseStart_1297636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297722 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4]
def baseStart_1297722 : Nat := 118140960795 + 1297722 * 2 ^ 59
def prefixEnd_1297722 : Nat := 4983230072969 + 3 ^ 40 * 1297722 * 2
def baseEnd_1297722 : Nat := 666355141914076890406891

theorem tailTrace_1297722 : CollatzResearch.WordTrace tailWord_1297722 prefixEnd_1297722 666355141914076890406891 := by
  unfold tailWord_1297722
  simp only [CollatzResearch.WordTrace]
  refine ⟨11832952451145575529395855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31554539869721534745055613 11832952451145575529395855)
  ·
    refine ⟨17749428676718363294093783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11832952451145575529395855 17749428676718363294093783)
    ·
      refine ⟨26624143015077544941140675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17749428676718363294093783 26624143015077544941140675)
      ·
        refine ⟨39936214522616317411711013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26624143015077544941140675 39936214522616317411711013)
        ·
          refine ⟨7488040222990559514695815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39936214522616317411711013 7488040222990559514695815)
          ·
            refine ⟨11232060334485839272043723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7488040222990559514695815 11232060334485839272043723)
            ·
              refine ⟨16848090501728758908065585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11232060334485839272043723 16848090501728758908065585)
              ·
                refine ⟨12636067876296569181049189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16848090501728758908065585 12636067876296569181049189)
                ·
                  refine ⟨2369262726805606721446723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12636067876296569181049189 2369262726805606721446723)
                  ·
                    refine ⟨3553894090208410082170085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2369262726805606721446723 3553894090208410082170085)
                    ·
                      refine ⟨666355141914076890406891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3553894090208410082170085 666355141914076890406891)
                      ·
                        rfl

theorem cell23_1297722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_1297722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297722 prefixEnd_1297722 := by exact prefixLift 1297722
  have htrace : WordTrace (prefixWord ++ tailWord_1297722) baseStart_1297722 baseEnd_1297722 := by
    simpa [prefixWord, tailWord_1297722, baseEnd_1297722] using wordTrace_append hprefix tailTrace_1297722
  have hstable : (prefixWord ++ tailWord_1297722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297722).length < 2 ^ (prefixWord ++ tailWord_1297722).sum := by decide
  have hdescent : baseEnd_1297722 < baseStart_1297722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297757 : List Nat := [1, 4, 5, 1, 1, 2, 2, 2, 5]
def baseStart_1297757 : Nat := 118140960795 + 1297757 * 2 ^ 59
def prefixEnd_1297757 : Nat := 4983230072969 + 3 ^ 40 * 1297757 * 2
def baseEnd_1297757 : Nat := 74041457081887139274359

theorem tailTrace_1297757 : CollatzResearch.WordTrace tailWord_1297757 prefixEnd_1297757 74041457081887139274359 := by
  unfold tailWord_1297757
  simp only [CollatzResearch.WordTrace]
  refine ⟨47333086359455503095107525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31555390906303668730071683 47333086359455503095107525)
  ·
    refine ⟨8874953692397906830332661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47333086359455503095107525 8874953692397906830332661)
    ·
      refine ⟨832026908662303765343687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8874953692397906830332661 832026908662303765343687)
      ·
        refine ⟨1248040362993455648015531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 832026908662303765343687 1248040362993455648015531)
        ·
          refine ⟨1872060544490183472023297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1248040362993455648015531 1872060544490183472023297)
          ·
            refine ⟨1404045408367637604017473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1872060544490183472023297 1404045408367637604017473)
            ·
              refine ⟨1053034056275728203013105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1404045408367637604017473 1053034056275728203013105)
              ·
                refine ⟨789775542206796152259829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1053034056275728203013105 789775542206796152259829)
                ·
                  refine ⟨74041457081887139274359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 789775542206796152259829 74041457081887139274359)
                  ·
                    rfl

theorem cell23_1297757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 5].length) (baseStart_1297757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297757 prefixEnd_1297757 := by exact prefixLift 1297757
  have htrace : WordTrace (prefixWord ++ tailWord_1297757) baseStart_1297757 baseEnd_1297757 := by
    simpa [prefixWord, tailWord_1297757, baseEnd_1297757] using wordTrace_append hprefix tailTrace_1297757
  have hstable : (prefixWord ++ tailWord_1297757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297757).length < 2 ^ (prefixWord ++ tailWord_1297757).sum := by decide
  have hdescent : baseEnd_1297757 < baseStart_1297757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297790 : List Nat := [4, 2, 3, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_1297790 : Nat := 118140960795 + 1297790 * 2 ^ 59
def prefixEnd_1297790 : Nat := 4983230072969 + 3 ^ 40 * 1297790 * 2
def baseEnd_1297790 : Nat := 666390058598582624356579

theorem tailTrace_1297790 : CollatzResearch.WordTrace tailWord_1297790 prefixEnd_1297790 666390058598582624356579 := by
  unfold tailWord_1297790
  simp only [CollatzResearch.WordTrace]
  refine ⟨5916786246041993716382353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31556193312223966487372549 5916786246041993716382353)
  ·
    refine ⟨4437589684531495287286765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5916786246041993716382353 4437589684531495287286765)
    ·
      refine ⟨1664096131699310732732537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4437589684531495287286765 1664096131699310732732537)
      ·
        refine ⟨1248072098774483049549403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1664096131699310732732537 1248072098774483049549403)
        ·
          refine ⟨1872108148161724574324105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1248072098774483049549403 1872108148161724574324105)
          ·
            refine ⟨1404081111121293430743079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1872108148161724574324105 1404081111121293430743079)
            ·
              refine ⟨2106121666681940146114619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1404081111121293430743079 2106121666681940146114619)
              ·
                refine ⟨3159182500022910219171929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2106121666681940146114619 3159182500022910219171929)
                ·
                  refine ⟨2369386875017182664378947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3159182500022910219171929 2369386875017182664378947)
                  ·
                    refine ⟨3554080312525773996568421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2369386875017182664378947 3554080312525773996568421)
                    ·
                      refine ⟨666390058598582624356579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3554080312525773996568421 666390058598582624356579)
                      ·
                        rfl

theorem cell23_1297790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_1297790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297790 prefixEnd_1297790 := by exact prefixLift 1297790
  have htrace : WordTrace (prefixWord ++ tailWord_1297790) baseStart_1297790 baseEnd_1297790 := by
    simpa [prefixWord, tailWord_1297790, baseEnd_1297790] using wordTrace_append hprefix tailTrace_1297790
  have hstable : (prefixWord ++ tailWord_1297790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297790).length < 2 ^ (prefixWord ++ tailWord_1297790).sum := by decide
  have hdescent : baseEnd_1297790 < baseStart_1297790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297793 : List Nat := [1, 2, 4, 3, 2, 2, 1, 1, 2, 2, 3]
def baseStart_1297793 : Nat := 118140960795 + 1297793 * 2 ^ 59
def prefixEnd_1297793 : Nat := 4983230072969 + 3 ^ 40 * 1297793 * 2
def baseEnd_1297793 : Nat := 666391599040546112619065

theorem tailTrace_1297793 : CollatzResearch.WordTrace tailWord_1297793 prefixEnd_1297793 666391599040546112619065 := by
  unfold tailWord_1297793
  simp only [CollatzResearch.WordTrace]
  refine ⟨47334399387325081243418033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31556266258216720828945355 47334399387325081243418033)
  ·
    refine ⟨35500799540493810932563525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47334399387325081243418033 35500799540493810932563525)
    ·
      refine ⟨6656399913842589549855661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35500799540493810932563525 6656399913842589549855661)
      ·
        refine ⟨2496149967690971081195873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6656399913842589549855661 2496149967690971081195873)
        ·
          refine ⟨1872112475768228310896905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2496149967690971081195873 1872112475768228310896905)
          ·
            refine ⟨1404084356826171233172679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1872112475768228310896905 1404084356826171233172679)
            ·
              refine ⟨2106126535239256849759019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1404084356826171233172679 2106126535239256849759019)
              ·
                refine ⟨3159189802858885274638529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2106126535239256849759019 3159189802858885274638529)
                ·
                  refine ⟨2369392352144163955978897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3159189802858885274638529 2369392352144163955978897)
                  ·
                    refine ⟨1777044264108122966984173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2369392352144163955978897 1777044264108122966984173)
                    ·
                      refine ⟨666391599040546112619065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1777044264108122966984173 666391599040546112619065)
                      ·
                        rfl

theorem cell23_1297793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_1297793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297793 prefixEnd_1297793 := by exact prefixLift 1297793
  have htrace : WordTrace (prefixWord ++ tailWord_1297793) baseStart_1297793 baseEnd_1297793 := by
    simpa [prefixWord, tailWord_1297793, baseEnd_1297793] using wordTrace_append hprefix tailTrace_1297793
  have hstable : (prefixWord ++ tailWord_1297793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297793).length < 2 ^ (prefixWord ++ tailWord_1297793).sum := by decide
  have hdescent : baseEnd_1297793 < baseStart_1297793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297823 : List Nat := [1, 1, 2, 5, 1, 2, 2, 4, 1, 1, 3]
def baseStart_1297823 : Nat := 118140960795 + 1297823 * 2 ^ 59
def prefixEnd_1297823 : Nat := 4983230072969 + 3 ^ 40 * 1297823 * 2
def baseEnd_1297823 : Nat := 666407003460180995243927

theorem tailTrace_1297823 : CollatzResearch.WordTrace tailWord_1297823 prefixEnd_1297823 666407003460180995243927 := by
  unfold tailWord_1297823
  simp only [CollatzResearch.WordTrace]
  refine ⟨47335493577216396367010123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31556995718144264244673415 47335493577216396367010123)
  ·
    refine ⟨71003240365824594550515185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47335493577216396367010123 71003240365824594550515185)
    ·
      refine ⟨53252430274368445912886389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71003240365824594550515185 53252430274368445912886389)
      ·
        refine ⟨4992415338222041804333099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53252430274368445912886389 4992415338222041804333099)
        ·
          refine ⟨7488623007333062706499649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4992415338222041804333099 7488623007333062706499649)
          ·
            refine ⟨5616467255499797029874737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7488623007333062706499649 5616467255499797029874737)
            ·
              refine ⟨4212350441624847772406053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5616467255499797029874737 4212350441624847772406053)
              ·
                refine ⟨789815707804658957326135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4212350441624847772406053 789815707804658957326135)
                ·
                  refine ⟨1184723561706988435989203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 789815707804658957326135 1184723561706988435989203)
                  ·
                    refine ⟨1777085342560482653983805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1184723561706988435989203 1777085342560482653983805)
                    ·
                      refine ⟨666407003460180995243927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1777085342560482653983805 666407003460180995243927)
                      ·
                        rfl

theorem cell23_1297823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_1297823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297823 prefixEnd_1297823 := by exact prefixLift 1297823
  have htrace : WordTrace (prefixWord ++ tailWord_1297823) baseStart_1297823 baseEnd_1297823 := by
    simpa [prefixWord, tailWord_1297823, baseEnd_1297823] using wordTrace_append hprefix tailTrace_1297823
  have hstable : (prefixWord ++ tailWord_1297823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297823).length < 2 ^ (prefixWord ++ tailWord_1297823).sum := by decide
  have hdescent : baseEnd_1297823 < baseStart_1297823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297839 : List Nat := [1, 1, 2, 1, 2, 2, 1, 7, 2, 4]
def baseStart_1297839 : Nat := 118140960795 + 1297839 * 2 ^ 59
def prefixEnd_1297839 : Nat := 4983230072969 + 3 ^ 40 * 1297839 * 2
def baseEnd_1297839 : Nat := 222138406383550977547951

theorem tailTrace_1297839 : CollatzResearch.WordTrace tailWord_1297839 prefixEnd_1297839 222138406383550977547951 := by
  unfold tailWord_1297839
  simp only [CollatzResearch.WordTrace]
  refine ⟨47336077145158431099592571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31557384763438954066395047 47336077145158431099592571)
  ·
    refine ⟨71004115717737646649388857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47336077145158431099592571 71004115717737646649388857)
    ·
      refine ⟨53253086788303234987041643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71004115717737646649388857 53253086788303234987041643)
      ·
        refine ⟨79879630182454852480562465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53253086788303234987041643 79879630182454852480562465)
        ·
          refine ⟨59909722636841139360421849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79879630182454852480562465 59909722636841139360421849)
          ·
            refine ⟨44932291977630854520316387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59909722636841139360421849 44932291977630854520316387)
            ·
              refine ⟨67398437966446281780474581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44932291977630854520316387 67398437966446281780474581)
              ·
                refine ⟨1579650889838584729229873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 67398437966446281780474581 1579650889838584729229873)
                ·
                  refine ⟨1184738167378938546922405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1579650889838584729229873 1184738167378938546922405)
                  ·
                    refine ⟨222138406383550977547951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1184738167378938546922405 222138406383550977547951)
                    ·
                      rfl

theorem cell23_1297839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 4].length) (baseStart_1297839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297839 prefixEnd_1297839 := by exact prefixLift 1297839
  have htrace : WordTrace (prefixWord ++ tailWord_1297839) baseStart_1297839 baseEnd_1297839 := by
    simpa [prefixWord, tailWord_1297839, baseEnd_1297839] using wordTrace_append hprefix tailTrace_1297839
  have hstable : (prefixWord ++ tailWord_1297839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297839).length < 2 ^ (prefixWord ++ tailWord_1297839).sum := by decide
  have hdescent : baseEnd_1297839 < baseStart_1297839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297866 : List Nat := [3, 1, 2, 1, 2, 3, 2, 3, 1, 2, 3]
def baseStart_1297866 : Nat := 118140960795 + 1297866 * 2 ^ 59
def prefixEnd_1297866 : Nat := 4983230072969 + 3 ^ 40 * 1297866 * 2
def baseEnd_1297866 : Nat := 666429083128324327006229

theorem tailTrace_1297866 : CollatzResearch.WordTrace tailWord_1297866 prefixEnd_1297866 666429083128324327006229 := by
  unfold tailWord_1297866
  simp only [CollatzResearch.WordTrace]
  refine ⟨11834265479015153677706363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31558041277373743140550301 11834265479015153677706363)
  ·
    refine ⟨17751398218522730516559545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11834265479015153677706363 17751398218522730516559545)
    ·
      refine ⟨13313548663892047887419659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17751398218522730516559545 13313548663892047887419659)
      ·
        refine ⟨19970322995838071831129489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13313548663892047887419659 19970322995838071831129489)
        ·
          refine ⟨14977742246878553873347117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19970322995838071831129489 14977742246878553873347117)
          ·
            refine ⟨5616653342579457702505169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14977742246878553873347117 5616653342579457702505169)
            ·
              refine ⟨4212490006934593276878877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5616653342579457702505169 4212490006934593276878877)
              ·
                refine ⟨1579683752600472478829579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4212490006934593276878877 1579683752600472478829579)
                ·
                  refine ⟨2369525628900708718244369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1579683752600472478829579 2369525628900708718244369)
                  ·
                    refine ⟨1777144221675531538683277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2369525628900708718244369 1777144221675531538683277)
                    ·
                      refine ⟨666429083128324327006229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1777144221675531538683277 666429083128324327006229)
                      ·
                        rfl

theorem cell23_1297866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_1297866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297866 prefixEnd_1297866 := by exact prefixLift 1297866
  have htrace : WordTrace (prefixWord ++ tailWord_1297866) baseStart_1297866 baseEnd_1297866 := by
    simpa [prefixWord, tailWord_1297866, baseEnd_1297866] using wordTrace_append hprefix tailTrace_1297866
  have hstable : (prefixWord ++ tailWord_1297866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297866).length < 2 ^ (prefixWord ++ tailWord_1297866).sum := by decide
  have hdescent : baseEnd_1297866 < baseStart_1297866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297939 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 3]
def baseStart_1297939 : Nat := 118140960795 + 1297939 * 2 ^ 59
def prefixEnd_1297939 : Nat := 4983230072969 + 3 ^ 40 * 1297939 * 2
def baseEnd_1297939 : Nat := 666466567216102541393393

theorem tailTrace_1297939 : CollatzResearch.WordTrace tailWord_1297939 prefixEnd_1297939 666466567216102541393393 := by
  unfold tailWord_1297939
  simp only [CollatzResearch.WordTrace]
  refine ⟨47339724444796148178232871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31559816296530765452155247 47339724444796148178232871)
  ·
    refine ⟨71009586667194222267349307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47339724444796148178232871 71009586667194222267349307)
    ·
      refine ⟨106514380000791333401023961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71009586667194222267349307 106514380000791333401023961)
      ·
        refine ⟨79885785000593500050767971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106514380000791333401023961 79885785000593500050767971)
        ·
          refine ⟨119828677500890250076151957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79885785000593500050767971 119828677500890250076151957)
          ·
            refine ⟨5616969257854230472319623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 119828677500890250076151957 5616969257854230472319623)
            ·
              refine ⟨8425453886781345708479435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5616969257854230472319623 8425453886781345708479435)
              ·
                refine ⟨12638180830172018562719153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8425453886781345708479435 12638180830172018562719153)
                ·
                  refine ⟨9478635622629013922039365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12638180830172018562719153 9478635622629013922039365)
                  ·
                    refine ⟨1777244179242940110382381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9478635622629013922039365 1777244179242940110382381)
                    ·
                      refine ⟨666466567216102541393393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1777244179242940110382381 666466567216102541393393)
                      ·
                        rfl

theorem cell23_1297939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 3].length) (baseStart_1297939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297939 prefixEnd_1297939 := by exact prefixLift 1297939
  have htrace : WordTrace (prefixWord ++ tailWord_1297939) baseStart_1297939 baseEnd_1297939 := by
    simpa [prefixWord, tailWord_1297939, baseEnd_1297939] using wordTrace_append hprefix tailTrace_1297939
  have hstable : (prefixWord ++ tailWord_1297939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297939).length < 2 ^ (prefixWord ++ tailWord_1297939).sum := by decide
  have hdescent : baseEnd_1297939 < baseStart_1297939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297953 : List Nat := [1, 2, 3, 2, 2, 3, 2, 1, 1, 4, 2]
def baseStart_1297953 : Nat := 118140960795 + 1297953 * 2 ^ 59
def prefixEnd_1297953 : Nat := 4983230072969 + 3 ^ 40 * 1297953 * 2
def baseEnd_1297953 : Nat := 666473755945265486618329

theorem tailTrace_1297953 : CollatzResearch.WordTrace tailWord_1297953 prefixEnd_1297953 666473755945265486618329 := by
  unfold tailWord_1297953
  simp only [CollatzResearch.WordTrace]
  refine ⟨47340235066745428569242513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31560156711163619046161675 47340235066745428569242513)
  ·
    refine ⟨35505176300059071426931885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47340235066745428569242513 35505176300059071426931885)
    ·
      refine ⟨13314441112522151785099457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35505176300059071426931885 13314441112522151785099457)
      ·
        refine ⟨9985830834391613838824593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13314441112522151785099457 9985830834391613838824593)
        ·
          refine ⟨7489373125793710379118445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9985830834391613838824593 7489373125793710379118445)
          ·
            refine ⟨2808514922172641392169417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7489373125793710379118445 2808514922172641392169417)
            ·
              refine ⟨2106386191629481044127063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2808514922172641392169417 2106386191629481044127063)
              ·
                refine ⟨3159579287444221566190595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2106386191629481044127063 3159579287444221566190595)
                ·
                  refine ⟨4739368931166332349285893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3159579287444221566190595 4739368931166332349285893)
                  ·
                    refine ⟨888631674593687315491105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4739368931166332349285893 888631674593687315491105)
                    ·
                      refine ⟨666473755945265486618329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 888631674593687315491105 666473755945265486618329)
                      ·
                        rfl

theorem cell23_1297953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_1297953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297953 prefixEnd_1297953 := by exact prefixLift 1297953
  have htrace : WordTrace (prefixWord ++ tailWord_1297953) baseStart_1297953 baseEnd_1297953 := by
    simpa [prefixWord, tailWord_1297953, baseEnd_1297953] using wordTrace_append hprefix tailTrace_1297953
  have hstable : (prefixWord ++ tailWord_1297953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297953).length < 2 ^ (prefixWord ++ tailWord_1297953).sum := by decide
  have hdescent : baseEnd_1297953 < baseStart_1297953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297969 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 3, 5, 3]
def baseStart_1297969 : Nat := 118140960795 + 1297969 * 2 ^ 59
def prefixEnd_1297969 : Nat := 4983230072969 + 3 ^ 40 * 1297969 * 2
def baseEnd_1297969 : Nat := 666481971635737424018255

theorem tailTrace_1297969 : CollatzResearch.WordTrace tailWord_1297969 prefixEnd_1297969 666481971635737424018255 := by
  unfold tailWord_1297969
  simp only [CollatzResearch.WordTrace]
  refine ⟨47340818634687463301824961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31560545756458308867883307 47340818634687463301824961)
  ·
    refine ⟨35505613976015597476368721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47340818634687463301824961 35505613976015597476368721)
    ·
      refine ⟨26629210482011698107276541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35505613976015597476368721 26629210482011698107276541)
      ·
        refine ⟨9985953930754386790228703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26629210482011698107276541 9985953930754386790228703)
        ·
          refine ⟨14978930896131580185343055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9985953930754386790228703 14978930896131580185343055)
          ·
            refine ⟨22468396344197370278014583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14978930896131580185343055 22468396344197370278014583)
            ·
              refine ⟨33702594516296055417021875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22468396344197370278014583 33702594516296055417021875)
              ·
                refine ⟨50553891774444083125532813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33702594516296055417021875 50553891774444083125532813)
                ·
                  refine ⟨18957709415416531172074805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50553891774444083125532813 18957709415416531172074805)
                  ·
                    refine ⟨1777285257695299797382013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18957709415416531172074805 1777285257695299797382013)
                    ·
                      refine ⟨666481971635737424018255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1777285257695299797382013 666481971635737424018255)
                      ·
                        rfl

theorem cell23_1297969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_1297969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297969 prefixEnd_1297969 := by exact prefixLift 1297969
  have htrace : WordTrace (prefixWord ++ tailWord_1297969) baseStart_1297969 baseEnd_1297969 := by
    simpa [prefixWord, tailWord_1297969, baseEnd_1297969] using wordTrace_append hprefix tailTrace_1297969
  have hstable : (prefixWord ++ tailWord_1297969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297969).length < 2 ^ (prefixWord ++ tailWord_1297969).sum := by decide
  have hdescent : baseEnd_1297969 < baseStart_1297969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297974 : List Nat := [5, 1, 2, 1, 3, 2, 2, 1, 1, 3, 2]
def baseStart_1297974 : Nat := 118140960795 + 1297974 * 2 ^ 59
def prefixEnd_1297974 : Nat := 4983230072969 + 3 ^ 40 * 1297974 * 2
def baseEnd_1297974 : Nat := 666484539039009904455733

theorem tailTrace_1297974 : CollatzResearch.WordTrace tailWord_1297974 prefixEnd_1297974 666484539039009904455733 := by
  unfold tailWord_1297974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2958812562479334322234811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31560667333112899437171317 2958812562479334322234811)
  ·
    refine ⟨4438218843719001483352217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2958812562479334322234811 4438218843719001483352217)
    ·
      refine ⟨3328664132789251112514163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4438218843719001483352217 3328664132789251112514163)
      ·
        refine ⟨4992996199183876668771245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3328664132789251112514163 4992996199183876668771245)
        ·
          refine ⟨1872373574693953750789217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4992996199183876668771245 1872373574693953750789217)
          ·
            refine ⟨1404280181020465313091913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1872373574693953750789217 1404280181020465313091913)
            ·
              refine ⟨1053210135765348984818935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1404280181020465313091913 1053210135765348984818935)
              ·
                refine ⟨1579815203648023477228403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1053210135765348984818935 1579815203648023477228403)
                ·
                  refine ⟨2369722805472035215842605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1579815203648023477228403 2369722805472035215842605)
                  ·
                    refine ⟨888646052052013205940977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2369722805472035215842605 888646052052013205940977)
                    ·
                      refine ⟨666484539039009904455733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 888646052052013205940977 666484539039009904455733)
                      ·
                        rfl

theorem cell23_1297974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_1297974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297974 prefixEnd_1297974 := by exact prefixLift 1297974
  have htrace : WordTrace (prefixWord ++ tailWord_1297974) baseStart_1297974 baseEnd_1297974 := by
    simpa [prefixWord, tailWord_1297974, baseEnd_1297974] using wordTrace_append hprefix tailTrace_1297974
  have hstable : (prefixWord ++ tailWord_1297974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297974).length < 2 ^ (prefixWord ++ tailWord_1297974).sum := by decide
  have hdescent : baseEnd_1297974 < baseStart_1297974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297976 : List Nat := [2, 1, 2, 1, 4, 2, 1, 5, 5]
def baseStart_1297976 : Nat := 118140960795 + 1297976 * 2 ^ 59
def prefixEnd_1297976 : Nat := 4983230072969 + 3 ^ 40 * 1297976 * 2
def baseEnd_1297976 : Nat := 74053951777813210736747

theorem tailTrace_1297976 : CollatzResearch.WordTrace tailWord_1297976 prefixEnd_1297976 74053951777813210736747 := by
  unfold tailWord_1297976
  simp only [CollatzResearch.WordTrace]
  refine ⟨23670536972831051748664891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31560715963774735664886521 23670536972831051748664891)
  ·
    refine ⟨35505805459246577622997337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23670536972831051748664891 35505805459246577622997337)
    ·
      refine ⟨26629354094434933217248003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35505805459246577622997337 26629354094434933217248003)
      ·
        refine ⟨39944031141652399825872005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26629354094434933217248003 39944031141652399825872005)
        ·
          refine ⟨7489505839059824967351001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39944031141652399825872005 7489505839059824967351001)
          ·
            refine ⟨5617129379294868725513251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7489505839059824967351001 5617129379294868725513251)
            ·
              refine ⟨8425694068942303088269877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5617129379294868725513251 8425694068942303088269877)
              ·
                refine ⟨789908818963340914525301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8425694068942303088269877 789908818963340914525301)
                ·
                  refine ⟨74053951777813210736747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 789908818963340914525301 74053951777813210736747)
                  ·
                    rfl

theorem cell23_1297976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 5].length) (baseStart_1297976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297976 prefixEnd_1297976 := by exact prefixLift 1297976
  have htrace : WordTrace (prefixWord ++ tailWord_1297976) baseStart_1297976 baseEnd_1297976 := by
    simpa [prefixWord, tailWord_1297976, baseEnd_1297976] using wordTrace_append hprefix tailTrace_1297976
  have hstable : (prefixWord ++ tailWord_1297976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297976).length < 2 ^ (prefixWord ++ tailWord_1297976).sum := by decide
  have hdescent : baseEnd_1297976 < baseStart_1297976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297989 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 4, 5]
def baseStart_1297989 : Nat := 118140960795 + 1297989 * 2 ^ 59
def prefixEnd_1297989 : Nat := 4983230072969 + 3 ^ 40 * 1297989 * 2
def baseEnd_1297989 : Nat := 222164080416275781922721

theorem tailTrace_1297989 : CollatzResearch.WordTrace tailWord_1297989 prefixEnd_1297989 222164080416275781922721 := by
  unfold tailWord_1297989
  simp only [CollatzResearch.WordTrace]
  refine ⟨47341548094615006717553021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31561032063076671145035347 47341548094615006717553021)
  ·
    refine ⟨17753080535480627519082383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47341548094615006717553021 17753080535480627519082383)
    ·
      refine ⟨26629620803220941278623575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17753080535480627519082383 26629620803220941278623575)
      ·
        refine ⟨39944431204831411917935363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26629620803220941278623575 39944431204831411917935363)
        ·
          refine ⟨59916646807247117876903045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39944431204831411917935363 59916646807247117876903045)
          ·
            refine ⟨11234371276358834601919321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59916646807247117876903045 11234371276358834601919321)
            ·
              refine ⟨8425778457269125951439491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11234371276358834601919321 8425778457269125951439491)
              ·
                refine ⟨12638667685903688927159237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8425778457269125951439491 12638667685903688927159237)
                ·
                  refine ⟨2369750191106941673842357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12638667685903688927159237 2369750191106941673842357)
                  ·
                    refine ⟨222164080416275781922721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2369750191106941673842357 222164080416275781922721)
                    ·
                      rfl

theorem cell23_1297989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 5].length) (baseStart_1297989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1297989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1297989 prefixEnd_1297989 := by exact prefixLift 1297989
  have htrace : WordTrace (prefixWord ++ tailWord_1297989) baseStart_1297989 baseEnd_1297989 := by
    simpa [prefixWord, tailWord_1297989, baseEnd_1297989] using wordTrace_append hprefix tailTrace_1297989
  have hstable : (prefixWord ++ tailWord_1297989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297989).length < 2 ^ (prefixWord ++ tailWord_1297989).sum := by decide
  have hdescent : baseEnd_1297989 < baseStart_1297989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298026 : List Nat := [3, 1, 3, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_1298026 : Nat := 118140960795 + 1298026 * 2 ^ 59
def prefixEnd_1298026 : Nat := 4983230072969 + 3 ^ 40 * 1298026 * 2
def baseEnd_1298026 : Nat := 666511240033043701005493

theorem tailTrace_1298026 : CollatzResearch.WordTrace tailWord_1298026 prefixEnd_1298026 666511240033043701005493 := by
  unfold tailWord_1298026
  simp only [CollatzResearch.WordTrace]
  refine ⟨11835724398870240509162483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31561931730320641357766621 11835724398870240509162483)
  ·
    refine ⟨17753586598305360763743725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11835724398870240509162483 17753586598305360763743725)
    ·
      refine ⟨6657594974364510286403897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17753586598305360763743725 6657594974364510286403897)
      ·
        refine ⟨4993196230773382714802923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6657594974364510286403897 4993196230773382714802923)
        ·
          refine ⟨7489794346160074072204385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4993196230773382714802923 7489794346160074072204385)
          ·
            refine ⟨5617345759620055554153289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7489794346160074072204385 5617345759620055554153289)
            ·
              refine ⟨4213009319715041665614967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5617345759620055554153289 4213009319715041665614967)
              ·
                refine ⟨6319513979572562498422451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4213009319715041665614967 6319513979572562498422451)
                ·
                  refine ⟨9479270969358843747633677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6319513979572562498422451 9479270969358843747633677)
                  ·
                    refine ⟨3554726613509566405362629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9479270969358843747633677 3554726613509566405362629)
                    ·
                      refine ⟨666511240033043701005493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3554726613509566405362629 666511240033043701005493)
                      ·
                        rfl

theorem cell23_1298026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_1298026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298026 prefixEnd_1298026 := by exact prefixLift 1298026
  have htrace : WordTrace (prefixWord ++ tailWord_1298026) baseStart_1298026 baseEnd_1298026 := by
    simpa [prefixWord, tailWord_1298026, baseEnd_1298026] using wordTrace_append hprefix tailTrace_1298026
  have hstable : (prefixWord ++ tailWord_1298026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298026).length < 2 ^ (prefixWord ++ tailWord_1298026).sum := by decide
  have hdescent : baseEnd_1298026 < baseStart_1298026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298069 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 1, 2, 6]
def baseStart_1298069 : Nat := 118140960795 + 1298069 * 2 ^ 59
def prefixEnd_1298069 : Nat := 4983230072969 + 3 ^ 40 * 1298069 * 2
def baseEnd_1298069 : Nat := 666533319701187032767795

theorem tailTrace_1298069 : CollatzResearch.WordTrace tailWord_1298069 prefixEnd_1298069 666533319701187032767795 := by
  unfold tailWord_1298069
  simp only [CollatzResearch.WordTrace]
  refine ⟨47344465934325180380465261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31562977289550120253643507 47344465934325180380465261)
  ·
    refine ⟨17754174725371942642674473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47344465934325180380465261 17754174725371942642674473)
    ·
      refine ⟨13315631044028956982005855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17754174725371942642674473 13315631044028956982005855)
      ·
        refine ⟨19973446566043435473008783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13315631044028956982005855 19973446566043435473008783)
        ·
          refine ⟨29960169849065153209513175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19973446566043435473008783 29960169849065153209513175)
          ·
            refine ⟨44940254773597729814269763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29960169849065153209513175 44940254773597729814269763)
            ·
              refine ⟨67410382160396594721404645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44940254773597729814269763 67410382160396594721404645)
              ·
                refine ⟨12639446655074361510263371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67410382160396594721404645 12639446655074361510263371)
                ·
                  refine ⟨18959169982611542265395057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12639446655074361510263371 18959169982611542265395057)
                  ·
                    refine ⟨14219377486958656699046293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18959169982611542265395057 14219377486958656699046293)
                    ·
                      refine ⟨666533319701187032767795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14219377486958656699046293 666533319701187032767795)
                      ·
                        rfl

theorem cell23_1298069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_1298069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298069 prefixEnd_1298069 := by exact prefixLift 1298069
  have htrace : WordTrace (prefixWord ++ tailWord_1298069) baseStart_1298069 baseEnd_1298069 := by
    simpa [prefixWord, tailWord_1298069, baseEnd_1298069] using wordTrace_append hprefix tailTrace_1298069
  have hstable : (prefixWord ++ tailWord_1298069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298069).length < 2 ^ (prefixWord ++ tailWord_1298069).sum := by decide
  have hdescent : baseEnd_1298069 < baseStart_1298069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298096 : List Nat := [2, 1, 1, 1, 2, 1, 4, 5, 1, 5]
def baseStart_1298096 : Nat := 118140960795 + 1298096 * 2 ^ 59
def prefixEnd_1298096 : Nat := 4983230072969 + 3 ^ 40 * 1298096 * 2
def baseEnd_1298096 : Nat := 222182394559619475710057

theorem tailTrace_1298096 : CollatzResearch.WordTrace tailWord_1298096 prefixEnd_1298096 222182394559619475710057 := by
  unfold tailWord_1298096
  simp only [CollatzResearch.WordTrace]
  refine ⟨23672725352613681995849071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31563633803484909327798761 23672725352613681995849071)
  ·
    refine ⟨35509088028920522993773607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23672725352613681995849071 35509088028920522993773607)
    ·
      refine ⟨53263632043380784490660411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35509088028920522993773607 53263632043380784490660411)
      ·
        refine ⟨79895448065071176735990617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53263632043380784490660411 79895448065071176735990617)
        ·
          refine ⟨59921586048803382551992963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79895448065071176735990617 59921586048803382551992963)
          ·
            refine ⟨89882379073205073827989445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59921586048803382551992963 89882379073205073827989445)
            ·
              refine ⟨16852946076225951342748021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89882379073205073827989445 16852946076225951342748021)
              ·
                refine ⟨1579963694646182938382627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16852946076225951342748021 1579963694646182938382627)
                ·
                  refine ⟨2369945541969274407573941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1579963694646182938382627 2369945541969274407573941)
                  ·
                    refine ⟨222182394559619475710057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2369945541969274407573941 222182394559619475710057)
                    ·
                      rfl

theorem cell23_1298096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 1, 5].length) (baseStart_1298096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298096 prefixEnd_1298096 := by exact prefixLift 1298096
  have htrace : WordTrace (prefixWord ++ tailWord_1298096) baseStart_1298096 baseEnd_1298096 := by
    simpa [prefixWord, tailWord_1298096, baseEnd_1298096] using wordTrace_append hprefix tailTrace_1298096
  have hstable : (prefixWord ++ tailWord_1298096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298096).length < 2 ^ (prefixWord ++ tailWord_1298096).sum := by decide
  have hdescent : baseEnd_1298096 < baseStart_1298096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298147 : List Nat := [1, 1, 1, 7, 2, 2, 2, 1, 1, 5]
def baseStart_1298147 : Nat := 118140960795 + 1298147 * 2 ^ 59
def prefixEnd_1298147 : Nat := 4983230072969 + 3 ^ 40 * 1298147 * 2
def baseEnd_1298147 : Nat := 222191123730745909197479

theorem tailTrace_1298147 : CollatzResearch.WordTrace tailWord_1298147 prefixEnd_1298147 222191123730745909197479 := by
  unfold tailWord_1298147
  simp only [CollatzResearch.WordTrace]
  refine ⟨47347310828042599701804695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31564873885361733134536463 47347310828042599701804695)
  ·
    refine ⟨71020966242063899552707043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47347310828042599701804695 71020966242063899552707043)
    ·
      refine ⟨106531449363095849329060565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71020966242063899552707043 106531449363095849329060565)
      ·
        refine ⟨2496830844447558968649857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 106531449363095849329060565 2496830844447558968649857)
        ·
          refine ⟨1872623133335669226487393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2496830844447558968649857 1872623133335669226487393)
          ·
            refine ⟨1404467350001751919865545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1872623133335669226487393 1404467350001751919865545)
            ·
              refine ⟨1053350512501313939899159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1404467350001751919865545 1053350512501313939899159)
              ·
                refine ⟨1580025768751970909848739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1053350512501313939899159 1580025768751970909848739)
                ·
                  refine ⟨2370038653127956364773109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1580025768751970909848739 2370038653127956364773109)
                  ·
                    refine ⟨222191123730745909197479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2370038653127956364773109 222191123730745909197479)
                    ·
                      rfl

theorem cell23_1298147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 1, 5].length) (baseStart_1298147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298147 prefixEnd_1298147 := by exact prefixLift 1298147
  have htrace : WordTrace (prefixWord ++ tailWord_1298147) baseStart_1298147 baseEnd_1298147 := by
    simpa [prefixWord, tailWord_1298147, baseEnd_1298147] using wordTrace_append hprefix tailTrace_1298147
  have hstable : (prefixWord ++ tailWord_1298147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298147).length < 2 ^ (prefixWord ++ tailWord_1298147).sum := by decide
  have hdescent : baseEnd_1298147 < baseStart_1298147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298167 : List Nat := [1, 1, 3, 1, 1, 1, 6, 4, 1, 2, 2]
def baseStart_1298167 : Nat := 118140960795 + 1298167 * 2 ^ 59
def prefixEnd_1298167 : Nat := 4983230072969 + 3 ^ 40 * 1298167 * 2
def baseEnd_1298167 : Nat := 666583640805327649342345

theorem tailTrace_1298167 : CollatzResearch.WordTrace tailWord_1298167 prefixEnd_1298167 666583640805327649342345 := by
  unfold tailWord_1298167
  simp only [CollatzResearch.WordTrace]
  refine ⟨47348040287970143117532755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31565360191980095411688503 47348040287970143117532755)
  ·
    refine ⟨71022060431955214676299133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47348040287970143117532755 71022060431955214676299133)
    ·
      refine ⟨26633272661983205503612175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71022060431955214676299133 26633272661983205503612175)
      ·
        refine ⟨39949908992974808255418263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26633272661983205503612175 39949908992974808255418263)
        ·
          refine ⟨59924863489462212383127395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39949908992974808255418263 59924863489462212383127395)
          ·
            refine ⟨89887295234193318574691093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59924863489462212383127395 89887295234193318574691093)
            ·
              refine ⟨4213466964102811808188645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89887295234193318574691093 4213466964102811808188645)
              ·
                refine ⟨790025055769277214035371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4213466964102811808188645 790025055769277214035371)
                ·
                  refine ⟨1185037583653915821053057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 790025055769277214035371 1185037583653915821053057)
                  ·
                    refine ⟨888778187740436865789793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1185037583653915821053057 888778187740436865789793)
                    ·
                      refine ⟨666583640805327649342345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 888778187740436865789793 666583640805327649342345)
                      ·
                        rfl

theorem cell23_1298167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 1, 2, 2].length) (baseStart_1298167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298167 prefixEnd_1298167 := by exact prefixLift 1298167
  have htrace : WordTrace (prefixWord ++ tailWord_1298167) baseStart_1298167 baseEnd_1298167 := by
    simpa [prefixWord, tailWord_1298167, baseEnd_1298167] using wordTrace_append hprefix tailTrace_1298167
  have hstable : (prefixWord ++ tailWord_1298167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298167).length < 2 ^ (prefixWord ++ tailWord_1298167).sum := by decide
  have hdescent : baseEnd_1298167 < baseStart_1298167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298180 : List Nat := [2, 3, 2, 2, 1, 4, 1, 1, 1, 2, 4]
def baseStart_1298180 : Nat := 118140960795 + 1298180 * 2 ^ 59
def prefixEnd_1298180 : Nat := 4983230072969 + 3 ^ 40 * 1298180 * 2
def baseEnd_1298180 : Nat := 666590316053836098479785

theorem tailTrace_1298180 : CollatzResearch.WordTrace tailWord_1298180 prefixEnd_1298180 666590316053836098479785 := by
  unfold tailWord_1298180
  simp only [CollatzResearch.WordTrace]
  refine ⟨23674257218461523168877997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31565676291282030891837329 23674257218461523168877997)
  ·
    refine ⟨8877846456923071188329249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23674257218461523168877997 8877846456923071188329249)
    ·
      refine ⟨6658384842692303391246937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8877846456923071188329249 6658384842692303391246937)
      ·
        refine ⟨4993788632019227543435203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6658384842692303391246937 4993788632019227543435203)
        ·
          refine ⟨7490682948028841315152805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4993788632019227543435203 7490682948028841315152805)
          ·
            refine ⟨1404503052755407746591151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7490682948028841315152805 1404503052755407746591151)
            ·
              refine ⟨2106754579133111619886727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1404503052755407746591151 2106754579133111619886727)
              ·
                refine ⟨3160131868699667429830091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2106754579133111619886727 3160131868699667429830091)
                ·
                  refine ⟨4740197803049501144745137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3160131868699667429830091 4740197803049501144745137)
                  ·
                    refine ⟨3555148352287125858558853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4740197803049501144745137 3555148352287125858558853)
                    ·
                      refine ⟨666590316053836098479785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3555148352287125858558853 666590316053836098479785)
                      ·
                        rfl

theorem cell23_1298180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_1298180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298180 prefixEnd_1298180 := by exact prefixLift 1298180
  have htrace : WordTrace (prefixWord ++ tailWord_1298180) baseStart_1298180 baseEnd_1298180 := by
    simpa [prefixWord, tailWord_1298180, baseEnd_1298180] using wordTrace_append hprefix tailTrace_1298180
  have hstable : (prefixWord ++ tailWord_1298180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298180).length < 2 ^ (prefixWord ++ tailWord_1298180).sum := by decide
  have hdescent : baseEnd_1298180 < baseStart_1298180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298223 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 3, 4, 2]
def baseStart_1298223 : Nat := 118140960795 + 1298223 * 2 ^ 59
def prefixEnd_1298223 : Nat := 4983230072969 + 3 ^ 40 * 1298223 * 2
def baseEnd_1298223 : Nat := 666612395721979430242087

theorem tailTrace_1298223 : CollatzResearch.WordTrace tailWord_1298223 prefixEnd_1298223 666612395721979430242087 := by
  unfold tailWord_1298223
  simp only [CollatzResearch.WordTrace]
  refine ⟨47350082775767264681571323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31566721850511509787714215 47350082775767264681571323)
  ·
    refine ⟨71025124163650897022356985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47350082775767264681571323 71025124163650897022356985)
    ·
      refine ⟨53268843122738172766767739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71025124163650897022356985 53268843122738172766767739)
      ·
        refine ⟨79903264684107259150151609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53268843122738172766767739 79903264684107259150151609)
        ·
          refine ⟨59927448513080444362613707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79903264684107259150151609 59927448513080444362613707)
          ·
            refine ⟨89891172769620666543920561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59927448513080444362613707 89891172769620666543920561)
            ·
              refine ⟨67418379577215499907940421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89891172769620666543920561 67418379577215499907940421)
              ·
                refine ⟨12640946170727906232738829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67418379577215499907940421 12640946170727906232738829)
                ·
                  refine ⟨4740354814022964837277061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12640946170727906232738829 4740354814022964837277061)
                  ·
                    refine ⟨888816527629305906989449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4740354814022964837277061 888816527629305906989449)
                    ·
                      refine ⟨666612395721979430242087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 888816527629305906989449 666612395721979430242087)
                      ·
                        rfl

theorem cell23_1298223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 4, 2].length) (baseStart_1298223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298223 prefixEnd_1298223 := by exact prefixLift 1298223
  have htrace : WordTrace (prefixWord ++ tailWord_1298223) baseStart_1298223 baseEnd_1298223 := by
    simpa [prefixWord, tailWord_1298223, baseEnd_1298223] using wordTrace_append hprefix tailTrace_1298223
  have hstable : (prefixWord ++ tailWord_1298223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298223).length < 2 ^ (prefixWord ++ tailWord_1298223).sum := by decide
  have hdescent : baseEnd_1298223 < baseStart_1298223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298234 : List Nat := [3, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3]
def baseStart_1298234 : Nat := 118140960795 + 1298234 * 2 ^ 59
def prefixEnd_1298234 : Nat := 4983230072969 + 3 ^ 40 * 1298234 * 2
def baseEnd_1298234 : Nat := 666618044009178887204537

theorem tailTrace_1298234 : CollatzResearch.WordTrace tailWord_1298234 prefixEnd_1298234 666618044009178887204537 := by
  unfold tailWord_1298234
  simp only [CollatzResearch.WordTrace]
  refine ⟨11837620994681853390055439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31566989319151609040147837 11837620994681853390055439)
  ·
    refine ⟨17756431492022780085083159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11837620994681853390055439 17756431492022780085083159)
    ·
      refine ⟨26634647238034170127624739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17756431492022780085083159 26634647238034170127624739)
      ·
        refine ⟨39951970857051255191437109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26634647238034170127624739 39951970857051255191437109)
        ·
          refine ⟨3745497267848555174197229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39951970857051255191437109 3745497267848555174197229)
          ·
            refine ⟨1404561475443208190323961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3745497267848555174197229 1404561475443208190323961)
            ·
              refine ⟨1053421106582406142742971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1404561475443208190323961 1053421106582406142742971)
              ·
                refine ⟨1580131659873609214114457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1053421106582406142742971 1580131659873609214114457)
                ·
                  refine ⟨1185098744905206910585843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1580131659873609214114457 1185098744905206910585843)
                  ·
                    refine ⟨1777648117357810365878765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1185098744905206910585843 1777648117357810365878765)
                    ·
                      refine ⟨666618044009178887204537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1777648117357810365878765 666618044009178887204537)
                      ·
                        rfl

theorem cell23_1298234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3].length) (baseStart_1298234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298234 prefixEnd_1298234 := by exact prefixLift 1298234
  have htrace : WordTrace (prefixWord ++ tailWord_1298234) baseStart_1298234 baseEnd_1298234 := by
    simpa [prefixWord, tailWord_1298234, baseEnd_1298234] using wordTrace_append hprefix tailTrace_1298234
  have hstable : (prefixWord ++ tailWord_1298234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298234).length < 2 ^ (prefixWord ++ tailWord_1298234).sum := by decide
  have hdescent : baseEnd_1298234 < baseStart_1298234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298273 : List Nat := [1, 2, 3, 1, 1, 1, 4, 2, 2, 3, 3]
def baseStart_1298273 : Nat := 118140960795 + 1298273 * 2 ^ 59
def prefixEnd_1298273 : Nat := 4983230072969 + 3 ^ 40 * 1298273 * 2
def baseEnd_1298273 : Nat := 666638069754704234616857

theorem tailTrace_1298273 : CollatzResearch.WordTrace tailWord_1298273 prefixEnd_1298273 666638069754704234616857 := by
  unfold tailWord_1298273
  simp only [CollatzResearch.WordTrace]
  refine ⟨47351906425586123220891473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31567937617057415480594315 47351906425586123220891473)
  ·
    refine ⟨35513929819189592415668605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47351906425586123220891473 35513929819189592415668605)
    ·
      refine ⟨13317723682196097155875727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35513929819189592415668605 13317723682196097155875727)
      ·
        refine ⟨19976585523294145733813591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13317723682196097155875727 19976585523294145733813591)
        ·
          refine ⟨29964878284941218600720387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19976585523294145733813591 29964878284941218600720387)
          ·
            refine ⟨44947317427411827901080581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29964878284941218600720387 44947317427411827901080581)
            ·
              refine ⟨8427622017639717731452609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44947317427411827901080581 8427622017639717731452609)
              ·
                refine ⟨6320716513229788298589457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8427622017639717731452609 6320716513229788298589457)
                ·
                  refine ⟨4740537384922341223942093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6320716513229788298589457 4740537384922341223942093)
                  ·
                    refine ⟨1777701519345877958978285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4740537384922341223942093 1777701519345877958978285)
                    ·
                      refine ⟨666638069754704234616857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1777701519345877958978285 666638069754704234616857)
                      ·
                        rfl

theorem cell23_1298273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_1298273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298273 prefixEnd_1298273 := by exact prefixLift 1298273
  have htrace : WordTrace (prefixWord ++ tailWord_1298273) baseStart_1298273 baseEnd_1298273 := by
    simpa [prefixWord, tailWord_1298273, baseEnd_1298273] using wordTrace_append hprefix tailTrace_1298273
  have hstable : (prefixWord ++ tailWord_1298273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298273).length < 2 ^ (prefixWord ++ tailWord_1298273).sum := by decide
  have hdescent : baseEnd_1298273 < baseStart_1298273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298274 : List Nat := [3, 3, 2, 1, 2, 1, 1, 4, 2, 2, 2]
def baseStart_1298274 : Nat := 118140960795 + 1298274 * 2 ^ 59
def prefixEnd_1298274 : Nat := 4983230072969 + 3 ^ 40 * 1298274 * 2
def baseEnd_1298274 : Nat := 666638583235358730704353

theorem tailTrace_1298274 : CollatzResearch.WordTrace tailWord_1298274 prefixEnd_1298274 666638583235358730704353 := by
  unfold tailWord_1298274
  simp only [CollatzResearch.WordTrace]
  refine ⟨11837985724645625097919469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31567961932388333594451917 11837985724645625097919469)
  ·
    refine ⟨4439244646742109411719801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11837985724645625097919469 4439244646742109411719801)
    ·
      refine ⟨3329433485056582058789851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4439244646742109411719801 3329433485056582058789851)
      ·
        refine ⟨4994150227584873088184777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3329433485056582058789851 4994150227584873088184777)
        ·
          refine ⟨3745612670688654816138583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4994150227584873088184777 3745612670688654816138583)
          ·
            refine ⟨5618419006032982224207875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3745612670688654816138583 5618419006032982224207875)
            ·
              refine ⟨8427628509049473336311813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5618419006032982224207875 8427628509049473336311813)
              ·
                refine ⟨1580180345446776250558465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8427628509049473336311813 1580180345446776250558465)
                ·
                  refine ⟨1185135259085082187918849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1580180345446776250558465 1185135259085082187918849)
                  ·
                    refine ⟨888851444313811640939137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1185135259085082187918849 888851444313811640939137)
                    ·
                      refine ⟨666638583235358730704353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 888851444313811640939137 666638583235358730704353)
                      ·
                        rfl

theorem cell23_1298274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_1298274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298274 prefixEnd_1298274 := by exact prefixLift 1298274
  have htrace : WordTrace (prefixWord ++ tailWord_1298274) baseStart_1298274 baseEnd_1298274 := by
    simpa [prefixWord, tailWord_1298274, baseEnd_1298274] using wordTrace_append hprefix tailTrace_1298274
  have hstable : (prefixWord ++ tailWord_1298274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298274).length < 2 ^ (prefixWord ++ tailWord_1298274).sum := by decide
  have hdescent : baseEnd_1298274 < baseStart_1298274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298280 : List Nat := [2, 1, 4, 2, 1, 1, 3, 4, 5]
def baseStart_1298280 : Nat := 118140960795 + 1298280 * 2 ^ 59
def prefixEnd_1298280 : Nat := 4983230072969 + 3 ^ 40 * 1298280 * 2
def baseEnd_1298280 : Nat := 74071296013253967469925

theorem tailTrace_1298280 : CollatzResearch.WordTrace tailWord_1298280 prefixEnd_1298280 74071296013253967469925 := by
  unfold tailWord_1298280
  simp only [CollatzResearch.WordTrace]
  refine ⟨23676080868280381708198147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31568107824373842277597529 23676080868280381708198147)
  ·
    refine ⟨35514121302420572562297221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23676080868280381708198147 35514121302420572562297221)
    ·
      refine ⟨6658897744203857355430729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35514121302420572562297221 6658897744203857355430729)
      ·
        refine ⟨4994173308152893016573047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6658897744203857355430729 4994173308152893016573047)
        ·
          refine ⟨7491259962229339524859571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4994173308152893016573047 7491259962229339524859571)
          ·
            refine ⟨11236889943344009287289357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7491259962229339524859571 11236889943344009287289357)
            ·
              refine ⟨4213833728754003482733509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11236889943344009287289357 4213833728754003482733509)
              ·
                refine ⟨790093824141375653012533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4213833728754003482733509 790093824141375653012533)
                ·
                  refine ⟨74071296013253967469925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 790093824141375653012533 74071296013253967469925)
                  ·
                    rfl

theorem cell23_1298280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 5].length) (baseStart_1298280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298280 prefixEnd_1298280 := by exact prefixLift 1298280
  have htrace : WordTrace (prefixWord ++ tailWord_1298280) baseStart_1298280 baseEnd_1298280 := by
    simpa [prefixWord, tailWord_1298280, baseEnd_1298280] using wordTrace_append hprefix tailTrace_1298280
  have hstable : (prefixWord ++ tailWord_1298280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298280).length < 2 ^ (prefixWord ++ tailWord_1298280).sum := by decide
  have hdescent : baseEnd_1298280 < baseStart_1298280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298293 : List Nat := [1, 3, 4, 1, 1, 1, 2, 2, 1, 7]
def baseStart_1298293 : Nat := 118140960795 + 1298293 * 2 ^ 59
def prefixEnd_1298293 : Nat := 4983230072969 + 3 ^ 40 * 1298293 * 2
def baseEnd_1298293 : Nat := 222216113122598052122255

theorem tailTrace_1298293 : CollatzResearch.WordTrace tailWord_1298293 prefixEnd_1298293 222216113122598052122255 := by
  unfold tailWord_1298293
  simp only [CollatzResearch.WordTrace]
  refine ⟨47352635885513666636619533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31568423923675777757746355 47352635885513666636619533)
  ·
    refine ⟨17757238457067624988732325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47352635885513666636619533 17757238457067624988732325)
    ·
      refine ⟨3329482210700179685387311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17757238457067624988732325 3329482210700179685387311)
      ·
        refine ⟨4994223316050269528080967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3329482210700179685387311 4994223316050269528080967)
        ·
          refine ⟨7491334974075404292121451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4994223316050269528080967 7491334974075404292121451)
          ·
            refine ⟨11237002461113106438182177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7491334974075404292121451 11237002461113106438182177)
            ·
              refine ⟨8427751845834829828636633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11237002461113106438182177 8427751845834829828636633)
              ·
                refine ⟨6320813884376122371477475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8427751845834829828636633 6320813884376122371477475)
                ·
                  refine ⟨9481220826564183557216213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6320813884376122371477475 9481220826564183557216213)
                  ·
                    refine ⟨222216113122598052122255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9481220826564183557216213 222216113122598052122255)
                    ·
                      rfl

theorem cell23_1298293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_1298293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298293 prefixEnd_1298293 := by exact prefixLift 1298293
  have htrace : WordTrace (prefixWord ++ tailWord_1298293) baseStart_1298293 baseEnd_1298293 := by
    simpa [prefixWord, tailWord_1298293, baseEnd_1298293] using wordTrace_append hprefix tailTrace_1298293
  have hstable : (prefixWord ++ tailWord_1298293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298293).length < 2 ^ (prefixWord ++ tailWord_1298293).sum := by decide
  have hdescent : baseEnd_1298293 < baseStart_1298293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298313 : List Nat := [1, 2, 1, 1, 5, 1, 3, 1, 1, 3, 4]
def baseStart_1298313 : Nat := 118140960795 + 1298313 * 2 ^ 59
def prefixEnd_1298313 : Nat := 4983230072969 + 3 ^ 40 * 1298313 * 2
def baseEnd_1298313 : Nat := 666658608980884078116673

theorem tailTrace_1298313 : CollatzResearch.WordTrace tailWord_1298313 prefixEnd_1298313 666658608980884078116673 := by
  unfold tailWord_1298313
  simp only [CollatzResearch.WordTrace]
  refine ⟨47353365345441210052347593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31568910230294140034898395 47353365345441210052347593)
  ·
    refine ⟨35515024009080907539260695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47353365345441210052347593 35515024009080907539260695)
    ·
      refine ⟨53272536013621361308891043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35515024009080907539260695 53272536013621361308891043)
      ·
        refine ⟨79908804020432041963336565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53272536013621361308891043 79908804020432041963336565)
        ·
          refine ⟨7491450376915503934062803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79908804020432041963336565 7491450376915503934062803)
          ·
            refine ⟨11237175565373255901094205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7491450376915503934062803 11237175565373255901094205)
            ·
              refine ⟨4213940837014970962910327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11237175565373255901094205 4213940837014970962910327)
              ·
                refine ⟨6320911255522456444365491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4213940837014970962910327 6320911255522456444365491)
                ·
                  refine ⟨9481366883283684666548237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6320911255522456444365491 9481366883283684666548237)
                  ·
                    refine ⟨3555512581231381749955589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9481366883283684666548237 3555512581231381749955589)
                    ·
                      refine ⟨666658608980884078116673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3555512581231381749955589 666658608980884078116673)
                      ·
                        rfl

theorem cell23_1298313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 3, 4].length) (baseStart_1298313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298313 prefixEnd_1298313 := by exact prefixLift 1298313
  have htrace : WordTrace (prefixWord ++ tailWord_1298313) baseStart_1298313 baseEnd_1298313 := by
    simpa [prefixWord, tailWord_1298313, baseEnd_1298313] using wordTrace_append hprefix tailTrace_1298313
  have hstable : (prefixWord ++ tailWord_1298313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298313).length < 2 ^ (prefixWord ++ tailWord_1298313).sum := by decide
  have hdescent : baseEnd_1298313 < baseStart_1298313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298340 : List Nat := [2, 3, 1, 2, 1, 3, 1, 3, 3, 4]
def baseStart_1298340 : Nat := 118140960795 + 1298340 * 2 ^ 59
def prefixEnd_1298340 : Nat := 4983230072969 + 3 ^ 40 * 1298340 * 2
def baseEnd_1298340 : Nat := 222224157652851824159683

theorem tailTrace_1298340 : CollatzResearch.WordTrace tailWord_1298340 prefixEnd_1298340 222224157652851824159683 := by
  unfold tailWord_1298340
  simp only [CollatzResearch.WordTrace]
  refine ⟨23677175058171696831790237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31569566744228929109053649 23677175058171696831790237)
  ·
    refine ⟨8878940646814386311921339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23677175058171696831790237 8878940646814386311921339)
    ·
      refine ⟨13318410970221579467882009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8878940646814386311921339 13318410970221579467882009)
      ·
        refine ⟨9988808227666184600911507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13318410970221579467882009 9988808227666184600911507)
        ·
          refine ⟨14983212341499276901367261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9988808227666184600911507 14983212341499276901367261)
          ·
            refine ⟨5618704628062228838012723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14983212341499276901367261 5618704628062228838012723)
            ·
              refine ⟨8428056942093343257019085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5618704628062228838012723 8428056942093343257019085)
              ·
                refine ⟨3160521353285003721382157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8428056942093343257019085 3160521353285003721382157)
                ·
                  refine ⟨1185195507481876395518309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3160521353285003721382157 1185195507481876395518309)
                  ·
                    refine ⟨222224157652851824159683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1185195507481876395518309 222224157652851824159683)
                    ·
                      rfl

theorem cell23_1298340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_1298340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298340 prefixEnd_1298340 := by exact prefixLift 1298340
  have htrace : WordTrace (prefixWord ++ tailWord_1298340) baseStart_1298340 baseEnd_1298340 := by
    simpa [prefixWord, tailWord_1298340, baseEnd_1298340] using wordTrace_append hprefix tailTrace_1298340
  have hstable : (prefixWord ++ tailWord_1298340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298340).length < 2 ^ (prefixWord ++ tailWord_1298340).sum := by decide
  have hdescent : baseEnd_1298340 < baseStart_1298340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298438 : List Nat := [6, 2, 1, 2, 1, 1, 2, 2, 6]
def baseStart_1298438 : Nat := 118140960795 + 1298438 * 2 ^ 59
def prefixEnd_1298438 : Nat := 4983230072969 + 3 ^ 40 * 1298438 * 2
def baseEnd_1298438 : Nat := 74080310451410676561511

theorem tailTrace_1298438 : CollatzResearch.WordTrace tailWord_1298438 prefixEnd_1298438 74080310451410676561511 := by
  unfold tailWord_1298438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1479935139687136137520249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31571949646658904267098645 1479935139687136137520249)
  ·
    refine ⟨1109951354765352103140187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1479935139687136137520249 1109951354765352103140187)
    ·
      refine ⟨1664927032148028154710281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1109951354765352103140187 1664927032148028154710281)
      ·
        refine ⟨1248695274111021116032711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1664927032148028154710281 1248695274111021116032711)
        ·
          refine ⟨1873042911166531674049067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1248695274111021116032711 1873042911166531674049067)
          ·
            refine ⟨2809564366749797511073601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1873042911166531674049067 2809564366749797511073601)
            ·
              refine ⟨2107173275062348133305201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2809564366749797511073601 2107173275062348133305201)
              ·
                refine ⟨1580379956296761099978901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2107173275062348133305201 1580379956296761099978901)
                ·
                  refine ⟨74080310451410676561511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1580379956296761099978901 74080310451410676561511)
                  ·
                    rfl

theorem cell23_1298438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_1298438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298438 prefixEnd_1298438 := by exact prefixLift 1298438
  have htrace : WordTrace (prefixWord ++ tailWord_1298438) baseStart_1298438 baseEnd_1298438 := by
    simpa [prefixWord, tailWord_1298438, baseEnd_1298438] using wordTrace_append hprefix tailTrace_1298438
  have hstable : (prefixWord ++ tailWord_1298438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298438).length < 2 ^ (prefixWord ++ tailWord_1298438).sum := by decide
  have hdescent : baseEnd_1298438 < baseStart_1298438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298460 : List Nat := [2, 2, 3, 1, 3, 1, 3, 8]
def baseStart_1298460 : Nat := 118140960795 + 1298460 * 2 ^ 59
def prefixEnd_1298460 : Nat := 4983230072969 + 3 ^ 40 * 1298460 * 2
def baseEnd_1298460 : Nat := 24693855208781296406611

theorem tailTrace_1298460 : CollatzResearch.WordTrace tailWord_1298460 prefixEnd_1298460 24693855208781296406611 := by
  unfold tailWord_1298460
  simp only [CollatzResearch.WordTrace]
  refine ⟨23679363437954327078974417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31572484583939102771965889 23679363437954327078974417)
  ·
    refine ⟨17759522578465745309230813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23679363437954327078974417 17759522578465745309230813)
    ·
      refine ⟨6659820966924654490961555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17759522578465745309230813 6659820966924654490961555)
      ·
        refine ⟨9989731450386981736442333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6659820966924654490961555 9989731450386981736442333)
        ·
          refine ⟨3746149293895118151165875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9989731450386981736442333 3746149293895118151165875)
          ·
            refine ⟨5619223940842677226748813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3746149293895118151165875 5619223940842677226748813)
            ·
              refine ⟨2107208977816003960030805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5619223940842677226748813 2107208977816003960030805)
              ·
                refine ⟨24693855208781296406611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2107208977816003960030805 24693855208781296406611)
                ·
                  rfl

theorem cell23_1298460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 8].length) (baseStart_1298460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298460 prefixEnd_1298460 := by exact prefixLift 1298460
  have htrace : WordTrace (prefixWord ++ tailWord_1298460) baseStart_1298460 baseEnd_1298460 := by
    simpa [prefixWord, tailWord_1298460, baseEnd_1298460] using wordTrace_append hprefix tailTrace_1298460
  have hstable : (prefixWord ++ tailWord_1298460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298460).length < 2 ^ (prefixWord ++ tailWord_1298460).sum := by decide
  have hdescent : baseEnd_1298460 < baseStart_1298460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298488 : List Nat := [2, 1, 2, 1, 6, 1, 2, 3, 1, 2, 2]
def baseStart_1298488 : Nat := 118140960795 + 1298488 * 2 ^ 59
def prefixEnd_1298488 : Nat := 4983230072969 + 3 ^ 40 * 1298488 * 2
def baseEnd_1298488 : Nat := 666748468095420893428369

theorem tailTrace_1298488 : CollatzResearch.WordTrace tailWord_1298488 prefixEnd_1298488 666748468095420893428369 := by
  unfold tailWord_1298488
  simp only [CollatzResearch.WordTrace]
  refine ⟨23679874059903607469984059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31573165413204809959978745 23679874059903607469984059)
  ·
    refine ⟨35519811089855411204976089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23679874059903607469984059 35519811089855411204976089)
    ·
      refine ⟨26639858317391558403732067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35519811089855411204976089 26639858317391558403732067)
      ·
        refine ⟨39959787476087337605598101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26639858317391558403732067 39959787476087337605598101)
        ·
          refine ⟨1873115037941593950262411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39959787476087337605598101 1873115037941593950262411)
          ·
            refine ⟨2809672556912390925393617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1873115037941593950262411 2809672556912390925393617)
            ·
              refine ⟨2107254417684293194045213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2809672556912390925393617 2107254417684293194045213)
              ·
                refine ⟨790220406631609947766955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2107254417684293194045213 790220406631609947766955)
                ·
                  refine ⟨1185330609947414921650433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 790220406631609947766955 1185330609947414921650433)
                  ·
                    refine ⟨888997957460561191237825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1185330609947414921650433 888997957460561191237825)
                    ·
                      refine ⟨666748468095420893428369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 888997957460561191237825 666748468095420893428369)
                      ·
                        rfl

theorem cell23_1298488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 1, 2, 2].length) (baseStart_1298488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298488 prefixEnd_1298488 := by exact prefixLift 1298488
  have htrace : WordTrace (prefixWord ++ tailWord_1298488) baseStart_1298488 baseEnd_1298488 := by
    simpa [prefixWord, tailWord_1298488, baseEnd_1298488] using wordTrace_append hprefix tailTrace_1298488
  have hstable : (prefixWord ++ tailWord_1298488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298488).length < 2 ^ (prefixWord ++ tailWord_1298488).sum := by decide
  have hdescent : baseEnd_1298488 < baseStart_1298488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298520 : List Nat := [2, 1, 2, 2, 1, 4, 2, 1, 2, 6]
def baseStart_1298520 : Nat := 118140960795 + 1298520 * 2 ^ 59
def prefixEnd_1298520 : Nat := 4983230072969 + 3 ^ 40 * 1298520 * 2
def baseEnd_1298520 : Nat := 222254966492121589409407

theorem tailTrace_1298520 : CollatzResearch.WordTrace tailWord_1298520 prefixEnd_1298520 222254966492121589409407 := by
  unfold tailWord_1298520
  simp only [CollatzResearch.WordTrace]
  refine ⟨23680457627845642202566507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31573943503794189603422009 23680457627845642202566507)
  ·
    refine ⟨35520686441768463303849761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23680457627845642202566507 35520686441768463303849761)
    ·
      refine ⟨26640514831326347477887321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35520686441768463303849761 26640514831326347477887321)
      ·
        refine ⟨19980386123494760608415491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26640514831326347477887321 19980386123494760608415491)
        ·
          refine ⟨29970579185242140912623237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19980386123494760608415491 29970579185242140912623237)
          ·
            refine ⟨5619483597232901421116857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29970579185242140912623237 5619483597232901421116857)
            ·
              refine ⟨4214612697924676065837643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5619483597232901421116857 4214612697924676065837643)
              ·
                refine ⟨6321919046887014098756465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4214612697924676065837643 6321919046887014098756465)
                ·
                  refine ⟨4741439285165260574067349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6321919046887014098756465 4741439285165260574067349)
                  ·
                    refine ⟨222254966492121589409407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4741439285165260574067349 222254966492121589409407)
                    ·
                      rfl

theorem cell23_1298520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_1298520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298520 prefixEnd_1298520 := by exact prefixLift 1298520
  have htrace : WordTrace (prefixWord ++ tailWord_1298520) baseStart_1298520 baseEnd_1298520 := by
    simpa [prefixWord, tailWord_1298520, baseEnd_1298520] using wordTrace_append hprefix tailTrace_1298520
  have hstable : (prefixWord ++ tailWord_1298520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298520).length < 2 ^ (prefixWord ++ tailWord_1298520).sum := by decide
  have hdescent : baseEnd_1298520 < baseStart_1298520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298527 : List Nat := [1, 1, 2, 3, 1, 1, 2, 5, 1, 4, 2]
def baseStart_1298527 : Nat := 118140960795 + 1298527 * 2 ^ 59
def prefixEnd_1298527 : Nat := 4983230072969 + 3 ^ 40 * 1298527 * 2
def baseEnd_1298527 : Nat := 666768493840946240840689

theorem tailTrace_1298527 : CollatzResearch.WordTrace tailWord_1298527 prefixEnd_1298527 666768493840946240840689 := by
  unfold tailWord_1298527
  simp only [CollatzResearch.WordTrace]
  refine ⟨47361170566665924600637835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31574113711110616400425223 47361170566665924600637835)
  ·
    refine ⟨71041755849998886900956753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47361170566665924600637835 71041755849998886900956753)
    ·
      refine ⟨53281316887499165175717565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71041755849998886900956753 53281316887499165175717565)
      ·
        refine ⟨19980493832812186940894087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53281316887499165175717565 19980493832812186940894087)
        ·
          refine ⟨29970740749218280411341131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19980493832812186940894087 29970740749218280411341131)
          ·
            refine ⟨44956111123827420617011697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29970740749218280411341131 44956111123827420617011697)
            ·
              refine ⟨33717083342870565462758773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44956111123827420617011697 33717083342870565462758773)
              ·
                refine ⟨3160976563394115512133635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33717083342870565462758773 3160976563394115512133635)
                ·
                  refine ⟨4741464845091173268200453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3160976563394115512133635 4741464845091173268200453)
                  ·
                    refine ⟨889024658454594987787585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4741464845091173268200453 889024658454594987787585)
                    ·
                      refine ⟨666768493840946240840689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 889024658454594987787585 666768493840946240840689)
                      ·
                        rfl

theorem cell23_1298527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 4, 2].length) (baseStart_1298527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298527 prefixEnd_1298527 := by exact prefixLift 1298527
  have htrace : WordTrace (prefixWord ++ tailWord_1298527) baseStart_1298527 baseEnd_1298527 := by
    simpa [prefixWord, tailWord_1298527, baseEnd_1298527] using wordTrace_append hprefix tailTrace_1298527
  have hstable : (prefixWord ++ tailWord_1298527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298527).length < 2 ^ (prefixWord ++ tailWord_1298527).sum := by decide
  have hdescent : baseEnd_1298527 < baseStart_1298527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298544 : List Nat := [2, 1, 1, 1, 5, 2, 1, 2, 4, 2, 2]
def baseStart_1298544 : Nat := 118140960795 + 1298544 * 2 ^ 59
def prefixEnd_1298544 : Nat := 4983230072969 + 3 ^ 40 * 1298544 * 2
def baseEnd_1298544 : Nat := 666777223012072674328111

theorem tailTrace_1298544 : CollatzResearch.WordTrace tailWord_1298544 prefixEnd_1298544 666777223012072674328111 := by
  unfold tailWord_1298544
  simp only [CollatzResearch.WordTrace]
  refine ⟨23680895303802168252003343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31574527071736224336004457 23680895303802168252003343)
  ·
    refine ⟨35521342955703252378005015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23680895303802168252003343 35521342955703252378005015)
    ·
      refine ⟨53282014433554878567007523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35521342955703252378005015 53282014433554878567007523)
      ·
        refine ⟨79923021650332317850511285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53282014433554878567007523 79923021650332317850511285)
        ·
          refine ⟨7492783279718654798485433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79923021650332317850511285 7492783279718654798485433)
          ·
            refine ⟨5619587459788991098864075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7492783279718654798485433 5619587459788991098864075)
            ·
              refine ⟨8429381189683486648296113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5619587459788991098864075 8429381189683486648296113)
              ·
                refine ⟨6322035892262614986222085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8429381189683486648296113 6322035892262614986222085)
                ·
                  refine ⟨1185381729799240309916641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6322035892262614986222085 1185381729799240309916641)
                  ·
                    refine ⟨889036297349430232437481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1185381729799240309916641 889036297349430232437481)
                    ·
                      refine ⟨666777223012072674328111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 889036297349430232437481 666777223012072674328111)
                      ·
                        rfl

theorem cell23_1298544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 4, 2, 2].length) (baseStart_1298544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298544 prefixEnd_1298544 := by exact prefixLift 1298544
  have htrace : WordTrace (prefixWord ++ tailWord_1298544) baseStart_1298544 baseEnd_1298544 := by
    simpa [prefixWord, tailWord_1298544, baseEnd_1298544] using wordTrace_append hprefix tailTrace_1298544
  have hstable : (prefixWord ++ tailWord_1298544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298544).length < 2 ^ (prefixWord ++ tailWord_1298544).sum := by decide
  have hdescent : baseEnd_1298544 < baseStart_1298544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298567 : List Nat := [1, 1, 4, 2, 1, 1, 2, 6, 5]
def baseStart_1298567 : Nat := 118140960795 + 1298567 * 2 ^ 59
def prefixEnd_1298567 : Nat := 4983230072969 + 3 ^ 40 * 1298567 * 2
def baseEnd_1298567 : Nat := 74087670340791787148945

theorem tailTrace_1298567 : CollatzResearch.WordTrace tailWord_1298567 prefixEnd_1298567 74087670340791787148945 := by
  unfold tailWord_1298567
  simp only [CollatzResearch.WordTrace]
  refine ⟨47362629486521011432093955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31575086324347340954729303 47362629486521011432093955)
  ·
    refine ⟨71043944229781517148140933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47362629486521011432093955 71043944229781517148140933)
    ·
      refine ⟨13320739543084034465276425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71043944229781517148140933 13320739543084034465276425)
      ·
        refine ⟨9990554657313025848957319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13320739543084034465276425 9990554657313025848957319)
        ·
          refine ⟨14985831985969538773435979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9990554657313025848957319 14985831985969538773435979)
          ·
            refine ⟨22478747978954308160153969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14985831985969538773435979 22478747978954308160153969)
            ·
              refine ⟨16859060984215731120115477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22478747978954308160153969 16859060984215731120115477)
              ·
                refine ⟨790268483635112396255413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16859060984215731120115477 790268483635112396255413)
                ·
                  refine ⟨74087670340791787148945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 790268483635112396255413 74087670340791787148945)
                  ·
                    rfl

theorem cell23_1298567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 5].length) (baseStart_1298567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298567 prefixEnd_1298567 := by exact prefixLift 1298567
  have htrace : WordTrace (prefixWord ++ tailWord_1298567) baseStart_1298567 baseEnd_1298567 := by
    simpa [prefixWord, tailWord_1298567, baseEnd_1298567] using wordTrace_append hprefix tailTrace_1298567
  have hstable : (prefixWord ++ tailWord_1298567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298567).length < 2 ^ (prefixWord ++ tailWord_1298567).sum := by decide
  have hdescent : baseEnd_1298567 < baseStart_1298567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298582 : List Nat := [5, 3, 2, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_1298582 : Nat := 118140960795 + 1298582 * 2 ^ 59
def prefixEnd_1298582 : Nat := 4983230072969 + 3 ^ 40 * 1298582 * 2
def baseEnd_1298582 : Nat := 666796735276943525652937

theorem tailTrace_1298582 : CollatzResearch.WordTrace tailWord_1298582 prefixEnd_1298582 666796735276943525652937 := by
  unfold tailWord_1298582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2960198536341666812118125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31575451054311112662593333 2960198536341666812118125)
  ·
    refine ⟨1110074451128125054544297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2960198536341666812118125 1110074451128125054544297)
    ·
      refine ⟨832555838346093790908223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1110074451128125054544297 832555838346093790908223)
      ·
        refine ⟨1248833757519140686362335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 832555838346093790908223 1248833757519140686362335)
        ·
          refine ⟨1873250636278711029543503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1248833757519140686362335 1873250636278711029543503)
          ·
            refine ⟨2809875954418066544315255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1873250636278711029543503 2809875954418066544315255)
            ·
              refine ⟨4214813931627099816472883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2809875954418066544315255 4214813931627099816472883)
              ·
                refine ⟨6322220897440649724709325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4214813931627099816472883 6322220897440649724709325)
                ·
                  refine ⟨2370832836540243646765997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6322220897440649724709325 2370832836540243646765997)
                  ·
                    refine ⟨889062313702591367537249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2370832836540243646765997 889062313702591367537249)
                    ·
                      refine ⟨666796735276943525652937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 889062313702591367537249 666796735276943525652937)
                      ·
                        rfl

theorem cell23_1298582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_1298582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298582 prefixEnd_1298582 := by exact prefixLift 1298582
  have htrace : WordTrace (prefixWord ++ tailWord_1298582) baseStart_1298582 baseEnd_1298582 := by
    simpa [prefixWord, tailWord_1298582, baseEnd_1298582] using wordTrace_append hprefix tailTrace_1298582
  have hstable : (prefixWord ++ tailWord_1298582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298582).length < 2 ^ (prefixWord ++ tailWord_1298582).sum := by decide
  have hdescent : baseEnd_1298582 < baseStart_1298582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298597 : List Nat := [1, 3, 1, 2, 1, 3, 4, 1, 2, 5]
def baseStart_1298597 : Nat := 118140960795 + 1298597 * 2 ^ 59
def prefixEnd_1298597 : Nat := 4983230072969 + 3 ^ 40 * 1298597 * 2
def baseEnd_1298597 : Nat := 222268145828920322321789

theorem tailTrace_1298597 : CollatzResearch.WordTrace tailWord_1298597 prefixEnd_1298597 222268145828920322321789 := by
  unfold tailWord_1298597
  simp only [CollatzResearch.WordTrace]
  refine ⟨47363723676412326555686045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31575815784274884370457363 47363723676412326555686045)
  ·
    refine ⟨17761396378654622458382267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47363723676412326555686045 17761396378654622458382267)
    ·
      refine ⟨26642094567981933687573401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17761396378654622458382267 26642094567981933687573401)
      ·
        refine ⟨19981570925986450265680051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26642094567981933687573401 19981570925986450265680051)
        ·
          refine ⟨29972356388979675398520077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19981570925986450265680051 29972356388979675398520077)
          ·
            refine ⟨11239633645867378274445029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29972356388979675398520077 11239633645867378274445029)
            ·
              refine ⟨2107431308600133426458443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11239633645867378274445029 2107431308600133426458443)
              ·
                refine ⟨3161146962900200139687665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2107431308600133426458443 3161146962900200139687665)
                ·
                  refine ⟨2370860222175150104765749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3161146962900200139687665 2370860222175150104765749)
                  ·
                    refine ⟨222268145828920322321789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2370860222175150104765749 222268145828920322321789)
                    ·
                      rfl

theorem cell23_1298597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 5].length) (baseStart_1298597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298597 prefixEnd_1298597 := by exact prefixLift 1298597
  have htrace : WordTrace (prefixWord ++ tailWord_1298597) baseStart_1298597 baseEnd_1298597 := by
    simpa [prefixWord, tailWord_1298597, baseEnd_1298597] using wordTrace_append hprefix tailTrace_1298597
  have hstable : (prefixWord ++ tailWord_1298597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298597).length < 2 ^ (prefixWord ++ tailWord_1298597).sum := by decide
  have hdescent : baseEnd_1298597 < baseStart_1298597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298617 : List Nat := [1, 2, 1, 4, 1, 2, 1, 4, 2, 1, 4]
def baseStart_1298617 : Nat := 118140960795 + 1298617 * 2 ^ 59
def prefixEnd_1298617 : Nat := 4983230072969 + 3 ^ 40 * 1298617 * 2
def baseEnd_1298617 : Nat := 666814707099850888715275

theorem tailTrace_1298617 : CollatzResearch.WordTrace tailWord_1298617 prefixEnd_1298617 666814707099850888715275 := by
  unfold tailWord_1298617
  simp only [CollatzResearch.WordTrace]
  refine ⟨47364453136339869971414105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31576302090893246647609403 47364453136339869971414105)
  ·
    refine ⟨35523339852254902478560579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47364453136339869971414105 35523339852254902478560579)
    ·
      refine ⟨53285009778382353717840869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35523339852254902478560579 53285009778382353717840869)
      ·
        refine ⟨9990939333446691322095163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53285009778382353717840869 9990939333446691322095163)
        ·
          refine ⟨14986409000170036983142745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9990939333446691322095163 14986409000170036983142745)
          ·
            refine ⟨11239806750127527737357059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14986409000170036983142745 11239806750127527737357059)
            ·
              refine ⟨16859710125191291606035589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11239806750127527737357059 16859710125191291606035589)
              ·
                refine ⟨3161195648473367176131673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16859710125191291606035589 3161195648473367176131673)
                ·
                  refine ⟨2370896736355025382098755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3161195648473367176131673 2370896736355025382098755)
                  ·
                    refine ⟨3556345104532538073148133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2370896736355025382098755 3556345104532538073148133)
                    ·
                      refine ⟨666814707099850888715275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3556345104532538073148133 666814707099850888715275)
                      ·
                        rfl

theorem cell23_1298617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_1298617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298617 prefixEnd_1298617 := by exact prefixLift 1298617
  have htrace : WordTrace (prefixWord ++ tailWord_1298617) baseStart_1298617 baseEnd_1298617 := by
    simpa [prefixWord, tailWord_1298617, baseEnd_1298617] using wordTrace_append hprefix tailTrace_1298617
  have hstable : (prefixWord ++ tailWord_1298617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298617).length < 2 ^ (prefixWord ++ tailWord_1298617).sum := by decide
  have hdescent : baseEnd_1298617 < baseStart_1298617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298634 : List Nat := [3, 1, 2, 1, 3, 1, 3, 1, 2, 4, 2]
def baseStart_1298634 : Nat := 118140960795 + 1298634 * 2 ^ 59
def prefixEnd_1298634 : Nat := 4983230072969 + 3 ^ 40 * 1298634 * 2
def baseEnd_1298634 : Nat := 666823436270977322202697

theorem tailTrace_1298634 : CollatzResearch.WordTrace tailWord_1298634 prefixEnd_1298634 666823436270977322202697 := by
  unfold tailWord_1298634
  simp only [CollatzResearch.WordTrace]
  refine ⟨11841268294319570468695739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31576715451518854583188637 11841268294319570468695739)
  ·
    refine ⟨17761902441479355703043609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11841268294319570468695739 17761902441479355703043609)
    ·
      refine ⟨13321426831109516777282707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17761902441479355703043609 13321426831109516777282707)
      ·
        refine ⟨19982140246664275165924061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13321426831109516777282707 19982140246664275165924061)
        ·
          refine ⟨7493302592499103187221523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19982140246664275165924061 7493302592499103187221523)
          ·
            refine ⟨11239953888748654780832285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7493302592499103187221523 11239953888748654780832285)
            ·
              refine ⟨4214982708280745542812107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11239953888748654780832285 4214982708280745542812107)
              ·
                refine ⟨6322474062421118314218161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4214982708280745542812107 6322474062421118314218161)
                ·
                  refine ⟨4741855546815838735663621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6322474062421118314218161 4741855546815838735663621)
                  ·
                    refine ⟨889097915027969762936929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4741855546815838735663621 889097915027969762936929)
                    ·
                      refine ⟨666823436270977322202697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 889097915027969762936929 666823436270977322202697)
                      ·
                        rfl

theorem cell23_1298634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 2, 4, 2].length) (baseStart_1298634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298634 prefixEnd_1298634 := by exact prefixLift 1298634
  have htrace : WordTrace (prefixWord ++ tailWord_1298634) baseStart_1298634 baseEnd_1298634 := by
    simpa [prefixWord, tailWord_1298634, baseEnd_1298634] using wordTrace_append hprefix tailTrace_1298634
  have hstable : (prefixWord ++ tailWord_1298634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298634).length < 2 ^ (prefixWord ++ tailWord_1298634).sum := by decide
  have hdescent : baseEnd_1298634 < baseStart_1298634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298661 : List Nat := [1, 3, 1, 4, 2, 1, 1, 5, 1, 4]
def baseStart_1298661 : Nat := 118140960795 + 1298661 * 2 ^ 59
def prefixEnd_1298661 : Nat := 4983230072969 + 3 ^ 40 * 1298661 * 2
def baseEnd_1298661 : Nat := 222279100082882905521691

theorem tailTrace_1298661 : CollatzResearch.WordTrace tailWord_1298661 prefixEnd_1298661 222279100082882905521691 := by
  unfold tailWord_1298661
  simp only [CollatzResearch.WordTrace]
  refine ⟨47366057948180465486015837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31577371965453643657343891 47366057948180465486015837)
  ·
    refine ⟨17762271730567674557255939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47366057948180465486015837 17762271730567674557255939)
    ·
      refine ⟨26643407595851511835883909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17762271730567674557255939 26643407595851511835883909)
      ·
        refine ⟨4995638924222158469228233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26643407595851511835883909 4995638924222158469228233)
        ·
          refine ⟨3746729193166618851921175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4995638924222158469228233 3746729193166618851921175)
          ·
            refine ⟨5620093789749928277881763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3746729193166618851921175 5620093789749928277881763)
            ·
              refine ⟨8430140684624892416822645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5620093789749928277881763 8430140684624892416822645)
              ·
                refine ⟨790325689183583664077123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8430140684624892416822645 790325689183583664077123)
                ·
                  refine ⟨1185488533775375496115685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 790325689183583664077123 1185488533775375496115685)
                  ·
                    refine ⟨222279100082882905521691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1185488533775375496115685 222279100082882905521691)
                    ·
                      rfl

theorem cell23_1298661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 1, 4].length) (baseStart_1298661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298661 prefixEnd_1298661 := by exact prefixLift 1298661
  have htrace : WordTrace (prefixWord ++ tailWord_1298661) baseStart_1298661 baseEnd_1298661 := by
    simpa [prefixWord, tailWord_1298661, baseEnd_1298661] using wordTrace_append hprefix tailTrace_1298661
  have hstable : (prefixWord ++ tailWord_1298661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298661).length < 2 ^ (prefixWord ++ tailWord_1298661).sum := by decide
  have hdescent : baseEnd_1298661 < baseStart_1298661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298674 : List Nat := [3, 2, 1, 3, 2, 1, 3, 2, 6]
def baseStart_1298674 : Nat := 118140960795 + 1298674 * 2 ^ 59
def prefixEnd_1298674 : Nat := 4983230072969 + 3 ^ 40 * 1298674 * 2
def baseEnd_1298674 : Nat := 74093775055239685078057

theorem tailTrace_1298674 : CollatzResearch.WordTrace tailWord_1298674 prefixEnd_1298674 74093775055239685078057 := by
  unfold tailWord_1298674
  simp only [CollatzResearch.WordTrace]
  refine ⟨11841633024283342176559769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31577688064755579137492717 11841633024283342176559769)
  ·
    refine ⟨8881224768212506632419827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11841633024283342176559769 8881224768212506632419827)
    ·
      refine ⟨13321837152318759948629741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8881224768212506632419827 13321837152318759948629741)
      ·
        refine ⟨4995688932119534980736153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13321837152318759948629741 4995688932119534980736153)
        ·
          refine ⟨3746766699089651235552115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4995688932119534980736153 3746766699089651235552115)
          ·
            refine ⟨5620150048634476853328173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3746766699089651235552115 5620150048634476853328173)
            ·
              refine ⟨2107556268237928819998065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5620150048634476853328173 2107556268237928819998065)
              ·
                refine ⟨1580667201178446614998549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2107556268237928819998065 1580667201178446614998549)
                ·
                  refine ⟨74093775055239685078057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1580667201178446614998549 74093775055239685078057)
                  ·
                    rfl

theorem cell23_1298674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_1298674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298674 prefixEnd_1298674 := by exact prefixLift 1298674
  have htrace : WordTrace (prefixWord ++ tailWord_1298674) baseStart_1298674 baseEnd_1298674 := by
    simpa [prefixWord, tailWord_1298674, baseEnd_1298674] using wordTrace_append hprefix tailTrace_1298674
  have hstable : (prefixWord ++ tailWord_1298674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298674).length < 2 ^ (prefixWord ++ tailWord_1298674).sum := by decide
  have hdescent : baseEnd_1298674 < baseStart_1298674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298707 : List Nat := [1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 4]
def baseStart_1298707 : Nat := 118140960795 + 1298707 * 2 ^ 59
def prefixEnd_1298707 : Nat := 4983230072969 + 3 ^ 40 * 1298707 * 2
def baseEnd_1298707 : Nat := 666860920358755536589861

theorem tailTrace_1298707 : CollatzResearch.WordTrace tailWord_1298707 prefixEnd_1298707 666860920358755536589861 := by
  unfold tailWord_1298707
  simp only [CollatzResearch.WordTrace]
  refine ⟨47367735706013815342190375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31578490470675876894793583 47367735706013815342190375)
  ·
    refine ⟨71051603559020723013285563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47367735706013815342190375 71051603559020723013285563)
    ·
      refine ⟨106577405338531084519928345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71051603559020723013285563 106577405338531084519928345)
      ·
        refine ⟨79933054003898313389946259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106577405338531084519928345 79933054003898313389946259)
        ·
          refine ⟨119899581005847470084919389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79933054003898313389946259 119899581005847470084919389)
          ·
            refine ⟨44962342877192801281844771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119899581005847470084919389 44962342877192801281844771)
            ·
              refine ⟨67443514315789201922767157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44962342877192801281844771 67443514315789201922767157)
              ·
                refine ⟨6322829467105237680259421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67443514315789201922767157 6322829467105237680259421)
                ·
                  refine ⟨2371061050164464130097283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6322829467105237680259421 2371061050164464130097283)
                  ·
                    refine ⟨3556591575246696195145925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2371061050164464130097283 3556591575246696195145925)
                    ·
                      refine ⟨666860920358755536589861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3556591575246696195145925 666860920358755536589861)
                      ·
                        rfl

theorem cell23_1298707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 4].length) (baseStart_1298707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298707 prefixEnd_1298707 := by exact prefixLift 1298707
  have htrace : WordTrace (prefixWord ++ tailWord_1298707) baseStart_1298707 baseEnd_1298707 := by
    simpa [prefixWord, tailWord_1298707, baseEnd_1298707] using wordTrace_append hprefix tailTrace_1298707
  have hstable : (prefixWord ++ tailWord_1298707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298707).length < 2 ^ (prefixWord ++ tailWord_1298707).sum := by decide
  have hdescent : baseEnd_1298707 < baseStart_1298707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298728 : List Nat := [2, 1, 5, 1, 3, 1, 1, 2, 2, 3, 2]
def baseStart_1298728 : Nat := 118140960795 + 1298728 * 2 ^ 59
def prefixEnd_1298728 : Nat := 4983230072969 + 3 ^ 40 * 1298728 * 2
def baseEnd_1298728 : Nat := 666871703452499954427265

theorem tailTrace_1298728 : CollatzResearch.WordTrace tailWord_1298728 prefixEnd_1298728 666871703452499954427265 := by
  unfold tailWord_1298728
  simp only [CollatzResearch.WordTrace]
  refine ⟨23684250819468867964352419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31579001092625157285803225 23684250819468867964352419)
  ·
    refine ⟨35526376229203301946528629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23684250819468867964352419 35526376229203301946528629)
    ·
      refine ⟨3330597771487809557487059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35526376229203301946528629 3330597771487809557487059)
      ·
        refine ⟨4995896657231714336230589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3330597771487809557487059 4995896657231714336230589)
        ·
          refine ⟨1873461246461892876086471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4995896657231714336230589 1873461246461892876086471)
          ·
            refine ⟨2810191869692839314129707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1873461246461892876086471 2810191869692839314129707)
            ·
              refine ⟨4215287804539258971194561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2810191869692839314129707 4215287804539258971194561)
              ·
                refine ⟨3161465853404444228395921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4215287804539258971194561 3161465853404444228395921)
                ·
                  refine ⟨2371099390053333171296941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3161465853404444228395921 2371099390053333171296941)
                  ·
                    refine ⟨889162271269999939236353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2371099390053333171296941 889162271269999939236353)
                    ·
                      refine ⟨666871703452499954427265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 889162271269999939236353 666871703452499954427265)
                      ·
                        rfl

theorem cell23_1298728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_1298728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298728 prefixEnd_1298728 := by exact prefixLift 1298728
  have htrace : WordTrace (prefixWord ++ tailWord_1298728) baseStart_1298728 baseEnd_1298728 := by
    simpa [prefixWord, tailWord_1298728, baseEnd_1298728] using wordTrace_append hprefix tailTrace_1298728
  have hstable : (prefixWord ++ tailWord_1298728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298728).length < 2 ^ (prefixWord ++ tailWord_1298728).sum := by decide
  have hdescent : baseEnd_1298728 < baseStart_1298728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298792 : List Nat := [2, 1, 4, 2, 2, 1, 4, 2, 1, 2, 2]
def baseStart_1298792 : Nat := 118140960795 + 1298792 * 2 ^ 59
def prefixEnd_1298792 : Nat := 4983230072969 + 3 ^ 40 * 1298792 * 2
def baseEnd_1298792 : Nat := 666904566214387704026971

theorem tailTrace_1298792 : CollatzResearch.WordTrace tailWord_1298792 prefixEnd_1298792 666904566214387704026971 := by
  unfold tailWord_1298792
  simp only [CollatzResearch.WordTrace]
  refine ⟨23685417955352937429517315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31580557273803916572689753 23685417955352937429517315)
  ·
    refine ⟨35528126933029406144275973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23685417955352937429517315 35528126933029406144275973)
    ·
      refine ⟨6661523799943013652051745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35528126933029406144275973 6661523799943013652051745)
      ·
        refine ⟨4996142849957260239038809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6661523799943013652051745 4996142849957260239038809)
        ·
          refine ⟨3747107137467945179279107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4996142849957260239038809 3747107137467945179279107)
          ·
            refine ⟨5620660706201917768918661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3747107137467945179279107 5620660706201917768918661)
            ·
              refine ⟨1053873882412859581672249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5620660706201917768918661 1053873882412859581672249)
              ·
                refine ⟨790405411809644686254187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1053873882412859581672249 790405411809644686254187)
                ·
                  refine ⟨1185608117714467029381281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 790405411809644686254187 1185608117714467029381281)
                  ·
                    refine ⟨889206088285850272035961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1185608117714467029381281 889206088285850272035961)
                    ·
                      refine ⟨666904566214387704026971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 889206088285850272035961 666904566214387704026971)
                      ·
                        rfl

theorem cell23_1298792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_1298792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298792 prefixEnd_1298792 := by exact prefixLift 1298792
  have htrace : WordTrace (prefixWord ++ tailWord_1298792) baseStart_1298792 baseEnd_1298792 := by
    simpa [prefixWord, tailWord_1298792, baseEnd_1298792] using wordTrace_append hprefix tailTrace_1298792
  have hstable : (prefixWord ++ tailWord_1298792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298792).length < 2 ^ (prefixWord ++ tailWord_1298792).sum := by decide
  have hdescent : baseEnd_1298792 < baseStart_1298792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298794 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 2, 7]
def baseStart_1298794 : Nat := 118140960795 + 1298794 * 2 ^ 59
def prefixEnd_1298794 : Nat := 4983230072969 + 3 ^ 40 * 1298794 * 2
def baseEnd_1298794 : Nat := 222301864391898898733987

theorem tailTrace_1298794 : CollatzResearch.WordTrace tailWord_1298794 prefixEnd_1298794 222301864391898898733987 := by
  unfold tailWord_1298794
  simp only [CollatzResearch.WordTrace]
  refine ⟨11842727214174657300151859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31580605904465752800404957 11842727214174657300151859)
  ·
    refine ⟨17764090821261985950227789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11842727214174657300151859 17764090821261985950227789)
    ·
      refine ⟨6661534057973244731335421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17764090821261985950227789 6661534057973244731335421)
      ·
        refine ⟨2498075271739966774250783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6661534057973244731335421 2498075271739966774250783)
        ·
          refine ⟨3747112907609950161376175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2498075271739966774250783 3747112907609950161376175)
          ·
            refine ⟨5620669361414925242064263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3747112907609950161376175 5620669361414925242064263)
            ·
              refine ⟨8431004042122387863096395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5620669361414925242064263 8431004042122387863096395)
              ·
                refine ⟨12646506063183581794644593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8431004042122387863096395 12646506063183581794644593)
                ·
                  refine ⟨9484879547387686345983445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12646506063183581794644593 9484879547387686345983445)
                  ·
                    refine ⟨222301864391898898733987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9484879547387686345983445 222301864391898898733987)
                    ·
                      rfl

theorem cell23_1298794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_1298794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298794 prefixEnd_1298794 := by exact prefixLift 1298794
  have htrace : WordTrace (prefixWord ++ tailWord_1298794) baseStart_1298794 baseEnd_1298794 := by
    simpa [prefixWord, tailWord_1298794, baseEnd_1298794] using wordTrace_append hprefix tailTrace_1298794
  have hstable : (prefixWord ++ tailWord_1298794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298794).length < 2 ^ (prefixWord ++ tailWord_1298794).sum := by decide
  have hdescent : baseEnd_1298794 < baseStart_1298794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298837 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 11]
def baseStart_1298837 : Nat := 118140960795 + 1298837 * 2 ^ 59
def prefixEnd_1298837 : Nat := 4983230072969 + 3 ^ 40 * 1298837 * 2
def baseEnd_1298837 : Nat := 74103074760426669773807

theorem tailTrace_1298837 : CollatzResearch.WordTrace tailWord_1298837 prefixEnd_1298837 74103074760426669773807 := by
  unfold tailWord_1298837
  simp only [CollatzResearch.WordTrace]
  refine ⟨47372477195542847544422765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31581651463695231696281843 47372477195542847544422765)
  ·
    refine ⟨17764678948328567829158537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47372477195542847544422765 17764678948328567829158537)
    ·
      refine ⟨13323509211246425871868903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17764678948328567829158537 13323509211246425871868903)
      ·
        refine ⟨19985263816869638807803355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13323509211246425871868903 19985263816869638807803355)
        ·
          refine ⟨29977895725304458211705033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19985263816869638807803355 29977895725304458211705033)
          ·
            refine ⟨22483421793978343658778775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29977895725304458211705033 22483421793978343658778775)
            ·
              refine ⟨33725132690967515488168163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22483421793978343658778775 33725132690967515488168163)
              ·
                refine ⟨50587699036451273232252245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33725132690967515488168163 50587699036451273232252245)
                ·
                  refine ⟨74103074760426669773807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 50587699036451273232252245 74103074760426669773807)
                  ·
                    rfl

theorem cell23_1298837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 11].length) (baseStart_1298837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298837 prefixEnd_1298837 := by exact prefixLift 1298837
  have htrace : WordTrace (prefixWord ++ tailWord_1298837) baseStart_1298837 baseEnd_1298837 := by
    simpa [prefixWord, tailWord_1298837, baseEnd_1298837] using wordTrace_append hprefix tailTrace_1298837
  have hstable : (prefixWord ++ tailWord_1298837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298837).length < 2 ^ (prefixWord ++ tailWord_1298837).sum := by decide
  have hdescent : baseEnd_1298837 < baseStart_1298837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298848 : List Nat := [2, 1, 1, 4, 1, 4, 1, 1, 4, 2, 2]
def baseStart_1298848 : Nat := 118140960795 + 1298848 * 2 ^ 59
def prefixEnd_1298848 : Nat := 4983230072969 + 3 ^ 40 * 1298848 * 2
def baseEnd_1298848 : Nat := 666933321131039484926713

theorem tailTrace_1298848 : CollatzResearch.WordTrace tailWord_1298848 prefixEnd_1298848 666933321131039484926713 := by
  unfold tailWord_1298848
  simp only [CollatzResearch.WordTrace]
  refine ⟨23686439199251498211536599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31581918932335330948715465 23686439199251498211536599)
  ·
    refine ⟨35529658798877247317304899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23686439199251498211536599 35529658798877247317304899)
    ·
      refine ⟨53294488198315870975957349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35529658798877247317304899 53294488198315870975957349)
      ·
        refine ⟨9992716537184225807992003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53294488198315870975957349 9992716537184225807992003)
        ·
          refine ⟨14989074805776338711988005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9992716537184225807992003 14989074805776338711988005)
          ·
            refine ⟨2810451526083063508497751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14989074805776338711988005 2810451526083063508497751)
            ·
              refine ⟨4215677289124595262746627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2810451526083063508497751 4215677289124595262746627)
              ·
                refine ⟨6323515933686892894119941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4215677289124595262746627 6323515933686892894119941)
                ·
                  refine ⟨1185659237566292417647489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6323515933686892894119941 1185659237566292417647489)
                  ·
                    refine ⟨889244428174719313235617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1185659237566292417647489 889244428174719313235617)
                    ·
                      refine ⟨666933321131039484926713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 889244428174719313235617 666933321131039484926713)
                      ·
                        rfl

theorem cell23_1298848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_1298848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298848 prefixEnd_1298848 := by exact prefixLift 1298848
  have htrace : WordTrace (prefixWord ++ tailWord_1298848) baseStart_1298848 baseEnd_1298848 := by
    simpa [prefixWord, tailWord_1298848, baseEnd_1298848] using wordTrace_append hprefix tailTrace_1298848
  have hstable : (prefixWord ++ tailWord_1298848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298848).length < 2 ^ (prefixWord ++ tailWord_1298848).sum := by decide
  have hdescent : baseEnd_1298848 < baseStart_1298848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298888 : List Nat := [2, 1, 3, 1, 3, 4, 1, 3, 5]
def baseStart_1298888 : Nat := 118140960795 + 1298888 * 2 ^ 59
def prefixEnd_1298888 : Nat := 4983230072969 + 3 ^ 40 * 1298888 * 2
def baseEnd_1298888 : Nat := 74105984484135480936281

theorem tailTrace_1298888 : CollatzResearch.WordTrace tailWord_1298888 prefixEnd_1298888 74105984484135480936281 := by
  unfold tailWord_1298888
  simp only [CollatzResearch.WordTrace]
  refine ⟨23687168659179041627264659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31582891545572055503019545 23687168659179041627264659)
  ·
    refine ⟨35530752988768562440896989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23687168659179041627264659 35530752988768562440896989)
    ·
      refine ⟨13324032370788210915336371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35530752988768562440896989 13324032370788210915336371)
      ·
        refine ⟨19986048556182316373004557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13324032370788210915336371 19986048556182316373004557)
        ·
          refine ⟨7494768208568368639876709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19986048556182316373004557 7494768208568368639876709)
          ·
            refine ⟨1405269039106569119976883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7494768208568368639876709 1405269039106569119976883)
            ·
              refine ⟨2107903558659853679965325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1405269039106569119976883 2107903558659853679965325)
              ·
                refine ⟨790463834497445129986997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2107903558659853679965325 790463834497445129986997)
                ·
                  refine ⟨74105984484135480936281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 790463834497445129986997 74105984484135480936281)
                  ·
                    rfl

theorem cell23_1298888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 5].length) (baseStart_1298888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298888 prefixEnd_1298888 := by exact prefixLift 1298888
  have htrace : WordTrace (prefixWord ++ tailWord_1298888) baseStart_1298888 baseEnd_1298888 := by
    simpa [prefixWord, tailWord_1298888, baseEnd_1298888] using wordTrace_append hprefix tailTrace_1298888
  have hstable : (prefixWord ++ tailWord_1298888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298888).length < 2 ^ (prefixWord ++ tailWord_1298888).sum := by decide
  have hdescent : baseEnd_1298888 < baseStart_1298888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298894 : List Nat := [4, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5]
def baseStart_1298894 : Nat := 118140960795 + 1298894 * 2 ^ 59
def prefixEnd_1298894 : Nat := 4983230072969 + 3 ^ 40 * 1298894 * 2
def baseEnd_1298894 : Nat := 666956941241146304951501

theorem tailTrace_1298894 : CollatzResearch.WordTrace tailWord_1298894 prefixEnd_1298894 666956941241146304951501 := by
  unfold tailWord_1298894
  simp only [CollatzResearch.WordTrace]
  refine ⟨5921819519542043284905967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31583037437557564186165157 5921819519542043284905967)
  ·
    refine ⟨8882729279313064927358951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5921819519542043284905967 8882729279313064927358951)
    ·
      refine ⟨13324093918969597391038427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8882729279313064927358951 13324093918969597391038427)
      ·
        refine ⟨19986140878454396086557641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13324093918969597391038427 19986140878454396086557641)
        ·
          refine ⟨14989605658840797064918231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19986140878454396086557641 14989605658840797064918231)
          ·
            refine ⟨22484408488261195597377347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14989605658840797064918231 22484408488261195597377347)
            ·
              refine ⟨33726612732391793396066021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22484408488261195597377347 33726612732391793396066021)
              ·
                refine ⟨6323739887323461261762379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33726612732391793396066021 6323739887323461261762379)
                ·
                  refine ⟨9485609830985191892643569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6323739887323461261762379 9485609830985191892643569)
                  ·
                    refine ⟨7114207373238893919482677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9485609830985191892643569 7114207373238893919482677)
                    ·
                      refine ⟨666956941241146304951501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7114207373238893919482677 666956941241146304951501)
                      ·
                        rfl

theorem cell23_1298894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_1298894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298894 prefixEnd_1298894 := by exact prefixLift 1298894
  have htrace : WordTrace (prefixWord ++ tailWord_1298894) baseStart_1298894 baseEnd_1298894 := by
    simpa [prefixWord, tailWord_1298894, baseEnd_1298894] using wordTrace_append hprefix tailTrace_1298894
  have hstable : (prefixWord ++ tailWord_1298894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298894).length < 2 ^ (prefixWord ++ tailWord_1298894).sum := by decide
  have hdescent : baseEnd_1298894 < baseStart_1298894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298901 : List Nat := [1, 3, 2, 3, 1, 3, 1, 2, 2, 5]
def baseStart_1298901 : Nat := 118140960795 + 1298901 * 2 ^ 59
def prefixEnd_1298901 : Nat := 4983230072969 + 3 ^ 40 * 1298901 * 2
def baseEnd_1298901 : Nat := 222320178535242592521323

theorem tailTrace_1298901 : CollatzResearch.WordTrace tailWord_1298901 prefixEnd_1298901 222320178535242592521323 := by
  unfold tailWord_1298901
  simp only [CollatzResearch.WordTrace]
  refine ⟨47374811467310986474752557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31583207644873990983168371 47374811467310986474752557)
  ·
    refine ⟨17765554300241619928032209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47374811467310986474752557 17765554300241619928032209)
    ·
      refine ⟨13324165725181214946024157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17765554300241619928032209 13324165725181214946024157)
      ·
        refine ⟨4996562146942955604759059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13324165725181214946024157 4996562146942955604759059)
        ·
          refine ⟨7494843220414433407138589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4996562146942955604759059 7494843220414433407138589)
          ·
            refine ⟨2810566207655412527676971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7494843220414433407138589 2810566207655412527676971)
            ·
              refine ⟨4215849311483118791515457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2810566207655412527676971 4215849311483118791515457)
              ·
                refine ⟨3161886983612339093636593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4215849311483118791515457 3161886983612339093636593)
                ·
                  refine ⟨2371415237709254320227445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3161886983612339093636593 2371415237709254320227445)
                  ·
                    refine ⟨222320178535242592521323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2371415237709254320227445 222320178535242592521323)
                    ·
                      rfl

theorem cell23_1298901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_1298901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298901 prefixEnd_1298901 := by exact prefixLift 1298901
  have htrace : WordTrace (prefixWord ++ tailWord_1298901) baseStart_1298901 baseEnd_1298901 := by
    simpa [prefixWord, tailWord_1298901, baseEnd_1298901] using wordTrace_append hprefix tailTrace_1298901
  have hstable : (prefixWord ++ tailWord_1298901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298901).length < 2 ^ (prefixWord ++ tailWord_1298901).sum := by decide
  have hdescent : baseEnd_1298901 < baseStart_1298901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298958 : List Nat := [4, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3]
def baseStart_1298958 : Nat := 118140960795 + 1298958 * 2 ^ 59
def prefixEnd_1298958 : Nat := 4983230072969 + 3 ^ 40 * 1298958 * 2
def baseEnd_1298958 : Nat := 666989804003034054551207

theorem tailTrace_1298958 : CollatzResearch.WordTrace tailWord_1298958 prefixEnd_1298958 666989804003034054551207 := by
  unfold tailWord_1298958
  simp only [CollatzResearch.WordTrace]
  refine ⟨5922111303513060651197191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31584593618736323473051685 5922111303513060651197191)
  ·
    refine ⟨8883166955269590976795787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5922111303513060651197191 8883166955269590976795787)
    ·
      refine ⟨13324750432904386465193681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8883166955269590976795787 13324750432904386465193681)
      ·
        refine ⟨9993562824678289848895261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13324750432904386465193681 9993562824678289848895261)
        ·
          refine ⟨3747586059254358693335723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9993562824678289848895261 3747586059254358693335723)
          ·
            refine ⟨5621379088881538040003585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3747586059254358693335723 5621379088881538040003585)
            ·
              refine ⟨4216034316661153530002689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5621379088881538040003585 4216034316661153530002689)
              ·
                refine ⟨3162025737495865147502017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4216034316661153530002689 3162025737495865147502017)
                ·
                  refine ⟨2371519303121898860626513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3162025737495865147502017 2371519303121898860626513)
                  ·
                    refine ⟨1778639477341424145469885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2371519303121898860626513 1778639477341424145469885)
                    ·
                      refine ⟨666989804003034054551207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1778639477341424145469885 666989804003034054551207)
                      ·
                        rfl

theorem cell23_1298958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_1298958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298958 prefixEnd_1298958 := by exact prefixLift 1298958
  have htrace : WordTrace (prefixWord ++ tailWord_1298958) baseStart_1298958 baseEnd_1298958 := by
    simpa [prefixWord, tailWord_1298958, baseEnd_1298958] using wordTrace_append hprefix tailTrace_1298958
  have hstable : (prefixWord ++ tailWord_1298958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298958).length < 2 ^ (prefixWord ++ tailWord_1298958).sum := by decide
  have hdescent : baseEnd_1298958 < baseStart_1298958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298971 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 9, 1, 3]
def baseStart_1298971 : Nat := 118140960795 + 1298971 * 2 ^ 59
def prefixEnd_1298971 : Nat := 4983230072969 + 3 ^ 40 * 1298971 * 2
def baseEnd_1298971 : Nat := 666996479251542503688647

theorem tailTrace_1298971 : CollatzResearch.WordTrace tailWord_1298971 prefixEnd_1298971 666996479251542503688647 := by
  unfold tailWord_1298971
  simp only [CollatzResearch.WordTrace]
  refine ⟨47377364577057388429800767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31584909718038258953200511 47377364577057388429800767)
  ·
    refine ⟨71066046865586082644701151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47377364577057388429800767 71066046865586082644701151)
    ·
      refine ⟨106599070298379123967051727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71066046865586082644701151 106599070298379123967051727)
      ·
        refine ⟨159898605447568685950577591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106599070298379123967051727 159898605447568685950577591)
        ·
          refine ⟨239847908171353028925866387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159898605447568685950577591 239847908171353028925866387)
          ·
            refine ⟨359771862257029543388799581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239847908171353028925866387 359771862257029543388799581)
            ·
              refine ⟨134914448346386078770799843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 359771862257029543388799581 134914448346386078770799843)
              ·
                refine ⟨202371672519579118156199765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134914448346386078770799843 202371672519579118156199765)
                ·
                  refine ⟨1185771518669408895446483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 202371672519579118156199765 1185771518669408895446483)
                  ·
                    refine ⟨1778657278004113343169725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1185771518669408895446483 1778657278004113343169725)
                    ·
                      refine ⟨666996479251542503688647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1778657278004113343169725 666996479251542503688647)
                      ·
                        rfl

theorem cell23_1298971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 1, 3].length) (baseStart_1298971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298971 prefixEnd_1298971 := by exact prefixLift 1298971
  have htrace : WordTrace (prefixWord ++ tailWord_1298971) baseStart_1298971 baseEnd_1298971 := by
    simpa [prefixWord, tailWord_1298971, baseEnd_1298971] using wordTrace_append hprefix tailTrace_1298971
  have hstable : (prefixWord ++ tailWord_1298971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298971).length < 2 ^ (prefixWord ++ tailWord_1298971).sum := by decide
  have hdescent : baseEnd_1298971 < baseStart_1298971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298989 : List Nat := [1, 5, 4, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_1298989 : Nat := 118140960795 + 1298989 * 2 ^ 59
def prefixEnd_1298989 : Nat := 4983230072969 + 3 ^ 40 * 1298989 * 2
def baseEnd_1298989 : Nat := 667005721903323433263565

theorem tailTrace_1298989 : CollatzResearch.WordTrace tailWord_1298989 prefixEnd_1298989 667005721903323433263565 := by
  unfold tailWord_1298989
  simp only [CollatzResearch.WordTrace]
  refine ⟨47378021090992177503956021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31585347393994785002637347 47378021090992177503956021)
  ·
    refine ⟨4441689477280516640995877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47378021090992177503956021 4441689477280516640995877)
    ·
      refine ⟨832816776990096870186727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4441689477280516640995877 832816776990096870186727)
      ·
        refine ⟨1249225165485145305280091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 832816776990096870186727 1249225165485145305280091)
        ·
          refine ⟨1873837748227717957920137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1249225165485145305280091 1873837748227717957920137)
          ·
            refine ⟨1405378311170788468440103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1873837748227717957920137 1405378311170788468440103)
            ·
              refine ⟨2108067466756182702660155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1405378311170788468440103 2108067466756182702660155)
              ·
                refine ⟨3162101200134274053990233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2108067466756182702660155 3162101200134274053990233)
                ·
                  refine ⟨2371575900100705540492675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3162101200134274053990233 2371575900100705540492675)
                  ·
                    refine ⟨3557363850151058310739013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2371575900100705540492675 3557363850151058310739013)
                    ·
                      refine ⟨667005721903323433263565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3557363850151058310739013 667005721903323433263565)
                      ·
                        rfl

theorem cell23_1298989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_1298989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1298989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1298989 prefixEnd_1298989 := by exact prefixLift 1298989
  have htrace : WordTrace (prefixWord ++ tailWord_1298989) baseStart_1298989 baseEnd_1298989 := by
    simpa [prefixWord, tailWord_1298989, baseEnd_1298989] using wordTrace_append hprefix tailTrace_1298989
  have hstable : (prefixWord ++ tailWord_1298989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298989).length < 2 ^ (prefixWord ++ tailWord_1298989).sum := by decide
  have hdescent : baseEnd_1298989 < baseStart_1298989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299008 : List Nat := [2, 1, 1, 2, 2, 2, 6, 1, 1, 5]
def baseStart_1299008 : Nat := 118140960795 + 1299008 * 2 ^ 59
def prefixEnd_1299008 : Nat := 4983230072969 + 3 ^ 40 * 1299008 * 2
def baseEnd_1299008 : Nat := 222338492678586286308659

theorem tailTrace_1299008 : CollatzResearch.WordTrace tailWord_1299008 prefixEnd_1299008 222338492678586286308659 := by
  unfold tailWord_1299008
  simp only [CollatzResearch.WordTrace]
  refine ⟨23689357038961671874448839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31585809385282229165931785 23689357038961671874448839)
  ·
    refine ⟨35534035558442507811673259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23689357038961671874448839 35534035558442507811673259)
    ·
      refine ⟨53301053337663761717509889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35534035558442507811673259 53301053337663761717509889)
      ·
        refine ⟨39975790003247821288132417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53301053337663761717509889 39975790003247821288132417)
        ·
          refine ⟨29981842502435865966099313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39975790003247821288132417 29981842502435865966099313)
          ·
            refine ⟨22486381876826899474574485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29981842502435865966099313 22486381876826899474574485)
            ·
              refine ⟨1054049150476260912870679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22486381876826899474574485 1054049150476260912870679)
              ·
                refine ⟨1581073725714391369306019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1054049150476260912870679 1581073725714391369306019)
                ·
                  refine ⟨2371610588571587053959029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1581073725714391369306019 2371610588571587053959029)
                  ·
                    refine ⟨222338492678586286308659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2371610588571587053959029 222338492678586286308659)
                    ·
                      rfl

theorem cell23_1299008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 1, 5].length) (baseStart_1299008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299008 prefixEnd_1299008 := by exact prefixLift 1299008
  have htrace : WordTrace (prefixWord ++ tailWord_1299008) baseStart_1299008 baseEnd_1299008 := by
    simpa [prefixWord, tailWord_1299008, baseEnd_1299008] using wordTrace_append hprefix tailTrace_1299008
  have hstable : (prefixWord ++ tailWord_1299008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299008).length < 2 ^ (prefixWord ++ tailWord_1299008).sum := by decide
  have hdescent : baseEnd_1299008 < baseStart_1299008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299011 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 1, 8, 2]
def baseStart_1299011 : Nat := 118140960795 + 1299011 * 2 ^ 59
def prefixEnd_1299011 : Nat := 4983230072969 + 3 ^ 40 * 1299011 * 2
def baseEnd_1299011 : Nat := 667017018477722347188463

theorem tailTrace_1299011 : CollatzResearch.WordTrace tailWord_1299011 prefixEnd_1299011 667017018477722347188463 := by
  unfold tailWord_1299011
  simp only [CollatzResearch.WordTrace]
  refine ⟨47378823496912475261256887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31585882331274983507504591 47378823496912475261256887)
  ·
    refine ⟨71068235245368712891885331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47378823496912475261256887 71068235245368712891885331)
    ·
      refine ⟨106602352868053069337827997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71068235245368712891885331 106602352868053069337827997)
      ·
        refine ⟨39975882325519901001685499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106602352868053069337827997 39975882325519901001685499)
        ·
          refine ⟨59963823488279851502528249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39975882325519901001685499 59963823488279851502528249)
          ·
            refine ⟨44972867616209888626896187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59963823488279851502528249 44972867616209888626896187)
            ·
              refine ⟨67459301424314832940344281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44972867616209888626896187 67459301424314832940344281)
              ·
                refine ⟨50594476068236124705258211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67459301424314832940344281 50594476068236124705258211)
                ·
                  refine ⟨75891714102354187057887317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50594476068236124705258211 75891714102354187057887317)
                  ·
                    refine ⟨889356024636963129584617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75891714102354187057887317 889356024636963129584617)
                    ·
                      refine ⟨667017018477722347188463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 889356024636963129584617 667017018477722347188463)
                      ·
                        rfl

theorem cell23_1299011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 8, 2].length) (baseStart_1299011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299011 prefixEnd_1299011 := by exact prefixLift 1299011
  have htrace : WordTrace (prefixWord ++ tailWord_1299011) baseStart_1299011 baseEnd_1299011 := by
    simpa [prefixWord, tailWord_1299011, baseEnd_1299011] using wordTrace_append hprefix tailTrace_1299011
  have hstable : (prefixWord ++ tailWord_1299011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299011).length < 2 ^ (prefixWord ++ tailWord_1299011).sum := by decide
  have hdescent : baseEnd_1299011 < baseStart_1299011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299031 : List Nat := [1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 5]
def baseStart_1299031 : Nat := 118140960795 + 1299031 * 2 ^ 59
def prefixEnd_1299031 : Nat := 4983230072969 + 3 ^ 40 * 1299031 * 2
def baseEnd_1299031 : Nat := 667027288090812268938371

theorem tailTrace_1299031 : CollatzResearch.WordTrace tailWord_1299031 prefixEnd_1299031 667027288090812268938371 := by
  unfold tailWord_1299031
  simp only [CollatzResearch.WordTrace]
  refine ⟨47379552956840018676984947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31586368637893345784656631 47379552956840018676984947)
  ·
    refine ⟨71069329435260028015477421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47379552956840018676984947 71069329435260028015477421)
    ·
      refine ⟨26650998538222510505804033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71069329435260028015477421 26650998538222510505804033)
      ·
        refine ⟨19988248903666882879353025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26650998538222510505804033 19988248903666882879353025)
        ·
          refine ⟨14991186677750162159514769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19988248903666882879353025 14991186677750162159514769)
          ·
            refine ⟨11243390008312621619636077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14991186677750162159514769 11243390008312621619636077)
            ·
              refine ⟨4216271253117233107363529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11243390008312621619636077 4216271253117233107363529)
              ·
                refine ⟨3162203439837924830522647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4216271253117233107363529 3162203439837924830522647)
                ·
                  refine ⟨4743305159756887245783971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3162203439837924830522647 4743305159756887245783971)
                  ·
                    refine ⟨7114957739635330868675957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4743305159756887245783971 7114957739635330868675957)
                    ·
                      refine ⟨667027288090812268938371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7114957739635330868675957 667027288090812268938371)
                      ·
                        rfl

theorem cell23_1299031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_1299031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299031 prefixEnd_1299031 := by exact prefixLift 1299031
  have htrace : WordTrace (prefixWord ++ tailWord_1299031) baseStart_1299031 baseEnd_1299031 := by
    simpa [prefixWord, tailWord_1299031, baseEnd_1299031] using wordTrace_append hprefix tailTrace_1299031
  have hstable : (prefixWord ++ tailWord_1299031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299031).length < 2 ^ (prefixWord ++ tailWord_1299031).sum := by decide
  have hdescent : baseEnd_1299031 < baseStart_1299031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299041 : List Nat := [1, 2, 3, 1, 1, 5, 1, 1, 1, 1, 6]
def baseStart_1299041 : Nat := 118140960795 + 1299041 * 2 ^ 59
def prefixEnd_1299041 : Nat := 4983230072969 + 3 ^ 40 * 1299041 * 2
def baseEnd_1299041 : Nat := 667032422897357229813325

theorem tailTrace_1299041 : CollatzResearch.WordTrace tailWord_1299041 prefixEnd_1299041 667032422897357229813325 := by
  unfold tailWord_1299041
  simp only [CollatzResearch.WordTrace]
  refine ⟨47379917686803790384848977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31586611791202526923232651 47379917686803790384848977)
  ·
    refine ⟨35534938265102842788636733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47379917686803790384848977 35534938265102842788636733)
    ·
      refine ⟨13325601849413566045738775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35534938265102842788636733 13325601849413566045738775)
      ·
        refine ⟨19988402774120349068608163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13325601849413566045738775 19988402774120349068608163)
        ·
          refine ⟨29982604161180523602912245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19988402774120349068608163 29982604161180523602912245)
          ·
            refine ⟨2810869140110674087773023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29982604161180523602912245 2810869140110674087773023)
            ·
              refine ⟨4216303710166011131659535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2810869140110674087773023 4216303710166011131659535)
              ·
                refine ⟨6324455565249016697489303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4216303710166011131659535 6324455565249016697489303)
                ·
                  refine ⟨9486683347873525046233955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6324455565249016697489303 9486683347873525046233955)
                  ·
                    refine ⟨14230025021810287569350933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9486683347873525046233955 14230025021810287569350933)
                    ·
                      refine ⟨667032422897357229813325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14230025021810287569350933 667032422897357229813325)
                      ·
                        rfl

theorem cell23_1299041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_1299041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299041 prefixEnd_1299041 := by exact prefixLift 1299041
  have htrace : WordTrace (prefixWord ++ tailWord_1299041) baseStart_1299041 baseEnd_1299041 := by
    simpa [prefixWord, tailWord_1299041, baseEnd_1299041] using wordTrace_append hprefix tailTrace_1299041
  have hstable : (prefixWord ++ tailWord_1299041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299041).length < 2 ^ (prefixWord ++ tailWord_1299041).sum := by decide
  have hdescent : baseEnd_1299041 < baseStart_1299041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299042 : List Nat := [3, 3, 2, 3, 1, 1, 2, 2, 1, 5]
def baseStart_1299042 : Nat := 118140960795 + 1299042 * 2 ^ 59
def prefixEnd_1299042 : Nat := 4983230072969 + 3 ^ 40 * 1299042 * 2
def baseEnd_1299042 : Nat := 222344312126003908633607

theorem tailTrace_1299042 : CollatzResearch.WordTrace tailWord_1299042 prefixEnd_1299042 222344312126003908633607 := by
  unfold tailWord_1299042
  simp only [CollatzResearch.WordTrace]
  refine ⟨11844988539950041888908845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31586636106533445037090253 11844988539950041888908845)
  ·
    refine ⟨4441870702481265708340817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11844988539950041888908845 4441870702481265708340817)
    ·
      refine ⟨3331403026860949281255613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4441870702481265708340817 3331403026860949281255613)
      ·
        refine ⟨1249276135072855980470855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3331403026860949281255613 1249276135072855980470855)
        ·
          refine ⟨1873914202609283970706283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1249276135072855980470855 1873914202609283970706283)
          ·
            refine ⟨2810871303913925956059425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1873914202609283970706283 2810871303913925956059425)
            ·
              refine ⟨2108153477935444467044569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2810871303913925956059425 2108153477935444467044569)
              ·
                refine ⟨1581115108451583350283427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2108153477935444467044569 1581115108451583350283427)
                ·
                  refine ⟨2371672662677375025425141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1581115108451583350283427 2371672662677375025425141)
                  ·
                    refine ⟨222344312126003908633607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2371672662677375025425141 222344312126003908633607)
                    ·
                      rfl

theorem cell23_1299042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_1299042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299042 prefixEnd_1299042 := by exact prefixLift 1299042
  have htrace : WordTrace (prefixWord ++ tailWord_1299042) baseStart_1299042 baseEnd_1299042 := by
    simpa [prefixWord, tailWord_1299042, baseEnd_1299042] using wordTrace_append hprefix tailTrace_1299042
  have hstable : (prefixWord ++ tailWord_1299042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299042).length < 2 ^ (prefixWord ++ tailWord_1299042).sum := by decide
  have hdescent : baseEnd_1299042 < baseStart_1299042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299045 : List Nat := [1, 3, 1, 3, 4, 1, 2, 2, 1, 1, 4]
def baseStart_1299045 : Nat := 118140960795 + 1299045 * 2 ^ 59
def prefixEnd_1299045 : Nat := 4983230072969 + 3 ^ 40 * 1299045 * 2
def baseEnd_1299045 : Nat := 667034476819975214163307

theorem tailTrace_1299045 : CollatzResearch.WordTrace tailWord_1299045 prefixEnd_1299045 667034476819975214163307 := by
  unfold tailWord_1299045
  simp only [CollatzResearch.WordTrace]
  refine ⟨47380063578789299067994589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31586709052526199378663059 47380063578789299067994589)
  ·
    refine ⟨17767523842045987150497971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47380063578789299067994589 17767523842045987150497971)
    ·
      refine ⟨26651285763068980725746957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17767523842045987150497971 26651285763068980725746957)
      ·
        refine ⟨9994232161150867772155109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26651285763068980725746957 9994232161150867772155109)
        ·
          refine ⟨1873918530215787707279083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9994232161150867772155109 1873918530215787707279083)
          ·
            refine ⟨2810877795323681560918625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1873918530215787707279083 2810877795323681560918625)
            ·
              refine ⟨2108158346492761170688969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2810877795323681560918625 2108158346492761170688969)
              ·
                refine ⟨1581118759869570878016727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2108158346492761170688969 1581118759869570878016727)
                ·
                  refine ⟨2371678139804356317025091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1581118759869570878016727 2371678139804356317025091)
                  ·
                    refine ⟨3557517209706534475537637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2371678139804356317025091 3557517209706534475537637)
                    ·
                      refine ⟨667034476819975214163307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3557517209706534475537637 667034476819975214163307)
                      ·
                        rfl

theorem cell23_1299045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_1299045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299045 prefixEnd_1299045 := by exact prefixLift 1299045
  have htrace : WordTrace (prefixWord ++ tailWord_1299045) baseStart_1299045 baseEnd_1299045 := by
    simpa [prefixWord, tailWord_1299045, baseEnd_1299045] using wordTrace_append hprefix tailTrace_1299045
  have hstable : (prefixWord ++ tailWord_1299045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299045).length < 2 ^ (prefixWord ++ tailWord_1299045).sum := by decide
  have hdescent : baseEnd_1299045 < baseStart_1299045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299079 : List Nat := [1, 1, 4, 2, 1, 2, 5, 2, 1, 2, 2]
def baseStart_1299079 : Nat := 118140960795 + 1299079 * 2 ^ 59
def prefixEnd_1299079 : Nat := 4983230072969 + 3 ^ 40 * 1299079 * 2
def baseEnd_1299079 : Nat := 667051935162228081138151

theorem tailTrace_1299079 : CollatzResearch.WordTrace tailWord_1299079 prefixEnd_1299079 667051935162228081138151 := by
  unfold tailWord_1299079
  simp only [CollatzResearch.WordTrace]
  refine ⟨47381303660666122874732291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31587535773777415249821527 47381303660666122874732291)
  ·
    refine ⟨71071955490999184312098437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47381303660666122874732291 71071955490999184312098437)
    ·
      refine ⟨13325991654562347058518457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71071955490999184312098437 13325991654562347058518457)
      ·
        refine ⟨9994493740921760293888843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13325991654562347058518457 9994493740921760293888843)
        ·
          refine ⟨14991740611382640440833265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9994493740921760293888843 14991740611382640440833265)
          ·
            refine ⟨11243805458536980330624949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14991740611382640440833265 11243805458536980330624949)
            ·
              refine ⟨1054106761737841905996089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11243805458536980330624949 1054106761737841905996089)
              ·
                refine ⟨790580071303381429497067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1054106761737841905996089 790580071303381429497067)
                ·
                  refine ⟨1185870106955072144245601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 790580071303381429497067 1185870106955072144245601)
                  ·
                    refine ⟨889402580216304108184201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1185870106955072144245601 889402580216304108184201)
                    ·
                      refine ⟨667051935162228081138151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 889402580216304108184201 667051935162228081138151)
                      ·
                        rfl

theorem cell23_1299079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_1299079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299079 prefixEnd_1299079 := by exact prefixLift 1299079
  have htrace : WordTrace (prefixWord ++ tailWord_1299079) baseStart_1299079 baseEnd_1299079 := by
    simpa [prefixWord, tailWord_1299079, baseEnd_1299079] using wordTrace_append hprefix tailTrace_1299079
  have hstable : (prefixWord ++ tailWord_1299079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299079).length < 2 ^ (prefixWord ++ tailWord_1299079).sum := by decide
  have hdescent : baseEnd_1299079 < baseStart_1299079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299095 : List Nat := [1, 1, 3, 3, 2, 1, 3, 3, 2, 1, 3]
def baseStart_1299095 : Nat := 118140960795 + 1299095 * 2 ^ 59
def prefixEnd_1299095 : Nat := 4983230072969 + 3 ^ 40 * 1299095 * 2
def baseEnd_1299095 : Nat := 667060150852700018538077

theorem tailTrace_1299095 : CollatzResearch.WordTrace tailWord_1299095 prefixEnd_1299095 667060150852700018538077 := by
  unfold tailWord_1299095
  simp only [CollatzResearch.WordTrace]
  refine ⟨47381887228608157607314739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31587924819072105071543159 47381887228608157607314739)
  ·
    refine ⟨71072830842912236410972109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47381887228608157607314739 71072830842912236410972109)
    ·
      refine ⟨26652311566092088654114541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71072830842912236410972109 26652311566092088654114541)
      ·
        refine ⟨9994616837284533245292953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26652311566092088654114541 9994616837284533245292953)
        ·
          refine ⟨7495962627963399933969715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9994616837284533245292953 7495962627963399933969715)
          ·
            refine ⟨11243943941945099900954573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7495962627963399933969715 11243943941945099900954573)
            ·
              refine ⟨4216478978229412462857965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11243943941945099900954573 4216478978229412462857965)
              ·
                refine ⟨1581179616836029673571737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4216478978229412462857965 1581179616836029673571737)
                ·
                  refine ⟨1185884712627022255178803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1581179616836029673571737 1185884712627022255178803)
                  ·
                    refine ⟨1778827068940533382768205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1185884712627022255178803 1778827068940533382768205)
                    ·
                      refine ⟨667060150852700018538077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1778827068940533382768205 667060150852700018538077)
                      ·
                        rfl

theorem cell23_1299095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_1299095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299095 prefixEnd_1299095 := by exact prefixLift 1299095
  have htrace : WordTrace (prefixWord ++ tailWord_1299095) baseStart_1299095 baseEnd_1299095 := by
    simpa [prefixWord, tailWord_1299095, baseEnd_1299095] using wordTrace_append hprefix tailTrace_1299095
  have hstable : (prefixWord ++ tailWord_1299095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299095).length < 2 ^ (prefixWord ++ tailWord_1299095).sum := by decide
  have hdescent : baseEnd_1299095 < baseStart_1299095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299148 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 1, 4, 4]
def baseStart_1299148 : Nat := 118140960795 + 1299148 * 2 ^ 59
def prefixEnd_1299148 : Nat := 4983230072969 + 3 ^ 40 * 1299148 * 2
def baseEnd_1299148 : Nat := 667087365327388311175333

theorem tailTrace_1299148 : CollatzResearch.WordTrace tailWord_1299148 prefixEnd_1299148 667087365327388311175333 := by
  unfold tailWord_1299148
  simp only [CollatzResearch.WordTrace]
  refine ⟨23691910148708073829497049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31589213531610765105996065 23691910148708073829497049)
  ·
    refine ⟨17768932611531055372122787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23691910148708073829497049 17768932611531055372122787)
    ·
      refine ⟨26653398917296583058184181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17768932611531055372122787 26653398917296583058184181)
      ·
        refine ⟨2498756148496554661704767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26653398917296583058184181 2498756148496554661704767)
        ·
          refine ⟨3748134222744831992557151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2498756148496554661704767 3748134222744831992557151)
          ·
            refine ⟨5622201334117247988835727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3748134222744831992557151 5622201334117247988835727)
            ·
              refine ⟨8433302001175871983253591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5622201334117247988835727 8433302001175871983253591)
              ·
                refine ⟨12649953001763807974880387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8433302001175871983253591 12649953001763807974880387)
                ·
                  refine ⟨18974929502645711962320581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12649953001763807974880387 18974929502645711962320581)
                  ·
                    refine ⟨3557799281746070992935109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18974929502645711962320581 3557799281746070992935109)
                    ·
                      refine ⟨667087365327388311175333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3557799281746070992935109 667087365327388311175333)
                      ·
                        rfl

theorem cell23_1299148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_1299148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299148 prefixEnd_1299148 := by exact prefixLift 1299148
  have htrace : WordTrace (prefixWord ++ tailWord_1299148) baseStart_1299148 baseEnd_1299148 := by
    simpa [prefixWord, tailWord_1299148, baseEnd_1299148] using wordTrace_append hprefix tailTrace_1299148
  have hstable : (prefixWord ++ tailWord_1299148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299148).length < 2 ^ (prefixWord ++ tailWord_1299148).sum := by decide
  have hdescent : baseEnd_1299148 < baseStart_1299148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299208 : List Nat := [2, 1, 3, 2, 2, 2, 1, 2, 1, 3, 4]
def baseStart_1299208 : Nat := 118140960795 + 1299208 * 2 ^ 59
def prefixEnd_1299208 : Nat := 4983230072969 + 3 ^ 40 * 1299208 * 2
def baseEnd_1299208 : Nat := 667118174166658076425057

theorem tailTrace_1299208 : CollatzResearch.WordTrace tailWord_1299208 prefixEnd_1299208 667118174166658076425057 := by
  unfold tailWord_1299208
  simp only [CollatzResearch.WordTrace]
  refine ⟨23693004338599388953089139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31590672451465851937452185 23693004338599388953089139)
  ·
    refine ⟨35539506507899083429633709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23693004338599388953089139 35539506507899083429633709)
    ·
      refine ⟨13327314940462156286112641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35539506507899083429633709 13327314940462156286112641)
      ·
        refine ⟨9995486205346617214584481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13327314940462156286112641 9995486205346617214584481)
        ·
          refine ⟨7496614654009962910938361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9995486205346617214584481 7496614654009962910938361)
          ·
            refine ⟨5622460990507472183203771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7496614654009962910938361 5622460990507472183203771)
            ·
              refine ⟨8433691485761208274805657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5622460990507472183203771 8433691485761208274805657)
              ·
                refine ⟨6325268614320906206104243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8433691485761208274805657 6325268614320906206104243)
                ·
                  refine ⟨9487902921481359309156365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6325268614320906206104243 9487902921481359309156365)
                  ·
                    refine ⟨3557963595555509740933637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9487902921481359309156365 3557963595555509740933637)
                    ·
                      refine ⟨667118174166658076425057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3557963595555509740933637 667118174166658076425057)
                      ·
                        rfl

theorem cell23_1299208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_1299208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299208 prefixEnd_1299208 := by exact prefixLift 1299208
  have htrace : WordTrace (prefixWord ++ tailWord_1299208) baseStart_1299208 baseEnd_1299208 := by
    simpa [prefixWord, tailWord_1299208, baseEnd_1299208] using wordTrace_append hprefix tailTrace_1299208
  have hstable : (prefixWord ++ tailWord_1299208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299208).length < 2 ^ (prefixWord ++ tailWord_1299208).sum := by decide
  have hdescent : baseEnd_1299208 < baseStart_1299208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299308 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 3, 6]
def baseStart_1299308 : Nat := 118140960795 + 1299308 * 2 ^ 59
def prefixEnd_1299308 : Nat := 4983230072969 + 3 ^ 40 * 1299308 * 2
def baseEnd_1299308 : Nat := 222389840744035895058199

theorem tailTrace_1299308 : CollatzResearch.WordTrace tailWord_1299308 prefixEnd_1299308 222389840744035895058199 := by
  unfold tailWord_1299308
  simp only [CollatzResearch.WordTrace]
  refine ⟨23694827988418247492409289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31593103984557663323212385 23694827988418247492409289)
  ·
    refine ⟨17771120991313685619306967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23694827988418247492409289 17771120991313685619306967)
    ·
      refine ⟨26656681486970528428960451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17771120991313685619306967 26656681486970528428960451)
      ·
        refine ⟨39985022230455792643440677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26656681486970528428960451 39985022230455792643440677)
        ·
          refine ⟨7497191668210461120645127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39985022230455792643440677 7497191668210461120645127)
          ·
            refine ⟨11245787502315691680967691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7497191668210461120645127 11245787502315691680967691)
            ·
              refine ⟨16868681253473537521451537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11245787502315691680967691 16868681253473537521451537)
              ·
                refine ⟨12651510940105153141088653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16868681253473537521451537 12651510940105153141088653)
                ·
                  refine ⟨4744316602539432427908245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12651510940105153141088653 4744316602539432427908245)
                  ·
                    refine ⟨222389840744035895058199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4744316602539432427908245 222389840744035895058199)
                    ·
                      rfl

theorem cell23_1299308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_1299308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299308 prefixEnd_1299308 := by exact prefixLift 1299308
  have htrace : WordTrace (prefixWord ++ tailWord_1299308) baseStart_1299308 baseEnd_1299308 := by
    simpa [prefixWord, tailWord_1299308, baseEnd_1299308] using wordTrace_append hprefix tailTrace_1299308
  have hstable : (prefixWord ++ tailWord_1299308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299308).length < 2 ^ (prefixWord ++ tailWord_1299308).sum := by decide
  have hdescent : baseEnd_1299308 < baseStart_1299308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299326 : List Nat := [4, 2, 3, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_1299326 : Nat := 118140960795 + 1299326 * 2 ^ 59
def prefixEnd_1299326 : Nat := 4983230072969 + 3 ^ 40 * 1299326 * 2
def baseEnd_1299326 : Nat := 667178764883888614749515

theorem tailTrace_1299326 : CollatzResearch.WordTrace tailWord_1299326 prefixEnd_1299326 667178764883888614749515 := by
  unfold tailWord_1299326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5923789061346410507371729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31593541660514189372649221 5923789061346410507371729)
  ·
    refine ⟨4442841796009807880528797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5923789061346410507371729 4442841796009807880528797)
    ·
      refine ⟨1666065673503677955198299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4442841796009807880528797 1666065673503677955198299)
      ·
        refine ⟨2499098510255516932797449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1666065673503677955198299 2499098510255516932797449)
        ·
          refine ⟨1874323882691637699598087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2499098510255516932797449 1874323882691637699598087)
          ·
            refine ⟨2811485824037456549397131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1874323882691637699598087 2811485824037456549397131)
            ·
              refine ⟨4217228736056184824095697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2811485824037456549397131 4217228736056184824095697)
              ·
                refine ⟨3162921552042138618071773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4217228736056184824095697 3162921552042138618071773)
                ·
                  refine ⟨1186095582015801981776915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3162921552042138618071773 1186095582015801981776915)
                  ·
                    refine ⟨1779143373023702972665373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1186095582015801981776915 1779143373023702972665373)
                    ·
                      refine ⟨667178764883888614749515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1779143373023702972665373 667178764883888614749515)
                      ·
                        rfl

theorem cell23_1299326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_1299326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299326 prefixEnd_1299326 := by exact prefixLift 1299326
  have htrace : WordTrace (prefixWord ++ tailWord_1299326) baseStart_1299326 baseEnd_1299326 := by
    simpa [prefixWord, tailWord_1299326, baseEnd_1299326] using wordTrace_append hprefix tailTrace_1299326
  have hstable : (prefixWord ++ tailWord_1299326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299326).length < 2 ^ (prefixWord ++ tailWord_1299326).sum := by decide
  have hdescent : baseEnd_1299326 < baseStart_1299326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299346 : List Nat := [3, 2, 3, 2, 2, 2, 2, 1, 1, 5]
def baseStart_1299346 : Nat := 118140960795 + 1299346 * 2 ^ 59
def prefixEnd_1299346 : Nat := 4983230072969 + 3 ^ 40 * 1299346 * 2
def baseEnd_1299346 : Nat := 222396344832326178833141

theorem tailTrace_1299346 : CollatzResearch.WordTrace tailWord_1299346 prefixEnd_1299346 222396344832326178833141 := by
  unfold tailWord_1299346
  simp only [CollatzResearch.WordTrace]
  refine ⟨11847760487674706868675473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31594027967132551649801261 11847760487674706868675473)
  ·
    refine ⟨8885820365756030151506605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11847760487674706868675473 8885820365756030151506605)
    ·
      refine ⟨3332182637158511306814977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8885820365756030151506605 3332182637158511306814977)
      ·
        refine ⟨2499136977868883480111233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3332182637158511306814977 2499136977868883480111233)
        ·
          refine ⟨1874352733401662610083425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2499136977868883480111233 1874352733401662610083425)
          ·
            refine ⟨1405764550051246957562569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1874352733401662610083425 1405764550051246957562569)
            ·
              refine ⟨1054323412538435218171927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1405764550051246957562569 1054323412538435218171927)
              ·
                refine ⟨1581485118807652827257891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1054323412538435218171927 1581485118807652827257891)
                ·
                  refine ⟨2372227678211479240886837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1581485118807652827257891 2372227678211479240886837)
                  ·
                    refine ⟨222396344832326178833141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2372227678211479240886837 222396344832326178833141)
                    ·
                      rfl

theorem cell23_1299346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_1299346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299346 prefixEnd_1299346 := by exact prefixLift 1299346
  have htrace : WordTrace (prefixWord ++ tailWord_1299346) baseStart_1299346 baseEnd_1299346 := by
    simpa [prefixWord, tailWord_1299346, baseEnd_1299346] using wordTrace_append hprefix tailTrace_1299346
  have hstable : (prefixWord ++ tailWord_1299346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299346).length < 2 ^ (prefixWord ++ tailWord_1299346).sum := by decide
  have hdescent : baseEnd_1299346 < baseStart_1299346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299349 : List Nat := [1, 3, 2, 1, 1, 6, 2, 1, 1, 1, 4]
def baseStart_1299349 : Nat := 118140960795 + 1299349 * 2 ^ 59
def prefixEnd_1299349 : Nat := 4983230072969 + 3 ^ 40 * 1299349 * 2
def baseEnd_1299349 : Nat := 667190574938942024761909

theorem tailTrace_1299349 : CollatzResearch.WordTrace tailWord_1299349 prefixEnd_1299349 667190574938942024761909 := by
  unfold tailWord_1299349
  simp only [CollatzResearch.WordTrace]
  refine ⟨47391151369687958987061101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31594100913125305991374067 47391151369687958987061101)
  ·
    refine ⟨17771681763632984620147913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47391151369687958987061101 17771681763632984620147913)
    ·
      refine ⟨13328761322724738465110935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17771681763632984620147913 13328761322724738465110935)
      ·
        refine ⟨19993141984087107697666403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13328761322724738465110935 19993141984087107697666403)
        ·
          refine ⟨29989712976130661546499605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19993141984087107697666403 29989712976130661546499605)
          ·
            refine ⟨1405767795756124759992169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29989712976130661546499605 1405767795756124759992169)
            ·
              refine ⟨1054325846817093569994127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1405767795756124759992169 1054325846817093569994127)
              ·
                refine ⟨1581488770225640354991191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1054325846817093569994127 1581488770225640354991191)
                ·
                  refine ⟨2372233155338460532486787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1581488770225640354991191 2372233155338460532486787)
                  ·
                    refine ⟨3558349733007690798730181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2372233155338460532486787 3558349733007690798730181)
                    ·
                      refine ⟨667190574938942024761909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3558349733007690798730181 667190574938942024761909)
                      ·
                        rfl

theorem cell23_1299349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 1, 1, 4].length) (baseStart_1299349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299349 prefixEnd_1299349 := by exact prefixLift 1299349
  have htrace : WordTrace (prefixWord ++ tailWord_1299349) baseStart_1299349 baseEnd_1299349 := by
    simpa [prefixWord, tailWord_1299349, baseEnd_1299349] using wordTrace_append hprefix tailTrace_1299349
  have hstable : (prefixWord ++ tailWord_1299349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299349).length < 2 ^ (prefixWord ++ tailWord_1299349).sum := by decide
  have hdescent : baseEnd_1299349 < baseStart_1299349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299359 : List Nat := [1, 1, 2, 5, 2, 3, 1, 2, 2, 4]
def baseStart_1299359 : Nat := 118140960795 + 1299359 * 2 ^ 59
def prefixEnd_1299359 : Nat := 4983230072969 + 3 ^ 40 * 1299359 * 2
def baseEnd_1299359 : Nat := 222398569915162328545621

theorem tailTrace_1299359 : CollatzResearch.WordTrace tailWord_1299359 prefixEnd_1299359 222398569915162328545621 := by
  unfold tailWord_1299359
  simp only [CollatzResearch.WordTrace]
  refine ⟨47391516099651730694925131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31594344066434487129950087 47391516099651730694925131)
  ·
    refine ⟨71087274149477596042387697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47391516099651730694925131 71087274149477596042387697)
    ·
      refine ⟨53315455612108197031790773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71087274149477596042387697 53315455612108197031790773)
      ·
        refine ⟨4998323963635143471730385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53315455612108197031790773 4998323963635143471730385)
        ·
          refine ⟨3748742972726357603797789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4998323963635143471730385 3748742972726357603797789)
          ·
            refine ⟨1405778614772384101424171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3748742972726357603797789 1405778614772384101424171)
            ·
              refine ⟨2108667922158576152136257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1405778614772384101424171 2108667922158576152136257)
              ·
                refine ⟨1581500941618932114102193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2108667922158576152136257 1581500941618932114102193)
                ·
                  refine ⟨1186125706214199085576645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1581500941618932114102193 1186125706214199085576645)
                  ·
                    refine ⟨222398569915162328545621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1186125706214199085576645 222398569915162328545621)
                    ·
                      rfl

theorem cell23_1299359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 4].length) (baseStart_1299359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299359 prefixEnd_1299359 := by exact prefixLift 1299359
  have htrace : WordTrace (prefixWord ++ tailWord_1299359) baseStart_1299359 baseEnd_1299359 := by
    simpa [prefixWord, tailWord_1299359, baseEnd_1299359] using wordTrace_append hprefix tailTrace_1299359
  have hstable : (prefixWord ++ tailWord_1299359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299359).length < 2 ^ (prefixWord ++ tailWord_1299359).sum := by decide
  have hdescent : baseEnd_1299359 < baseStart_1299359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299375 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 2, 7, 2]
def baseStart_1299375 : Nat := 118140960795 + 1299375 * 2 ^ 59
def prefixEnd_1299375 : Nat := 4983230072969 + 3 ^ 40 * 1299375 * 2
def baseEnd_1299375 : Nat := 667203925435958923036789

theorem tailTrace_1299375 : CollatzResearch.WordTrace tailWord_1299375 prefixEnd_1299375 667203925435958923036789 := by
  unfold tailWord_1299375
  simp only [CollatzResearch.WordTrace]
  refine ⟨47392099667593765427507579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31594733111729176951671719 47392099667593765427507579)
  ·
    refine ⟨71088149501390648141261369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47392099667593765427507579 71088149501390648141261369)
    ·
      refine ⟨53316112126042986105946027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71088149501390648141261369 53316112126042986105946027)
      ·
        refine ⟨79974168189064479158919041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53316112126042986105946027 79974168189064479158919041)
        ·
          refine ⟨59980626141798359369189281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79974168189064479158919041 59980626141798359369189281)
          ·
            refine ⟨44985469606348769526891961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59980626141798359369189281 44985469606348769526891961)
            ·
              refine ⟨33739102204761577145168971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44985469606348769526891961 33739102204761577145168971)
              ·
                refine ⟨50608653307142365717753457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33739102204761577145168971 50608653307142365717753457)
                ·
                  refine ⟨37956489980356774288315093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50608653307142365717753457 37956489980356774288315093)
                  ·
                    refine ⟨889605233914611897382385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37956489980356774288315093 889605233914611897382385)
                    ·
                      refine ⟨667203925435958923036789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 889605233914611897382385 667203925435958923036789)
                      ·
                        rfl

theorem cell23_1299375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 7, 2].length) (baseStart_1299375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299375 prefixEnd_1299375 := by exact prefixLift 1299375
  have htrace : WordTrace (prefixWord ++ tailWord_1299375) baseStart_1299375 baseEnd_1299375 := by
    simpa [prefixWord, tailWord_1299375, baseEnd_1299375] using wordTrace_append hprefix tailTrace_1299375
  have hstable : (prefixWord ++ tailWord_1299375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299375).length < 2 ^ (prefixWord ++ tailWord_1299375).sum := by decide
  have hdescent : baseEnd_1299375 < baseStart_1299375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299389 : List Nat := [1, 4, 1, 2, 5, 1, 2, 7]
def baseStart_1299389 : Nat := 118140960795 + 1299389 * 2 ^ 59
def prefixEnd_1299389 : Nat := 4983230072969 + 3 ^ 40 * 1299389 * 2
def baseEnd_1299389 : Nat := 24711522746856365491175

theorem tailTrace_1299389 : CollatzResearch.WordTrace tailWord_1299389 prefixEnd_1299389 24711522746856365491175 := by
  unfold tailWord_1299389
  simp only [CollatzResearch.WordTrace]
  refine ⟨47392610289543045818517221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31595073526362030545678147 47392610289543045818517221)
  ·
    refine ⟨8886114429289321090971979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47392610289543045818517221 8886114429289321090971979)
    ·
      refine ⟨13329171643933981636457969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8886114429289321090971979 13329171643933981636457969)
      ·
        refine ⟨9996878732950486227343477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13329171643933981636457969 9996878732950486227343477)
        ·
          refine ⟨937207381214108083813451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9996878732950486227343477 937207381214108083813451)
          ·
            refine ⟨1405811071821162125720177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 937207381214108083813451 1405811071821162125720177)
            ·
              refine ⟨1054358303865871594290133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1405811071821162125720177 1054358303865871594290133)
              ·
                refine ⟨24711522746856365491175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1054358303865871594290133 24711522746856365491175)
                ·
                  rfl

theorem cell23_1299389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 7].length) (baseStart_1299389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299389 prefixEnd_1299389 := by exact prefixLift 1299389
  have htrace : WordTrace (prefixWord ++ tailWord_1299389) baseStart_1299389 baseEnd_1299389 := by
    simpa [prefixWord, tailWord_1299389, baseEnd_1299389] using wordTrace_append hprefix tailTrace_1299389
  have hstable : (prefixWord ++ tailWord_1299389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299389).length < 2 ^ (prefixWord ++ tailWord_1299389).sum := by decide
  have hdescent : baseEnd_1299389 < baseStart_1299389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299400 : List Nat := [2, 1, 3, 1, 6, 1, 1, 3, 1, 2, 2]
def baseStart_1299400 : Nat := 118140960795 + 1299400 * 2 ^ 59
def prefixEnd_1299400 : Nat := 4983230072969 + 3 ^ 40 * 1299400 * 2
def baseEnd_1299400 : Nat := 667216762452321325224175

theorem tailTrace_1299400 : CollatzResearch.WordTrace tailWord_1299400 prefixEnd_1299400 667216762452321325224175 := by
  unfold tailWord_1299400
  simp only [CollatzResearch.WordTrace]
  refine ⟨23696505746251597348583827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31595340995002129798111769 23696505746251597348583827)
  ·
    refine ⟨35544758619377396022875741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23696505746251597348583827 35544758619377396022875741)
    ·
      refine ⟨13329284482266523508578403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35544758619377396022875741 13329284482266523508578403)
      ·
        refine ⟨19993926723399785262867605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13329284482266523508578403 19993926723399785262867605)
        ·
          refine ⟨937215315159364934196919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19993926723399785262867605 937215315159364934196919)
          ·
            refine ⟨1405822972739047401295379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 937215315159364934196919 1405822972739047401295379)
            ·
              refine ⟨2108734459108571101943069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1405822972739047401295379 2108734459108571101943069)
              ·
                refine ⟨790775422165714163228651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2108734459108571101943069 790775422165714163228651)
                ·
                  refine ⟨1186163133248571244842977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 790775422165714163228651 1186163133248571244842977)
                  ·
                    refine ⟨889622349936428433632233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1186163133248571244842977 889622349936428433632233)
                    ·
                      refine ⟨667216762452321325224175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 889622349936428433632233 667216762452321325224175)
                      ·
                        rfl

theorem cell23_1299400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 1, 2, 2].length) (baseStart_1299400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299400 prefixEnd_1299400 := by exact prefixLift 1299400
  have htrace : WordTrace (prefixWord ++ tailWord_1299400) baseStart_1299400 baseEnd_1299400 := by
    simpa [prefixWord, tailWord_1299400, baseEnd_1299400] using wordTrace_append hprefix tailTrace_1299400
  have hstable : (prefixWord ++ tailWord_1299400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299400).length < 2 ^ (prefixWord ++ tailWord_1299400).sum := by decide
  have hdescent : baseEnd_1299400 < baseStart_1299400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299425 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 2, 4, 3]
def baseStart_1299425 : Nat := 118140960795 + 1299425 * 2 ^ 59
def prefixEnd_1299425 : Nat := 4983230072969 + 3 ^ 40 * 1299425 * 2
def baseEnd_1299425 : Nat := 667229599468683727411559

theorem tailTrace_1299425 : CollatzResearch.WordTrace tailWord_1299425 prefixEnd_1299425 667229599468683727411559 := by
  unfold tailWord_1299425
  simp only [CollatzResearch.WordTrace]
  refine ⟨47393923317412623966827729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31595948878275082644551819 47393923317412623966827729)
  ·
    refine ⟨35545442488059467975120797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47393923317412623966827729 35545442488059467975120797)
    ·
      refine ⟨13329540933022300490670299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35545442488059467975120797 13329540933022300490670299)
      ·
        refine ⟨19994311399533450736005449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13329540933022300490670299 19994311399533450736005449)
        ·
          refine ⟨14995733549650088052004087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19994311399533450736005449 14995733549650088052004087)
          ·
            refine ⟨22493600324475132078006131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14995733549650088052004087 22493600324475132078006131)
            ·
              refine ⟨33740400486712698117009197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22493600324475132078006131 33740400486712698117009197)
              ·
                refine ⟨12652650182517261793878449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33740400486712698117009197 12652650182517261793878449)
                ·
                  refine ⟨9489487636887946345408837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12652650182517261793878449 9489487636887946345408837)
                  ·
                    refine ⟨1779278931916489939764157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9489487636887946345408837 1779278931916489939764157)
                    ·
                      refine ⟨667229599468683727411559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1779278931916489939764157 667229599468683727411559)
                      ·
                        rfl

theorem cell23_1299425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_1299425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299425 prefixEnd_1299425 := by exact prefixLift 1299425
  have htrace : WordTrace (prefixWord ++ tailWord_1299425) baseStart_1299425 baseEnd_1299425 := by
    simpa [prefixWord, tailWord_1299425, baseEnd_1299425] using wordTrace_append hprefix tailTrace_1299425
  have hstable : (prefixWord ++ tailWord_1299425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299425).length < 2 ^ (prefixWord ++ tailWord_1299425).sum := by decide
  have hdescent : baseEnd_1299425 < baseStart_1299425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299455 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 3]
def baseStart_1299455 : Nat := 118140960795 + 1299455 * 2 ^ 59
def prefixEnd_1299455 : Nat := 4983230072969 + 3 ^ 40 * 1299455 * 2
def baseEnd_1299455 : Nat := 667245003888318610036421

theorem tailTrace_1299455 : CollatzResearch.WordTrace tailWord_1299455 prefixEnd_1299455 667245003888318610036421 := by
  unfold tailWord_1299455
  simp only [CollatzResearch.WordTrace]
  refine ⟨47395017507303939090419819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31596678338202626060279879 47395017507303939090419819)
  ·
    refine ⟨71092526260955908635629729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47395017507303939090419819 71092526260955908635629729)
    ·
      refine ⟨53319394695716931476722297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71092526260955908635629729 53319394695716931476722297)
      ·
        refine ⟨39989546021787698607541723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53319394695716931476722297 39989546021787698607541723)
        ·
          refine ⟨59984319032681547911312585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39989546021787698607541723 59984319032681547911312585)
          ·
            refine ⟨44988239274511160933484439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59984319032681547911312585 44988239274511160933484439)
            ·
              refine ⟨67482358911766741400226659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44988239274511160933484439 67482358911766741400226659)
              ·
                refine ⟨101223538367650112100339989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67482358911766741400226659 101223538367650112100339989)
                ·
                  refine ⟨4744853360983599004703437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 101223538367650112100339989 4744853360983599004703437)
                  ·
                    refine ⟨1779320010368849626763789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4744853360983599004703437 1779320010368849626763789)
                    ·
                      refine ⟨667245003888318610036421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1779320010368849626763789 667245003888318610036421)
                      ·
                        rfl

theorem cell23_1299455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 3].length) (baseStart_1299455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299455 prefixEnd_1299455 := by exact prefixLift 1299455
  have htrace : WordTrace (prefixWord ++ tailWord_1299455) baseStart_1299455 baseEnd_1299455 := by
    simpa [prefixWord, tailWord_1299455, baseEnd_1299455] using wordTrace_append hprefix tailTrace_1299455
  have hstable : (prefixWord ++ tailWord_1299455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299455).length < 2 ^ (prefixWord ++ tailWord_1299455).sum := by decide
  have hdescent : baseEnd_1299455 < baseStart_1299455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299479 : List Nat := [1, 1, 3, 5, 1, 2, 1, 4, 5]
def baseStart_1299479 : Nat := 118140960795 + 1299479 * 2 ^ 59
def prefixEnd_1299479 : Nat := 4983230072969 + 3 ^ 40 * 1299479 * 2
def baseEnd_1299479 : Nat := 74139703047114057348479

theorem tailTrace_1299479 : CollatzResearch.WordTrace tailWord_1299479 prefixEnd_1299479 74139703047114057348479 := by
  unfold tailWord_1299479
  simp only [CollatzResearch.WordTrace]
  refine ⟨47395892859216991189293491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31597261906144660792862327 47395892859216991189293491)
  ·
    refine ⟨71093839288825486783940237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47395892859216991189293491 71093839288825486783940237)
    ·
      refine ⟨26660189733309557543977589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71093839288825486783940237 26660189733309557543977589)
      ·
        refine ⟨2499392787497771019747899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26660189733309557543977589 2499392787497771019747899)
        ·
          refine ⟨3749089181246656529621849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2499392787497771019747899 3749089181246656529621849)
          ·
            refine ⟨2811816885934992397216387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3749089181246656529621849 2811816885934992397216387)
            ·
              refine ⟨4217725328902488595824581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2811816885934992397216387 4217725328902488595824581)
              ·
                refine ⟨790823499169216611717109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4217725328902488595824581 790823499169216611717109)
                ·
                  refine ⟨74139703047114057348479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 790823499169216611717109 74139703047114057348479)
                  ·
                    rfl

theorem cell23_1299479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 5].length) (baseStart_1299479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299479 prefixEnd_1299479 := by exact prefixLift 1299479
  have htrace : WordTrace (prefixWord ++ tailWord_1299479) baseStart_1299479 baseEnd_1299479 := by
    simpa [prefixWord, tailWord_1299479, baseEnd_1299479] using wordTrace_append hprefix tailTrace_1299479
  have hstable : (prefixWord ++ tailWord_1299479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299479).length < 2 ^ (prefixWord ++ tailWord_1299479).sum := by decide
  have hdescent : baseEnd_1299479 < baseStart_1299479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299482 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2]
def baseStart_1299482 : Nat := 118140960795 + 1299482 * 2 ^ 59
def prefixEnd_1299482 : Nat := 4983230072969 + 3 ^ 40 * 1299482 * 2
def baseEnd_1299482 : Nat := 667258867865990004398797

theorem tailTrace_1299482 : CollatzResearch.WordTrace tailWord_1299482 prefixEnd_1299482 667258867865990004398797 := by
  unfold tailWord_1299482
  simp only [CollatzResearch.WordTrace]
  refine ⟨11849000569551530675413175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31597334852137415134435133 11849000569551530675413175)
  ·
    refine ⟨17773500854327296013119763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11849000569551530675413175 17773500854327296013119763)
    ·
      refine ⟨26660251281490944019679645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17773500854327296013119763 26660251281490944019679645)
      ·
        refine ⟨9997594230559104007379867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26660251281490944019679645 9997594230559104007379867)
        ·
          refine ⟨14996391345838656011069801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9997594230559104007379867 14996391345838656011069801)
          ·
            refine ⟨11247293509378992008302351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14996391345838656011069801 11247293509378992008302351)
            ·
              refine ⟨16870940264068488012453527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11247293509378992008302351 16870940264068488012453527)
              ·
                refine ⟨25306410396102732018680291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16870940264068488012453527 25306410396102732018680291)
                ·
                  refine ⟨37959615594154098028020437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25306410396102732018680291 37959615594154098028020437)
                  ·
                    refine ⟨889678490487986672531729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37959615594154098028020437 889678490487986672531729)
                    ·
                      refine ⟨667258867865990004398797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 889678490487986672531729 667258867865990004398797)
                      ·
                        rfl

theorem cell23_1299482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_1299482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299482 prefixEnd_1299482 := by exact prefixLift 1299482
  have htrace : WordTrace (prefixWord ++ tailWord_1299482) baseStart_1299482 baseEnd_1299482 := by
    simpa [prefixWord, tailWord_1299482, baseEnd_1299482] using wordTrace_append hprefix tailTrace_1299482
  have hstable : (prefixWord ++ tailWord_1299482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299482).length < 2 ^ (prefixWord ++ tailWord_1299482).sum := by decide
  have hdescent : baseEnd_1299482 < baseStart_1299482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299512 : List Nat := [2, 1, 2, 1, 5, 2, 1, 1, 1, 3, 4]
def baseStart_1299512 : Nat := 118140960795 + 1299512 * 2 ^ 59
def prefixEnd_1299512 : Nat := 4983230072969 + 3 ^ 40 * 1299512 * 2
def baseEnd_1299512 : Nat := 667274272285624887023659

theorem tailTrace_1299512 : CollatzResearch.WordTrace tailWord_1299512 prefixEnd_1299512 667274272285624887023659 := by
  unfold tailWord_1299512
  simp only [CollatzResearch.WordTrace]
  refine ⟨23698548234048718912622395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31598064312064958550163193 23698548234048718912622395)
  ·
    refine ⟨35547822351073078368933593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23698548234048718912622395 35547822351073078368933593)
    ·
      refine ⟨26660866763304808776700195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35547822351073078368933593 26660866763304808776700195)
      ·
        refine ⟨39991300144957213165050293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26660866763304808776700195 39991300144957213165050293)
        ·
          refine ⟨3749184388589738734223465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39991300144957213165050293 3749184388589738734223465)
          ·
            refine ⟨2811888291442304050667599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3749184388589738734223465 2811888291442304050667599)
            ·
              refine ⟨4217832437163456076001399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2811888291442304050667599 4217832437163456076001399)
              ·
                refine ⟨6326748655745184114002099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4217832437163456076001399 6326748655745184114002099)
                ·
                  refine ⟨9490122983617776171003149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6326748655745184114002099 9490122983617776171003149)
                  ·
                    refine ⟨3558796118856666064126181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9490122983617776171003149 3558796118856666064126181)
                    ·
                      refine ⟨667274272285624887023659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3558796118856666064126181 667274272285624887023659)
                      ·
                        rfl

theorem cell23_1299512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_1299512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299512 prefixEnd_1299512 := by exact prefixLift 1299512
  have htrace : WordTrace (prefixWord ++ tailWord_1299512) baseStart_1299512 baseEnd_1299512 := by
    simpa [prefixWord, tailWord_1299512, baseEnd_1299512] using wordTrace_append hprefix tailTrace_1299512
  have hstable : (prefixWord ++ tailWord_1299512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299512).length < 2 ^ (prefixWord ++ tailWord_1299512).sum := by decide
  have hdescent : baseEnd_1299512 < baseStart_1299512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299525 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 2, 1, 6]
def baseStart_1299525 : Nat := 118140960795 + 1299525 * 2 ^ 59
def prefixEnd_1299525 : Nat := 4983230072969 + 3 ^ 40 * 1299525 * 2
def baseEnd_1299525 : Nat := 667280947534133336161099

theorem tailTrace_1299525 : CollatzResearch.WordTrace tailWord_1299525 prefixEnd_1299525 667280947534133336161099 := by
  unfold tailWord_1299525
  simp only [CollatzResearch.WordTrace]
  refine ⟨47397570617050341045468029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31598380411366894030312019 47397570617050341045468029)
  ·
    refine ⟨17774088981393877892050511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47397570617050341045468029 17774088981393877892050511)
    ·
      refine ⟨26661133472090816838075767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17774088981393877892050511 26661133472090816838075767)
      ·
        refine ⟨39991700208136225257113651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26661133472090816838075767 39991700208136225257113651)
        ·
          refine ⟨59987550312204337885670477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39991700208136225257113651 59987550312204337885670477)
          ·
            refine ⟨22495331367076626707126429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59987550312204337885670477 22495331367076626707126429)
            ·
              refine ⟨8435749262653735015172411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22495331367076626707126429 8435749262653735015172411)
              ·
                refine ⟨12653623893980602522758617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8435749262653735015172411 12653623893980602522758617)
                ·
                  refine ⟨9490217920485451892068963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12653623893980602522758617 9490217920485451892068963)
                  ·
                    refine ⟨14235326880728177838103445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9490217920485451892068963 14235326880728177838103445)
                    ·
                      refine ⟨667280947534133336161099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14235326880728177838103445 667280947534133336161099)
                      ·
                        rfl

theorem cell23_1299525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_1299525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299525 prefixEnd_1299525 := by exact prefixLift 1299525
  have htrace : WordTrace (prefixWord ++ tailWord_1299525) baseStart_1299525 baseEnd_1299525 := by
    simpa [prefixWord, tailWord_1299525, baseEnd_1299525] using wordTrace_append hprefix tailTrace_1299525
  have hstable : (prefixWord ++ tailWord_1299525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299525).length < 2 ^ (prefixWord ++ tailWord_1299525).sum := by decide
  have hdescent : baseEnd_1299525 < baseStart_1299525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299532 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 4, 2, 3]
def baseStart_1299532 : Nat := 118140960795 + 1299532 * 2 ^ 59
def prefixEnd_1299532 : Nat := 4983230072969 + 3 ^ 40 * 1299532 * 2
def baseEnd_1299532 : Nat := 667284541898714808773567

theorem tailTrace_1299532 : CollatzResearch.WordTrace tailWord_1299532 prefixEnd_1299532 667284541898714808773567 := by
  unfold tailWord_1299532
  simp only [CollatzResearch.WordTrace]
  refine ⟨23698912964012490620486425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31598550618683320827315233 23698912964012490620486425)
  ·
    refine ⟨17774184723009367965364819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23698912964012490620486425 17774184723009367965364819)
    ·
      refine ⟨26661277084514051948047229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17774184723009367965364819 26661277084514051948047229)
      ·
        refine ⟨9997978906692769480517711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26661277084514051948047229 9997978906692769480517711)
        ·
          refine ⟨14996968360039154220776567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9997978906692769480517711 14996968360039154220776567)
          ·
            refine ⟨22495452540058731331164851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14996968360039154220776567 22495452540058731331164851)
            ·
              refine ⟨33743178810088096996747277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22495452540058731331164851 33743178810088096996747277)
              ·
                refine ⟨12653692053783036373780229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33743178810088096996747277 12653692053783036373780229)
                ·
                  refine ⟨2372567260084319320083793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12653692053783036373780229 2372567260084319320083793)
                  ·
                    refine ⟨1779425445063239490062845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2372567260084319320083793 1779425445063239490062845)
                    ·
                      refine ⟨667284541898714808773567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1779425445063239490062845 667284541898714808773567)
                      ·
                        rfl

theorem cell23_1299532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_1299532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299532 prefixEnd_1299532 := by exact prefixLift 1299532
  have htrace : WordTrace (prefixWord ++ tailWord_1299532) baseStart_1299532 baseEnd_1299532 := by
    simpa [prefixWord, tailWord_1299532, baseEnd_1299532] using wordTrace_append hprefix tailTrace_1299532
  have hstable : (prefixWord ++ tailWord_1299532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299532).length < 2 ^ (prefixWord ++ tailWord_1299532).sum := by decide
  have hdescent : baseEnd_1299532 < baseStart_1299532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299555 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 6]
def baseStart_1299555 : Nat := 118140960795 + 1299555 * 2 ^ 59
def prefixEnd_1299555 : Nat := 4983230072969 + 3 ^ 40 * 1299555 * 2
def baseEnd_1299555 : Nat := 667296351953768218785961

theorem tailTrace_1299555 : CollatzResearch.WordTrace tailWord_1299555 prefixEnd_1299555 667296351953768218785961 := by
  unfold tailWord_1299555
  simp only [CollatzResearch.WordTrace]
  refine ⟨47398664806941656169060119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31599109871294437446040079 47398664806941656169060119)
  ·
    refine ⟨71097997210412484253590179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47398664806941656169060119 71097997210412484253590179)
    ·
      refine ⟨106646995815618726380385269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71097997210412484253590179 106646995815618726380385269)
      ·
        refine ⟨9998155857714255598161119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106646995815618726380385269 9998155857714255598161119)
        ·
          refine ⟨14997233786571383397241679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9998155857714255598161119 14997233786571383397241679)
          ·
            refine ⟨22495850679857075095862519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14997233786571383397241679 22495850679857075095862519)
            ·
              refine ⟨33743776019785612643793779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22495850679857075095862519 33743776019785612643793779)
              ·
                refine ⟨50615664029678418965690669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33743776019785612643793779 50615664029678418965690669)
                ·
                  refine ⟨18980874011129407112134001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50615664029678418965690669 18980874011129407112134001)
                  ·
                    refine ⟨14235655508347055334100501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18980874011129407112134001 14235655508347055334100501)
                    ·
                      refine ⟨667296351953768218785961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14235655508347055334100501 667296351953768218785961)
                      ·
                        rfl

theorem cell23_1299555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_1299555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299555 prefixEnd_1299555 := by exact prefixLift 1299555
  have htrace : WordTrace (prefixWord ++ tailWord_1299555) baseStart_1299555 baseEnd_1299555 := by
    simpa [prefixWord, tailWord_1299555, baseEnd_1299555] using wordTrace_append hprefix tailTrace_1299555
  have hstable : (prefixWord ++ tailWord_1299555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299555).length < 2 ^ (prefixWord ++ tailWord_1299555).sum := by decide
  have hdescent : baseEnd_1299555 < baseStart_1299555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299596 : List Nat := [2, 2, 1, 2, 1, 1, 1, 8, 1, 1, 3]
def baseStart_1299596 : Nat := 118140960795 + 1299596 * 2 ^ 59
def prefixEnd_1299596 : Nat := 4983230072969 + 3 ^ 40 * 1299596 * 2
def baseEnd_1299596 : Nat := 667317404660602558373273

theorem tailTrace_1299596 : CollatzResearch.WordTrace tailWord_1299596 prefixEnd_1299596 667317404660602558373273 := by
  unfold tailWord_1299596
  simp only [CollatzResearch.WordTrace]
  refine ⟨23700080099896560085651321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31600106799862080114201761 23700080099896560085651321)
  ·
    refine ⟨17775060074922420064238491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23700080099896560085651321 17775060074922420064238491)
    ·
      refine ⟨26662590112383630096357737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17775060074922420064238491 26662590112383630096357737)
      ·
        refine ⟨19996942584287722572268303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26662590112383630096357737 19996942584287722572268303)
        ·
          refine ⟨29995413876431583858402455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19996942584287722572268303 29995413876431583858402455)
          ·
            refine ⟨44993120814647375787603683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29995413876431583858402455 44993120814647375787603683)
            ·
              refine ⟨67489681221971063681405525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44993120814647375787603683 67489681221971063681405525)
              ·
                refine ⟨790894701819973402516471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 67489681221971063681405525 790894701819973402516471)
                ·
                  refine ⟨1186342052729960103774707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 790894701819973402516471 1186342052729960103774707)
                  ·
                    refine ⟨1779513079094940155662061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1186342052729960103774707 1779513079094940155662061)
                    ·
                      refine ⟨667317404660602558373273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1779513079094940155662061 667317404660602558373273)
                      ·
                        rfl

theorem cell23_1299596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 1, 1, 3].length) (baseStart_1299596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299596 prefixEnd_1299596 := by exact prefixLift 1299596
  have htrace : WordTrace (prefixWord ++ tailWord_1299596) baseStart_1299596 baseEnd_1299596 := by
    simpa [prefixWord, tailWord_1299596, baseEnd_1299596] using wordTrace_append hprefix tailTrace_1299596
  have hstable : (prefixWord ++ tailWord_1299596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299596).length < 2 ^ (prefixWord ++ tailWord_1299596).sum := by decide
  have hdescent : baseEnd_1299596 < baseStart_1299596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299623 : List Nat := [1, 1, 6, 2, 1, 2, 2, 1, 2, 3, 2]
def baseStart_1299623 : Nat := 118140960795 + 1299623 * 2 ^ 59
def prefixEnd_1299623 : Nat := 4983230072969 + 3 ^ 40 * 1299623 * 2
def baseEnd_1299623 : Nat := 667331268638273952735649

theorem tailTrace_1299623 : CollatzResearch.WordTrace tailWord_1299623 prefixEnd_1299623 667331268638273952735649 := by
  unfold tailWord_1299623
  simp only [CollatzResearch.WordTrace]
  refine ⟨47401144970695303782535523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31600763313796869188357015 47401144970695303782535523)
  ·
    refine ⟨71101717456042955673803285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47401144970695303782535523 71101717456042955673803285)
    ·
      refine ⟨3332893005752013547209529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 71101717456042955673803285 3332893005752013547209529)
      ·
        refine ⟨2499669754314010160407147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3332893005752013547209529 2499669754314010160407147)
        ·
          refine ⟨3749504631471015240610721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2499669754314010160407147 3749504631471015240610721)
          ·
            refine ⟨2812128473603261430458041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3749504631471015240610721 2812128473603261430458041)
            ·
              refine ⟨2109096355202446072843531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2812128473603261430458041 2109096355202446072843531)
              ·
                refine ⟨3163644532803669109265297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2109096355202446072843531 3163644532803669109265297)
                ·
                  refine ⟨2372733399602751831948973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3163644532803669109265297 2372733399602751831948973)
                  ·
                    refine ⟨889775024851031936980865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2372733399602751831948973 889775024851031936980865)
                    ·
                      refine ⟨667331268638273952735649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 889775024851031936980865 667331268638273952735649)
                      ·
                        rfl

theorem cell23_1299623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_1299623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299623 prefixEnd_1299623 := by exact prefixLift 1299623
  have htrace : WordTrace (prefixWord ++ tailWord_1299623) baseStart_1299623 baseEnd_1299623 := by
    simpa [prefixWord, tailWord_1299623, baseEnd_1299623] using wordTrace_append hprefix tailTrace_1299623
  have hstable : (prefixWord ++ tailWord_1299623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299623).length < 2 ^ (prefixWord ++ tailWord_1299623).sum := by decide
  have hdescent : baseEnd_1299623 < baseStart_1299623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299632 : List Nat := [2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 4]
def baseStart_1299632 : Nat := 118140960795 + 1299632 * 2 ^ 59
def prefixEnd_1299632 : Nat := 4983230072969 + 3 ^ 40 * 1299632 * 2
def baseEnd_1299632 : Nat := 667335889964164417523107

theorem tailTrace_1299632 : CollatzResearch.WordTrace tailWord_1299632 prefixEnd_1299632 667335889964164417523107 := by
  unfold tailWord_1299632
  simp only [CollatzResearch.WordTrace]
  refine ⟨23700736613831349159806575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31600982151775132213075433 23700736613831349159806575)
  ·
    refine ⟨35551104920747023739709863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23700736613831349159806575 35551104920747023739709863)
    ·
      refine ⟨53326657381120535609564795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35551104920747023739709863 53326657381120535609564795)
      ·
        refine ⟨79989986071680803414347193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53326657381120535609564795 79989986071680803414347193)
        ·
          refine ⟨59992489553760602560760395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79989986071680803414347193 59992489553760602560760395)
          ·
            refine ⟨89988734330640903841140593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59992489553760602560760395 89988734330640903841140593)
            ·
              refine ⟨67491550747980677880855445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89988734330640903841140593 67491550747980677880855445)
              ·
                refine ⟨3163666441311594275665099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67491550747980677880855445 3163666441311594275665099)
                ·
                  refine ⟨4745499661967391413497649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3163666441311594275665099 4745499661967391413497649)
                  ·
                    refine ⟨3559124746475543560123237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4745499661967391413497649 3559124746475543560123237)
                    ·
                      refine ⟨667335889964164417523107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3559124746475543560123237 667335889964164417523107)
                      ·
                        rfl

theorem cell23_1299632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 4].length) (baseStart_1299632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299632 prefixEnd_1299632 := by exact prefixLift 1299632
  have htrace : WordTrace (prefixWord ++ tailWord_1299632) baseStart_1299632 baseEnd_1299632 := by
    simpa [prefixWord, tailWord_1299632, baseEnd_1299632] using wordTrace_append hprefix tailTrace_1299632
  have hstable : (prefixWord ++ tailWord_1299632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299632).length < 2 ^ (prefixWord ++ tailWord_1299632).sum := by decide
  have hdescent : baseEnd_1299632 < baseStart_1299632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299646 : List Nat := [4, 2, 1, 1, 3, 1, 1, 4, 2, 4]
def baseStart_1299646 : Nat := 118140960795 + 1299646 * 2 ^ 59
def prefixEnd_1299646 : Nat := 4983230072969 + 3 ^ 40 * 1299646 * 2
def baseEnd_1299646 : Nat := 222447692897775787582681

theorem tailTrace_1299646 : CollatzResearch.WordTrace tailWord_1299646 prefixEnd_1299646 222447692897775787582681 := by
  unfold tailWord_1299646
  simp only [CollatzResearch.WordTrace]
  refine ⟨5925247981201497338827849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31601322566407985807081861 5925247981201497338827849)
  ·
    refine ⟨4443935985901123004120887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5925247981201497338827849 4443935985901123004120887)
    ·
      refine ⟨6665903978851684506181331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4443935985901123004120887 6665903978851684506181331)
      ·
        refine ⟨9998855968277526759271997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6665903978851684506181331 9998855968277526759271997)
        ·
          refine ⟨3749570988104072534726999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9998855968277526759271997 3749570988104072534726999)
          ·
            refine ⟨5624356482156108802090499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3749570988104072534726999 5624356482156108802090499)
            ·
              refine ⟨8436534723234163203135749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5624356482156108802090499 8436534723234163203135749)
              ·
                refine ⟨1581850260606405600587953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8436534723234163203135749 1581850260606405600587953)
                ·
                  refine ⟨1186387695454804200440965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1581850260606405600587953 1186387695454804200440965)
                  ·
                    refine ⟨222447692897775787582681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1186387695454804200440965 222447692897775787582681)
                    ·
                      rfl

theorem cell23_1299646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_1299646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299646 prefixEnd_1299646 := by exact prefixLift 1299646
  have htrace : WordTrace (prefixWord ++ tailWord_1299646) baseStart_1299646 baseEnd_1299646 := by
    simpa [prefixWord, tailWord_1299646, baseEnd_1299646] using wordTrace_append hprefix tailTrace_1299646
  have hstable : (prefixWord ++ tailWord_1299646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299646).length < 2 ^ (prefixWord ++ tailWord_1299646).sum := by decide
  have hdescent : baseEnd_1299646 < baseStart_1299646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299687 : List Nat := [1, 1, 5, 3, 2, 1, 2, 3, 1, 2, 2]
def baseStart_1299687 : Nat := 118140960795 + 1299687 * 2 ^ 59
def prefixEnd_1299687 : Nat := 4983230072969 + 3 ^ 40 * 1299687 * 2
def baseEnd_1299687 : Nat := 667364131400161702335355

theorem tailTrace_1299687 : CollatzResearch.WordTrace tailWord_1299687 prefixEnd_1299687 667364131400161702335355 := by
  unfold tailWord_1299687
  simp only [CollatzResearch.WordTrace]
  refine ⟨47403479242463442712865315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31602319494975628475243543 47403479242463442712865315)
  ·
    refine ⟨71105218863695164069297973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47403479242463442712865315 71105218863695164069297973)
    ·
      refine ⟨6666114268471421631496685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71105218863695164069297973 6666114268471421631496685)
      ·
        refine ⟨2499792850676783111811257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6666114268471421631496685 2499792850676783111811257)
        ·
          refine ⟨1874844638007587333858443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2499792850676783111811257 1874844638007587333858443)
          ·
            refine ⟨2812266957011381000787665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1874844638007587333858443 2812266957011381000787665)
            ·
              refine ⟨2109200217758535750590749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2812266957011381000787665 2109200217758535750590749)
              ·
                refine ⟨790950081659450906471531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2109200217758535750590749 790950081659450906471531)
                ·
                  refine ⟨1186425122489176359707297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 790950081659450906471531 1186425122489176359707297)
                  ·
                    refine ⟨889818841866882269780473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1186425122489176359707297 889818841866882269780473)
                    ·
                      refine ⟨667364131400161702335355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 889818841866882269780473 667364131400161702335355)
                      ·
                        rfl

theorem cell23_1299687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_1299687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299687 prefixEnd_1299687 := by exact prefixLift 1299687
  have htrace : WordTrace (prefixWord ++ tailWord_1299687) baseStart_1299687 baseEnd_1299687 := by
    simpa [prefixWord, tailWord_1299687, baseEnd_1299687] using wordTrace_append hprefix tailTrace_1299687
  have hstable : (prefixWord ++ tailWord_1299687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299687).length < 2 ^ (prefixWord ++ tailWord_1299687).sum := by decide
  have hdescent : baseEnd_1299687 < baseStart_1299687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299709 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 2, 8, 2]
def baseStart_1299709 : Nat := 118140960795 + 1299709 * 2 ^ 59
def prefixEnd_1299709 : Nat := 4983230072969 + 3 ^ 40 * 1299709 * 2
def baseEnd_1299709 : Nat := 667375427974560616260253

theorem tailTrace_1299709 : CollatzResearch.WordTrace tailWord_1299709 prefixEnd_1299709 667375427974560616260253 := by
  unfold tailWord_1299709
  simp only [CollatzResearch.WordTrace]
  refine ⟨47404281648383740470166181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31602854432255826980110787 47404281648383740470166181)
  ·
    refine ⟨8888302809071951338156159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47404281648383740470166181 8888302809071951338156159)
    ·
      refine ⟨13332454213607927007234239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8888302809071951338156159 13332454213607927007234239)
      ·
        refine ⟨19998681320411890510851359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13332454213607927007234239 19998681320411890510851359)
        ·
          refine ⟨29998021980617835766277039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19998681320411890510851359 29998021980617835766277039)
          ·
            refine ⟨44997032970926753649415559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29998021980617835766277039 44997032970926753649415559)
            ·
              refine ⟨67495549456390130474123339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44997032970926753649415559 67495549456390130474123339)
              ·
                refine ⟨101243324184585195711185009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67495549456390130474123339 101243324184585195711185009)
                ·
                  refine ⟨75932493138438896783388757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101243324184585195711185009 75932493138438896783388757)
                  ·
                    refine ⟨889833903966080821680337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75932493138438896783388757 889833903966080821680337)
                    ·
                      refine ⟨667375427974560616260253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 889833903966080821680337 667375427974560616260253)
                      ·
                        rfl

theorem cell23_1299709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 8, 2].length) (baseStart_1299709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299709 prefixEnd_1299709 := by exact prefixLift 1299709
  have htrace : WordTrace (prefixWord ++ tailWord_1299709) baseStart_1299709 baseEnd_1299709 := by
    simpa [prefixWord, tailWord_1299709, baseEnd_1299709] using wordTrace_append hprefix tailTrace_1299709
  have hstable : (prefixWord ++ tailWord_1299709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299709).length < 2 ^ (prefixWord ++ tailWord_1299709).sum := by decide
  have hdescent : baseEnd_1299709 < baseStart_1299709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299712 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 5]
def baseStart_1299712 : Nat := 118140960795 + 1299712 * 2 ^ 59
def prefixEnd_1299712 : Nat := 4983230072969 + 3 ^ 40 * 1299712 * 2
def baseEnd_1299712 : Nat := 667376968416524104522739

theorem tailTrace_1299712 : CollatzResearch.WordTrace tailWord_1299712 prefixEnd_1299712 667376968416524104522739 := by
  unfold tailWord_1299712
  simp only [CollatzResearch.WordTrace]
  refine ⟨23702195533686435991262695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31602927378248581321683593 23702195533686435991262695)
  ·
    refine ⟨35553293300529653986894043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23702195533686435991262695 35553293300529653986894043)
    ·
      refine ⟨53329939950794480980341065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35553293300529653986894043 53329939950794480980341065)
      ·
        refine ⟨39997454963095860735255799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53329939950794480980341065 39997454963095860735255799)
        ·
          refine ⟨59996182444643791102883699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39997454963095860735255799 59996182444643791102883699)
          ·
            refine ⟨89994273666965686654325549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59996182444643791102883699 89994273666965686654325549)
            ·
              refine ⟨33747852625112132495372081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89994273666965686654325549 33747852625112132495372081)
              ·
                refine ⟨25310889468834099371529061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33747852625112132495372081 25310889468834099371529061)
                ·
                  refine ⟨4745791775406393632161699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25310889468834099371529061 4745791775406393632161699)
                  ·
                    refine ⟨7118687663109590448242549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4745791775406393632161699 7118687663109590448242549)
                    ·
                      refine ⟨667376968416524104522739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7118687663109590448242549 667376968416524104522739)
                      ·
                        rfl

theorem cell23_1299712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_1299712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299712 prefixEnd_1299712 := by exact prefixLift 1299712
  have htrace : WordTrace (prefixWord ++ tailWord_1299712) baseStart_1299712 baseEnd_1299712 := by
    simpa [prefixWord, tailWord_1299712, baseEnd_1299712] using wordTrace_append hprefix tailTrace_1299712
  have hstable : (prefixWord ++ tailWord_1299712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299712).length < 2 ^ (prefixWord ++ tailWord_1299712).sum := by decide
  have hdescent : baseEnd_1299712 < baseStart_1299712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299720 : List Nat := [2, 1, 3, 2, 4, 1, 3, 1, 2, 1, 3]
def baseStart_1299720 : Nat := 118140960795 + 1299720 * 2 ^ 59
def prefixEnd_1299720 : Nat := 4983230072969 + 3 ^ 40 * 1299720 * 2
def baseEnd_1299720 : Nat := 667381076261760073222703

theorem tailTrace_1299720 : CollatzResearch.WordTrace tailWord_1299720 prefixEnd_1299720 667381076261760073222703 := by
  unfold tailWord_1299720
  simp only [CollatzResearch.WordTrace]
  refine ⟨23702341425671944674408307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31603121900895926232544409 23702341425671944674408307)
  ·
    refine ⟨35553512138507917011612461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23702341425671944674408307 35553512138507917011612461)
    ·
      refine ⟨13332567051940468879354673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35553512138507917011612461 13332567051940468879354673)
      ·
        refine ⟨9999425288955351659516005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13332567051940468879354673 9999425288955351659516005)
        ·
          refine ⟨1874892241679128436159251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9999425288955351659516005 1874892241679128436159251)
          ·
            refine ⟨2812338362518692654238877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1874892241679128436159251 2812338362518692654238877)
            ·
              refine ⟨1054626885944509745339579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2812338362518692654238877 1054626885944509745339579)
              ·
                refine ⟨1581940328916764618009369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1054626885944509745339579 1581940328916764618009369)
                ·
                  refine ⟨1186455246687573463507027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1581940328916764618009369 1186455246687573463507027)
                  ·
                    refine ⟨1779682870031360195260541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1186455246687573463507027 1779682870031360195260541)
                    ·
                      refine ⟨667381076261760073222703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1779682870031360195260541 667381076261760073222703)
                      ·
                        rfl

theorem cell23_1299720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_1299720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299720 prefixEnd_1299720 := by exact prefixLift 1299720
  have htrace : WordTrace (prefixWord ++ tailWord_1299720) baseStart_1299720 baseEnd_1299720 := by
    simpa [prefixWord, tailWord_1299720, baseEnd_1299720] using wordTrace_append hprefix tailTrace_1299720
  have hstable : (prefixWord ++ tailWord_1299720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299720).length < 2 ^ (prefixWord ++ tailWord_1299720).sum := by decide
  have hdescent : baseEnd_1299720 < baseStart_1299720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299746 : List Nat := [3, 3, 1, 1, 4, 1, 1, 1, 2, 1, 5]
def baseStart_1299746 : Nat := 118140960795 + 1299746 * 2 ^ 59
def prefixEnd_1299746 : Nat := 4983230072969 + 3 ^ 40 * 1299746 * 2
def baseEnd_1299746 : Nat := 667394426758776971497583

theorem tailTrace_1299746 : CollatzResearch.WordTrace tailWord_1299746 prefixEnd_1299746 667394426758776971497583 := by
  unfold tailWord_1299746
  simp only [CollatzResearch.WordTrace]
  refine ⟨11851407787312423947315773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31603754099499797192842061 11851407787312423947315773)
  ·
    refine ⟨4444277920242158980243415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11851407787312423947315773 4444277920242158980243415)
    ·
      refine ⟨6666416880363238470365123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4444277920242158980243415 6666416880363238470365123)
      ·
        refine ⟨9999625320544857705547685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6666416880363238470365123 9999625320544857705547685)
        ·
          refine ⟨1874929747602160819790191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9999625320544857705547685 1874929747602160819790191)
          ·
            refine ⟨2812394621403241229685287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1874929747602160819790191 2812394621403241229685287)
            ·
              refine ⟨4218591932104861844527931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2812394621403241229685287 4218591932104861844527931)
              ·
                refine ⟨6327887898157292766791897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4218591932104861844527931 6327887898157292766791897)
                ·
                  refine ⟨4745915923617969575093923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6327887898157292766791897 4745915923617969575093923)
                  ·
                    refine ⟨7118873885426954362640885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4745915923617969575093923 7118873885426954362640885)
                    ·
                      refine ⟨667394426758776971497583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7118873885426954362640885 667394426758776971497583)
                      ·
                        rfl

theorem cell23_1299746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_1299746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299746 prefixEnd_1299746 := by exact prefixLift 1299746
  have htrace : WordTrace (prefixWord ++ tailWord_1299746) baseStart_1299746 baseEnd_1299746 := by
    simpa [prefixWord, tailWord_1299746, baseEnd_1299746] using wordTrace_append hprefix tailTrace_1299746
  have hstable : (prefixWord ++ tailWord_1299746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299746).length < 2 ^ (prefixWord ++ tailWord_1299746).sum := by decide
  have hdescent : baseEnd_1299746 < baseStart_1299746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299777 : List Nat := [1, 2, 5, 2, 1, 1, 4, 1, 2, 2, 2]
def baseStart_1299777 : Nat := 118140960795 + 1299777 * 2 ^ 59
def prefixEnd_1299777 : Nat := 4983230072969 + 3 ^ 40 * 1299777 * 2
def baseEnd_1299777 : Nat := 667410344659066350209941

theorem tailTrace_1299777 : CollatzResearch.WordTrace tailWord_1299777 prefixEnd_1299777 667410344659066350209941 := by
  unfold tailWord_1299777
  simp only [CollatzResearch.WordTrace]
  refine ⟨47406761812137388083641585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31604507874758258722427723 47406761812137388083641585)
  ·
    refine ⟨35555071359103041062731189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47406761812137388083641585 35555071359103041062731189)
    ·
      refine ⟨3333287939915910099631049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35555071359103041062731189 3333287939915910099631049)
      ·
        refine ⟨2499965954936932574723287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3333287939915910099631049 2499965954936932574723287)
        ·
          refine ⟨3749948932405398862084931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2499965954936932574723287 3749948932405398862084931)
          ·
            refine ⟨5624923398608098293127397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3749948932405398862084931 5624923398608098293127397)
            ·
              refine ⟨1054673137239018429961387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5624923398608098293127397 1054673137239018429961387)
              ·
                refine ⟨1582009705858527644942081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1054673137239018429961387 1582009705858527644942081)
                ·
                  refine ⟨1186507279393895733706561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1582009705858527644942081 1186507279393895733706561)
                  ·
                    refine ⟨889880459545421800279921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1186507279393895733706561 889880459545421800279921)
                    ·
                      refine ⟨667410344659066350209941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 889880459545421800279921 667410344659066350209941)
                      ·
                        rfl

theorem cell23_1299777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_1299777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299777 prefixEnd_1299777 := by exact prefixLift 1299777
  have htrace : WordTrace (prefixWord ++ tailWord_1299777) baseStart_1299777 baseEnd_1299777 := by
    simpa [prefixWord, tailWord_1299777, baseEnd_1299777] using wordTrace_append hprefix tailTrace_1299777
  have hstable : (prefixWord ++ tailWord_1299777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299777).length < 2 ^ (prefixWord ++ tailWord_1299777).sum := by decide
  have hdescent : baseEnd_1299777 < baseStart_1299777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299796 : List Nat := [2, 4, 1, 1, 2, 1, 4, 1, 2, 5]
def baseStart_1299796 : Nat := 118140960795 + 1299796 * 2 ^ 59
def prefixEnd_1299796 : Nat := 4983230072969 + 3 ^ 40 * 1299796 * 2
def baseEnd_1299796 : Nat := 222473366930500591957451

theorem tailTrace_1299796 : CollatzResearch.WordTrace tailWord_1299796 prefixEnd_1299796 222473366930500591957451 := by
  unfold tailWord_1299796
  simp only [CollatzResearch.WordTrace]
  refine ⟨23703727399534277164291621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31604969866045702885722161 23703727399534277164291621)
  ·
    refine ⟨4444448887412676968304679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23703727399534277164291621 4444448887412676968304679)
    ·
      refine ⟨6666673331119015452457019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4444448887412676968304679 6666673331119015452457019)
      ·
        refine ⟨10000009996678523178685529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6666673331119015452457019 10000009996678523178685529)
        ·
          refine ⟨7500007497508892384014147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10000009996678523178685529 7500007497508892384014147)
          ·
            refine ⟨11250011246263338576021221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7500007497508892384014147 11250011246263338576021221)
            ·
              refine ⟨2109377108674375983003979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11250011246263338576021221 2109377108674375983003979)
              ·
                refine ⟨3164065663011563974505969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2109377108674375983003979 3164065663011563974505969)
                ·
                  refine ⟨2373049247258672980879477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3164065663011563974505969 2373049247258672980879477)
                  ·
                    refine ⟨222473366930500591957451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2373049247258672980879477 222473366930500591957451)
                    ·
                      rfl

theorem cell23_1299796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_1299796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299796 prefixEnd_1299796 := by exact prefixLift 1299796
  have htrace : WordTrace (prefixWord ++ tailWord_1299796) baseStart_1299796 baseEnd_1299796 := by
    simpa [prefixWord, tailWord_1299796, baseEnd_1299796] using wordTrace_append hprefix tailTrace_1299796
  have hstable : (prefixWord ++ tailWord_1299796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299796).length < 2 ^ (prefixWord ++ tailWord_1299796).sum := by decide
  have hdescent : baseEnd_1299796 < baseStart_1299796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299826 : List Nat := [3, 2, 1, 2, 1, 2, 2, 3, 3, 4]
def baseStart_1299826 : Nat := 118140960795 + 1299826 * 2 ^ 59
def prefixEnd_1299826 : Nat := 4983230072969 + 3 ^ 40 * 1299826 * 2
def baseEnd_1299826 : Nat := 222478501737045552832405

theorem tailTrace_1299826 : CollatzResearch.WordTrace tailWord_1299826 prefixEnd_1299826 222478501737045552832405 := by
  unfold tailWord_1299826
  simp only [CollatzResearch.WordTrace]
  refine ⟨11852137247239967363043833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31605699325973246301450221 11852137247239967363043833)
  ·
    refine ⟨8889102935429975522282875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11852137247239967363043833 8889102935429975522282875)
    ·
      refine ⟨13333654403144963283424313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8889102935429975522282875 13333654403144963283424313)
      ·
        refine ⟨10000240802358722462568235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13333654403144963283424313 10000240802358722462568235)
        ·
          refine ⟨15000361203538083693852353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10000240802358722462568235 15000361203538083693852353)
          ·
            refine ⟨11250270902653562770389265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15000361203538083693852353 11250270902653562770389265)
            ·
              refine ⟨8437703176990172077791949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11250270902653562770389265 8437703176990172077791949)
              ·
                refine ⟨3164138691371314529171981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8437703176990172077791949 3164138691371314529171981)
                ·
                  refine ⟨1186552009264242948439493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3164138691371314529171981 1186552009264242948439493)
                  ·
                    refine ⟨222478501737045552832405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1186552009264242948439493 222478501737045552832405)
                    ·
                      rfl

theorem cell23_1299826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_1299826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299826 prefixEnd_1299826 := by exact prefixLift 1299826
  have htrace : WordTrace (prefixWord ++ tailWord_1299826) baseStart_1299826 baseEnd_1299826 := by
    simpa [prefixWord, tailWord_1299826, baseEnd_1299826] using wordTrace_append hprefix tailTrace_1299826
  have hstable : (prefixWord ++ tailWord_1299826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299826).length < 2 ^ (prefixWord ++ tailWord_1299826).sum := by decide
  have hdescent : baseEnd_1299826 < baseStart_1299826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299860 : List Nat := [2, 4, 2, 1, 2, 1, 1, 5, 1, 4]
def baseStart_1299860 : Nat := 118140960795 + 1299860 * 2 ^ 59
def prefixEnd_1299860 : Nat := 4983230072969 + 3 ^ 40 * 1299860 * 2
def baseEnd_1299860 : Nat := 222484321184463175157353

theorem tailTrace_1299860 : CollatzResearch.WordTrace tailWord_1299860 prefixEnd_1299860 222484321184463175157353 := by
  unfold tailWord_1299860
  simp only [CollatzResearch.WordTrace]
  refine ⟨23704894535418346629456517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31606526047224462172608689 23704894535418346629456517)
  ·
    refine ⟨4444667725390939993023097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23704894535418346629456517 4444667725390939993023097)
    ·
      refine ⟨3333500794043204994767323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4444667725390939993023097 3333500794043204994767323)
      ·
        refine ⟨5000251191064807492150985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3333500794043204994767323 5000251191064807492150985)
        ·
          refine ⟨3750188393298605619113239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5000251191064807492150985 3750188393298605619113239)
          ·
            refine ⟨5625282589947908428669859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3750188393298605619113239 5625282589947908428669859)
            ·
              refine ⟨8437923884921862643004789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5625282589947908428669859 8437923884921862643004789)
              ·
                refine ⟨791055364211424622781699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8437923884921862643004789 791055364211424622781699)
                ·
                  refine ⟨1186583046317136934172549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 791055364211424622781699 1186583046317136934172549)
                  ·
                    refine ⟨222484321184463175157353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1186583046317136934172549 222484321184463175157353)
                    ·
                      rfl

theorem cell23_1299860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_1299860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299860 prefixEnd_1299860 := by exact prefixLift 1299860
  have htrace : WordTrace (prefixWord ++ tailWord_1299860) baseStart_1299860 baseEnd_1299860 := by
    simpa [prefixWord, tailWord_1299860, baseEnd_1299860] using wordTrace_append hprefix tailTrace_1299860
  have hstable : (prefixWord ++ tailWord_1299860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299860).length < 2 ^ (prefixWord ++ tailWord_1299860).sum := by decide
  have hdescent : baseEnd_1299860 < baseStart_1299860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299893 : List Nat := [1, 3, 3, 2, 2, 1, 1, 2, 1, 5, 2]
def baseStart_1299893 : Nat := 118140960795 + 1299893 * 2 ^ 59
def prefixEnd_1299893 : Nat := 4983230072969 + 3 ^ 40 * 1299893 * 2
def baseEnd_1299893 : Nat := 667469908414987896359407

theorem tailTrace_1299893 : CollatzResearch.WordTrace tailWord_1299893 prefixEnd_1299893 667469908414987896359407 := by
  unfold tailWord_1299893
  simp only [CollatzResearch.WordTrace]
  refine ⟨47410992679717139894864333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31607328453144759929909555 47410992679717139894864333)
  ·
    refine ⟨17779122254893927460574125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47410992679717139894864333 17779122254893927460574125)
    ·
      refine ⟨6667170845585222797715297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17779122254893927460574125 6667170845585222797715297)
      ·
        refine ⟨5000378134188917098286473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6667170845585222797715297 5000378134188917098286473)
        ·
          refine ⟨3750283600641687823714855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5000378134188917098286473 3750283600641687823714855)
          ·
            refine ⟨5625425400962531735572283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3750283600641687823714855 5625425400962531735572283)
            ·
              refine ⟨8438138101443797603358425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5625425400962531735572283 8438138101443797603358425)
              ·
                refine ⟨6328603576082848202518819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8438138101443797603358425 6328603576082848202518819)
                ·
                  refine ⟨9492905364124272303778229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6328603576082848202518819 9492905364124272303778229)
                  ·
                    refine ⟨889959877886650528479209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9492905364124272303778229 889959877886650528479209)
                    ·
                      refine ⟨667469908414987896359407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 889959877886650528479209 667469908414987896359407)
                      ·
                        rfl

theorem cell23_1299893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_1299893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299893 prefixEnd_1299893 := by exact prefixLift 1299893
  have htrace : WordTrace (prefixWord ++ tailWord_1299893) baseStart_1299893 baseEnd_1299893 := by
    simpa [prefixWord, tailWord_1299893, baseEnd_1299893] using wordTrace_append hprefix tailTrace_1299893
  have hstable : (prefixWord ++ tailWord_1299893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299893).length < 2 ^ (prefixWord ++ tailWord_1299893).sum := by decide
  have hdescent : baseEnd_1299893 < baseStart_1299893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299929 : List Nat := [1, 2, 1, 2, 4, 2, 11]
def baseStart_1299929 : Nat := 118140960795 + 1299929 * 2 ^ 59
def prefixEnd_1299929 : Nat := 4983230072969 + 3 ^ 40 * 1299929 * 2
def baseEnd_1299929 : Nat := 8240597453315429080361

theorem tailTrace_1299929 : CollatzResearch.WordTrace tailWord_1299929 prefixEnd_1299929 8240597453315429080361 := by
  unfold tailWord_1299929
  simp only [CollatzResearch.WordTrace]
  refine ⟨47412305707586718043174841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31608203805057812028783227 47412305707586718043174841)
  ·
    refine ⟨35559229280690038532381131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47412305707586718043174841 35559229280690038532381131)
    ·
      refine ⟨53338843921035057798571697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35559229280690038532381131 53338843921035057798571697)
      ·
        refine ⟨40004132940776293348928773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53338843921035057798571697 40004132940776293348928773)
        ·
          refine ⟨7500774926395555002924145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40004132940776293348928773 7500774926395555002924145)
          ·
            refine ⟨5625581194796666252193109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7500774926395555002924145 5625581194796666252193109)
            ·
              refine ⟨8240597453315429080361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5625581194796666252193109 8240597453315429080361)
              ·
                rfl

theorem cell23_1299929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 11].length) (baseStart_1299929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299929 prefixEnd_1299929 := by exact prefixLift 1299929
  have htrace : WordTrace (prefixWord ++ tailWord_1299929) baseStart_1299929 baseEnd_1299929 := by
    simpa [prefixWord, tailWord_1299929, baseEnd_1299929] using wordTrace_append hprefix tailTrace_1299929
  have hstable : (prefixWord ++ tailWord_1299929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299929).length < 2 ^ (prefixWord ++ tailWord_1299929).sum := by decide
  have hdescent : baseEnd_1299929 < baseStart_1299929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299933 : List Nat := [1, 4, 3, 1, 1, 2, 2, 1, 4, 4]
def baseStart_1299933 : Nat := 118140960795 + 1299933 * 2 ^ 59
def prefixEnd_1299933 : Nat := 4983230072969 + 3 ^ 40 * 1299933 * 2
def baseEnd_1299933 : Nat := 222496815880389246619741

theorem tailTrace_1299933 : CollatzResearch.WordTrace tailWord_1299933 prefixEnd_1299933 222496815880389246619741 := by
  unfold tailWord_1299933
  simp only [CollatzResearch.WordTrace]
  refine ⟨47412451599572226726320453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31608301066381484484213635 47412451599572226726320453)
  ·
    refine ⟨8889834674919792511185085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47412451599572226726320453 8889834674919792511185085)
    ·
      refine ⟨3333688003094922191694407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8889834674919792511185085 3333688003094922191694407)
      ·
        refine ⟨5000532004642383287541611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3333688003094922191694407 5000532004642383287541611)
        ·
          refine ⟨7500798006963574931312417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5000532004642383287541611 7500798006963574931312417)
          ·
            refine ⟨5625598505222681198484313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7500798006963574931312417 5625598505222681198484313)
            ·
              refine ⟨4219198878917010898863235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5625598505222681198484313 4219198878917010898863235)
              ·
                refine ⟨6328798318375516348294853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4219198878917010898863235 6328798318375516348294853)
                ·
                  refine ⟨1186649684695409315305285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6328798318375516348294853 1186649684695409315305285)
                  ·
                    refine ⟨222496815880389246619741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1186649684695409315305285 222496815880389246619741)
                    ·
                      rfl

theorem cell23_1299933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_1299933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299933 prefixEnd_1299933 := by exact prefixLift 1299933
  have htrace : WordTrace (prefixWord ++ tailWord_1299933) baseStart_1299933 baseEnd_1299933 := by
    simpa [prefixWord, tailWord_1299933, baseEnd_1299933] using wordTrace_append hprefix tailTrace_1299933
  have hstable : (prefixWord ++ tailWord_1299933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299933).length < 2 ^ (prefixWord ++ tailWord_1299933).sum := by decide
  have hdescent : baseEnd_1299933 < baseStart_1299933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299957 : List Nat := [1, 3, 5, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_1299957 : Nat := 118140960795 + 1299957 * 2 ^ 59
def prefixEnd_1299957 : Nat := 4983230072969 + 3 ^ 40 * 1299957 * 2
def baseEnd_1299957 : Nat := 667502771176875645959113

theorem tailTrace_1299957 : CollatzResearch.WordTrace tailWord_1299957 prefixEnd_1299957 667502771176875645959113 := by
  unfold tailWord_1299957
  simp only [CollatzResearch.WordTrace]
  refine ⟨47413326951485278825194125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31608884634323519216796083 47413326951485278825194125)
  ·
    refine ⟨17779997606806979559447797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47413326951485278825194125 17779997606806979559447797)
    ·
      refine ⟨1666874775638154333698231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17779997606806979559447797 1666874775638154333698231)
      ·
        refine ⟨2500312163457231500547347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1666874775638154333698231 2500312163457231500547347)
        ·
          refine ⟨3750468245185847250821021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2500312163457231500547347 3750468245185847250821021)
          ·
            refine ⟨1406425591944692719057883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3750468245185847250821021 1406425591944692719057883)
            ·
              refine ⟨2109638387917039078586825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1406425591944692719057883 2109638387917039078586825)
              ·
                refine ⟨1582228790937779308940119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2109638387917039078586825 1582228790937779308940119)
                ·
                  refine ⟨2373343186406668963410179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1582228790937779308940119 2373343186406668963410179)
                  ·
                    refine ⟨3560014779610003445115269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2373343186406668963410179 3560014779610003445115269)
                    ·
                      refine ⟨667502771176875645959113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3560014779610003445115269 667502771176875645959113)
                      ·
                        rfl

theorem cell23_1299957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_1299957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299957 prefixEnd_1299957 := by exact prefixLift 1299957
  have htrace : WordTrace (prefixWord ++ tailWord_1299957) baseStart_1299957 baseEnd_1299957 := by
    simpa [prefixWord, tailWord_1299957, baseEnd_1299957] using wordTrace_append hprefix tailTrace_1299957
  have hstable : (prefixWord ++ tailWord_1299957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299957).length < 2 ^ (prefixWord ++ tailWord_1299957).sum := by decide
  have hdescent : baseEnd_1299957 < baseStart_1299957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299959 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 4, 7]
def baseStart_1299959 : Nat := 118140960795 + 1299959 * 2 ^ 59
def prefixEnd_1299959 : Nat := 4983230072969 + 3 ^ 40 * 1299959 * 2
def baseEnd_1299959 : Nat := 222501266046061546044701

theorem tailTrace_1299959 : CollatzResearch.WordTrace tailWord_1299959 prefixEnd_1299959 222501266046061546044701 := by
  unfold tailWord_1299959
  simp only [CollatzResearch.WordTrace]
  refine ⟨47413399897478033166766931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31608933264985355444511287 47413399897478033166766931)
  ·
    refine ⟨71120099846217049750150397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47413399897478033166766931 71120099846217049750150397)
    ·
      refine ⟨26670037442331393656306399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71120099846217049750150397 26670037442331393656306399)
      ·
        refine ⟨40005056163497090484459599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26670037442331393656306399 40005056163497090484459599)
        ·
          refine ⟨60007584245245635726689399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40005056163497090484459599 60007584245245635726689399)
          ·
            refine ⟨90011376367868453590034099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60007584245245635726689399 90011376367868453590034099)
            ·
              refine ⟨135017064551802680385051149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90011376367868453590034099 135017064551802680385051149)
              ·
                refine ⟨50631399206926005144394181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135017064551802680385051149 50631399206926005144394181)
                ·
                  refine ⟨9493387351298625964573909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50631399206926005144394181 9493387351298625964573909)
                  ·
                    refine ⟨222501266046061546044701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9493387351298625964573909 222501266046061546044701)
                    ·
                      rfl

theorem cell23_1299959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_1299959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299959 prefixEnd_1299959 := by exact prefixLift 1299959
  have htrace : WordTrace (prefixWord ++ tailWord_1299959) baseStart_1299959 baseEnd_1299959 := by
    simpa [prefixWord, tailWord_1299959, baseEnd_1299959] using wordTrace_append hprefix tailTrace_1299959
  have hstable : (prefixWord ++ tailWord_1299959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299959).length < 2 ^ (prefixWord ++ tailWord_1299959).sum := by decide
  have hdescent : baseEnd_1299959 < baseStart_1299959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299960 : List Nat := [2, 1, 2, 1, 1, 7, 1, 2, 1, 2, 3]
def baseStart_1299960 : Nat := 118140960795 + 1299960 * 2 ^ 59
def prefixEnd_1299960 : Nat := 4983230072969 + 3 ^ 40 * 1299960 * 2
def baseEnd_1299960 : Nat := 667504311618839134221599

theorem tailTrace_1299960 : CollatzResearch.WordTrace tailWord_1299960 prefixEnd_1299960 667504311618839134221599 := by
  unfold tailWord_1299960
  simp only [CollatzResearch.WordTrace]
  refine ⟨23706718185237205168776667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31608957580316273558368889 23706718185237205168776667)
  ·
    refine ⟨35560077277855807753165001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23706718185237205168776667 35560077277855807753165001)
    ·
      refine ⟨26670057958391855814873751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35560077277855807753165001 26670057958391855814873751)
      ·
        refine ⟨40005086937587783722310627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26670057958391855814873751 40005086937587783722310627)
        ·
          refine ⟨60007630406381675583465941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40005086937587783722310627 60007630406381675583465941)
          ·
            refine ⟨1406428837649570521487483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 60007630406381675583465941 1406428837649570521487483)
            ·
              refine ⟨2109643256474355782231225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1406428837649570521487483 2109643256474355782231225)
              ·
                refine ⟨1582232442355766836673419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2109643256474355782231225 1582232442355766836673419)
                ·
                  refine ⟨2373348663533650255010129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1582232442355766836673419 2373348663533650255010129)
                  ·
                    refine ⟨1780011497650237691257597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2373348663533650255010129 1780011497650237691257597)
                    ·
                      refine ⟨667504311618839134221599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1780011497650237691257597 667504311618839134221599)
                      ·
                        rfl

theorem cell23_1299960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 1, 2, 3].length) (baseStart_1299960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299960 prefixEnd_1299960 := by exact prefixLift 1299960
  have htrace : WordTrace (prefixWord ++ tailWord_1299960) baseStart_1299960 baseEnd_1299960 := by
    simpa [prefixWord, tailWord_1299960, baseEnd_1299960] using wordTrace_append hprefix tailTrace_1299960
  have hstable : (prefixWord ++ tailWord_1299960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299960).length < 2 ^ (prefixWord ++ tailWord_1299960).sum := by decide
  have hdescent : baseEnd_1299960 < baseStart_1299960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299970 : List Nat := [3, 4, 1, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1299970 : Nat := 118140960795 + 1299970 * 2 ^ 59
def prefixEnd_1299970 : Nat := 4983230072969 + 3 ^ 40 * 1299970 * 2
def baseEnd_1299970 : Nat := 667509446425384095096553

theorem tailTrace_1299970 : CollatzResearch.WordTrace tailWord_1299970 prefixEnd_1299970 667509446425384095096553 := by
  unfold tailWord_1299970
  simp only [CollatzResearch.WordTrace]
  refine ⟨11853450275109545511354341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31609200733625454696944909 11853450275109545511354341)
  ·
    refine ⟨2222521926583039783378939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11853450275109545511354341 2222521926583039783378939)
    ·
      refine ⟨3333782889874559675068409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2222521926583039783378939 3333782889874559675068409)
      ·
        refine ⟨2500337167405919756301307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3333782889874559675068409 2500337167405919756301307)
        ·
          refine ⟨3750505751108879634451961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2500337167405919756301307 3750505751108879634451961)
          ·
            refine ⟨2812879313331659725838971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3750505751108879634451961 2812879313331659725838971)
            ·
              refine ⟨4219318969997489588758457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2812879313331659725838971 4219318969997489588758457)
              ·
                refine ⟨3164489227498117191568843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4219318969997489588758457 3164489227498117191568843)
                ·
                  refine ⟨4746733841247175787353265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3164489227498117191568843 4746733841247175787353265)
                  ·
                    refine ⟨3560050380935381840514949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4746733841247175787353265 3560050380935381840514949)
                    ·
                      refine ⟨667509446425384095096553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3560050380935381840514949 667509446425384095096553)
                      ·
                        rfl

theorem cell23_1299970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1299970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299970 prefixEnd_1299970 := by exact prefixLift 1299970
  have htrace : WordTrace (prefixWord ++ tailWord_1299970) baseStart_1299970 baseEnd_1299970 := by
    simpa [prefixWord, tailWord_1299970, baseEnd_1299970] using wordTrace_append hprefix tailTrace_1299970
  have hstable : (prefixWord ++ tailWord_1299970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299970).length < 2 ^ (prefixWord ++ tailWord_1299970).sum := by decide
  have hdescent : baseEnd_1299970 < baseStart_1299970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299996 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_1299996 : Nat := 118140960795 + 1299996 * 2 ^ 59
def prefixEnd_1299996 : Nat := 4983230072969 + 3 ^ 40 * 1299996 * 2
def baseEnd_1299996 : Nat := 667522796922400993371433

theorem tailTrace_1299996 : CollatzResearch.WordTrace tailWord_1299996 prefixEnd_1299996 667522796922400993371433 := by
  unfold tailWord_1299996
  simp only [CollatzResearch.WordTrace]
  refine ⟨23707374699171994242931921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31609832932229325657242561 23707374699171994242931921)
  ·
    refine ⟨17780531024378995682198941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23707374699171994242931921 17780531024378995682198941)
    ·
      refine ⟨6667699134142123380824603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17780531024378995682198941 6667699134142123380824603)
      ·
        refine ⟨10001548701213185071236905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6667699134142123380824603 10001548701213185071236905)
        ·
          refine ⟨7501161525909888803427679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10001548701213185071236905 7501161525909888803427679)
          ·
            refine ⟨11251742288864833205141519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7501161525909888803427679 11251742288864833205141519)
            ·
              refine ⟨16877613433297249807712279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11251742288864833205141519 16877613433297249807712279)
              ·
                refine ⟨25316420149945874711568419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16877613433297249807712279 25316420149945874711568419)
                ·
                  refine ⟨37974630224918812067352629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25316420149945874711568419 37974630224918812067352629)
                  ·
                    refine ⟨3560121583586138631314309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37974630224918812067352629 3560121583586138631314309)
                    ·
                      refine ⟨667522796922400993371433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3560121583586138631314309 667522796922400993371433)
                      ·
                        rfl

theorem cell23_1299996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_1299996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1299996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1299996 prefixEnd_1299996 := by exact prefixLift 1299996
  have htrace : WordTrace (prefixWord ++ tailWord_1299996) baseStart_1299996 baseEnd_1299996 := by
    simpa [prefixWord, tailWord_1299996, baseEnd_1299996] using wordTrace_append hprefix tailTrace_1299996
  have hstable : (prefixWord ++ tailWord_1299996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299996).length < 2 ^ (prefixWord ++ tailWord_1299996).sum := by decide
  have hdescent : baseEnd_1299996 < baseStart_1299996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300000 : List Nat := [2, 1, 1, 6, 1, 1, 1, 2, 3, 3, 2]
def baseStart_1300000 : Nat := 118140960795 + 1300000 * 2 ^ 59
def prefixEnd_1300000 : Nat := 4983230072969 + 3 ^ 40 * 1300000 * 2
def baseEnd_1300000 : Nat := 667524850845018977721415

theorem tailTrace_1300000 : CollatzResearch.WordTrace tailWord_1300000 prefixEnd_1300000 667524850845018977721415 := by
  unfold tailWord_1300000
  simp only [CollatzResearch.WordTrace]
  refine ⟨23707447645164748584504727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31609930193552998112672969 23707447645164748584504727)
  ·
    refine ⟨35561171467747122876757091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23707447645164748584504727 35561171467747122876757091)
    ·
      refine ⟨53341757201620684315135637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35561171467747122876757091 53341757201620684315135637)
      ·
        refine ⟨2500394868825969577271983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53341757201620684315135637 2500394868825969577271983)
        ·
          refine ⟨3750592303238954365907975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2500394868825969577271983 3750592303238954365907975)
          ·
            refine ⟨5625888454858431548861963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3750592303238954365907975 5625888454858431548861963)
            ·
              refine ⟨8438832682287647323292945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5625888454858431548861963 8438832682287647323292945)
              ·
                refine ⟨6329124511715735492469709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8438832682287647323292945 6329124511715735492469709)
                ·
                  refine ⟨2373421691893400809676141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6329124511715735492469709 2373421691893400809676141)
                  ·
                    refine ⟨890033134460025303628553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2373421691893400809676141 890033134460025303628553)
                    ·
                      refine ⟨667524850845018977721415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 890033134460025303628553 667524850845018977721415)
                      ·
                        rfl

theorem cell23_1300000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_1300000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300000 prefixEnd_1300000 := by exact prefixLift 1300000
  have htrace : WordTrace (prefixWord ++ tailWord_1300000) baseStart_1300000 baseEnd_1300000 := by
    simpa [prefixWord, tailWord_1300000, baseEnd_1300000] using wordTrace_append hprefix tailTrace_1300000
  have hstable : (prefixWord ++ tailWord_1300000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300000).length < 2 ^ (prefixWord ++ tailWord_1300000).sum := by decide
  have hdescent : baseEnd_1300000 < baseStart_1300000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300016 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 3]
def baseStart_1300016 : Nat := 118140960795 + 1300016 * 2 ^ 59
def prefixEnd_1300016 : Nat := 4983230072969 + 3 ^ 40 * 1300016 * 2
def baseEnd_1300016 : Nat := 667533066535490915121341

theorem tailTrace_1300016 : CollatzResearch.WordTrace tailWord_1300016 prefixEnd_1300016 667533066535490915121341 := by
  unfold tailWord_1300016
  simp only [CollatzResearch.WordTrace]
  refine ⟨23707739429135765950795951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31610319238847687934394601 23707739429135765950795951)
  ·
    refine ⟨35561609143703648926193927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23707739429135765950795951 35561609143703648926193927)
    ·
      refine ⟨53342413715555473389290891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35561609143703648926193927 53342413715555473389290891)
      ·
        refine ⟨80013620573333210083936337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53342413715555473389290891 80013620573333210083936337)
        ·
          refine ⟨60010215429999907562952253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80013620573333210083936337 60010215429999907562952253)
          ·
            refine ⟨22503830786249965336107095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60010215429999907562952253 22503830786249965336107095)
            ·
              refine ⟨33755746179374948004160643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22503830786249965336107095 33755746179374948004160643)
              ·
                refine ⟨50633619269062422006240965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33755746179374948004160643 50633619269062422006240965)
                ·
                  refine ⟨9493803612949204126170181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50633619269062422006240965 9493803612949204126170181)
                  ·
                    refine ⟨1780088177427975773656909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9493803612949204126170181 1780088177427975773656909)
                    ·
                      refine ⟨667533066535490915121341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1780088177427975773656909 667533066535490915121341)
                      ·
                        rfl

theorem cell23_1300016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 3].length) (baseStart_1300016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300016 prefixEnd_1300016 := by exact prefixLift 1300016
  have htrace : WordTrace (prefixWord ++ tailWord_1300016) baseStart_1300016 baseEnd_1300016 := by
    simpa [prefixWord, tailWord_1300016, baseEnd_1300016] using wordTrace_append hprefix tailTrace_1300016
  have hstable : (prefixWord ++ tailWord_1300016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300016).length < 2 ^ (prefixWord ++ tailWord_1300016).sum := by decide
  have hdescent : baseEnd_1300016 < baseStart_1300016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300026 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4]
def baseStart_1300026 : Nat := 118140960795 + 1300026 * 2 ^ 59
def prefixEnd_1300026 : Nat := 4983230072969 + 3 ^ 40 * 1300026 * 2
def baseEnd_1300026 : Nat := 667538201342035875996295

theorem tailTrace_1300026 : CollatzResearch.WordTrace tailWord_1300026 prefixEnd_1300026 667538201342035875996295 := by
  unfold tailWord_1300026
  simp only [CollatzResearch.WordTrace]
  refine ⟨11853960897058825902363983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31610562392156869072970621 11853960897058825902363983)
  ·
    refine ⟨17780941345588238853545975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11853960897058825902363983 17780941345588238853545975)
    ·
      refine ⟨26671412018382358280318963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17780941345588238853545975 26671412018382358280318963)
      ·
        refine ⟨40007118027573537420478445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26671412018382358280318963 40007118027573537420478445)
        ·
          refine ⟨15002669260340076532679417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40007118027573537420478445 15002669260340076532679417)
          ·
            refine ⟨11252001945255057399509563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15002669260340076532679417 11252001945255057399509563)
            ·
              refine ⟨16878002917882586099264345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11252001945255057399509563 16878002917882586099264345)
              ·
                refine ⟨12658502188411939574448259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16878002917882586099264345 12658502188411939574448259)
                ·
                  refine ⟨18987753282617909361672389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12658502188411939574448259 18987753282617909361672389)
                  ·
                    refine ⟨3560203740490858005313573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18987753282617909361672389 3560203740490858005313573)
                    ·
                      refine ⟨667538201342035875996295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3560203740490858005313573 667538201342035875996295)
                      ·
                        rfl

theorem cell23_1300026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_1300026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300026 prefixEnd_1300026 := by exact prefixLift 1300026
  have htrace : WordTrace (prefixWord ++ tailWord_1300026) baseStart_1300026 baseEnd_1300026 := by
    simpa [prefixWord, tailWord_1300026, baseEnd_1300026] using wordTrace_append hprefix tailTrace_1300026
  have hstable : (prefixWord ++ tailWord_1300026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300026).length < 2 ^ (prefixWord ++ tailWord_1300026).sum := by decide
  have hdescent : baseEnd_1300026 < baseStart_1300026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300073 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 2, 5, 2]
def baseStart_1300073 : Nat := 118140960795 + 1300073 * 2 ^ 59
def prefixEnd_1300073 : Nat := 4983230072969 + 3 ^ 40 * 1300073 * 2
def baseEnd_1300073 : Nat := 667562334932797192108579

theorem tailTrace_1300073 : CollatzResearch.WordTrace tailWord_1300073 prefixEnd_1300073 667562334932797192108579 := by
  unfold tailWord_1300073
  simp only [CollatzResearch.WordTrace]
  refine ⟨47417557819065030636416873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31611705212710020424277915 47417557819065030636416873)
  ·
    refine ⟨35563168364298772977312655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47417557819065030636416873 35563168364298772977312655)
    ·
      refine ⟨53344752546448159465968983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35563168364298772977312655 53344752546448159465968983)
      ·
        refine ⟨80017128819672239198953475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53344752546448159465968983 80017128819672239198953475)
        ·
          refine ⟨120025693229508358798430213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80017128819672239198953475 120025693229508358798430213)
          ·
            refine ⟨22504817480532817274705665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120025693229508358798430213 22504817480532817274705665)
            ·
              refine ⟨16878613110399612956029249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22504817480532817274705665 16878613110399612956029249)
              ·
                refine ⟨12658959832799709717021937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16878613110399612956029249 12658959832799709717021937)
                ·
                  refine ⟨9494219874599782287766453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12658959832799709717021937 9494219874599782287766453)
                  ·
                    refine ⟨890083113243729589478105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9494219874599782287766453 890083113243729589478105)
                    ·
                      refine ⟨667562334932797192108579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 890083113243729589478105 667562334932797192108579)
                      ·
                        rfl

theorem cell23_1300073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 5, 2].length) (baseStart_1300073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300073 prefixEnd_1300073 := by exact prefixLift 1300073
  have htrace : WordTrace (prefixWord ++ tailWord_1300073) baseStart_1300073 baseEnd_1300073 := by
    simpa [prefixWord, tailWord_1300073, baseEnd_1300073] using wordTrace_append hprefix tailTrace_1300073
  have hstable : (prefixWord ++ tailWord_1300073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300073).length < 2 ^ (prefixWord ++ tailWord_1300073).sum := by decide
  have hdescent : baseEnd_1300073 < baseStart_1300073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300076 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 5]
def baseStart_1300076 : Nat := 118140960795 + 1300076 * 2 ^ 59
def prefixEnd_1300076 : Nat := 4983230072969 + 3 ^ 40 * 1300076 * 2
def baseEnd_1300076 : Nat := 667563875374760680371065

theorem tailTrace_1300076 : CollatzResearch.WordTrace tailWord_1300076 prefixEnd_1300076 667563875374760680371065 := by
  unfold tailWord_1300076
  simp only [CollatzResearch.WordTrace]
  refine ⟨23708833619027081074388041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31611778158702774765850721 23708833619027081074388041)
  ·
    refine ⟨17781625214270310805791031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23708833619027081074388041 17781625214270310805791031)
    ·
      refine ⟨26672437821405466208686547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17781625214270310805791031 26672437821405466208686547)
      ·
        refine ⟨40008656732108199313029821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26672437821405466208686547 40008656732108199313029821)
        ·
          refine ⟨15003246274540574742386183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40008656732108199313029821 15003246274540574742386183)
          ·
            refine ⟨22504869411810862113579275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15003246274540574742386183 22504869411810862113579275)
            ·
              refine ⟨33757304117716293170368913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22504869411810862113579275 33757304117716293170368913)
              ·
                refine ⟨25317978088287219877776685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33757304117716293170368913 25317978088287219877776685)
                ·
                  refine ⟨9494241783107707454166257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25317978088287219877776685 9494241783107707454166257)
                  ·
                    refine ⟨7120681337330780590624693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9494241783107707454166257 7120681337330780590624693)
                    ·
                      refine ⟨667563875374760680371065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7120681337330780590624693 667563875374760680371065)
                      ·
                        rfl

theorem cell23_1300076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_1300076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300076 prefixEnd_1300076 := by exact prefixLift 1300076
  have htrace : WordTrace (prefixWord ++ tailWord_1300076) baseStart_1300076 baseEnd_1300076 := by
    simpa [prefixWord, tailWord_1300076, baseEnd_1300076] using wordTrace_append hprefix tailTrace_1300076
  have hstable : (prefixWord ++ tailWord_1300076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300076).length < 2 ^ (prefixWord ++ tailWord_1300076).sum := by decide
  have hdescent : baseEnd_1300076 < baseStart_1300076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300100 : List Nat := [2, 3, 2, 1, 4, 1, 1, 2, 2, 5]
def baseStart_1300100 : Nat := 118140960795 + 1300100 * 2 ^ 59
def prefixEnd_1300100 : Nat := 4983230072969 + 3 ^ 40 * 1300100 * 2
def baseEnd_1300100 : Nat := 222525399636822862156985

theorem tailTrace_1300100 : CollatzResearch.WordTrace tailWord_1300100 prefixEnd_1300100 222525399636822862156985 := by
  unfold tailWord_1300100
  simp only [CollatzResearch.WordTrace]
  refine ⟨23709271294983607123824877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31612361726644809498433169 23709271294983607123824877)
  ·
    refine ⟨8890976735618852671434329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23709271294983607123824877 8890976735618852671434329)
    ·
      refine ⟨6668232551714139503575747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8890976735618852671434329 6668232551714139503575747)
      ·
        refine ⟨10002348827571209255363621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6668232551714139503575747 10002348827571209255363621)
        ·
          refine ⟨1875440405169601735380679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10002348827571209255363621 1875440405169601735380679)
          ·
            refine ⟨2813160607754402603071019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1875440405169601735380679 2813160607754402603071019)
            ·
              refine ⟨4219740911631603904606529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2813160607754402603071019 4219740911631603904606529)
              ·
                refine ⟨3164805683723702928454897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4219740911631603904606529 3164805683723702928454897)
                ·
                  refine ⟨2373604262792777196341173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3164805683723702928454897 2373604262792777196341173)
                  ·
                    refine ⟨222525399636822862156985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2373604262792777196341173 222525399636822862156985)
                    ·
                      rfl

theorem cell23_1300100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_1300100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300100 prefixEnd_1300100 := by exact prefixLift 1300100
  have htrace : WordTrace (prefixWord ++ tailWord_1300100) baseStart_1300100 baseEnd_1300100 := by
    simpa [prefixWord, tailWord_1300100, baseEnd_1300100] using wordTrace_append hprefix tailTrace_1300100
  have hstable : (prefixWord ++ tailWord_1300100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300100).length < 2 ^ (prefixWord ++ tailWord_1300100).sum := by decide
  have hdescent : baseEnd_1300100 < baseStart_1300100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300103 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 4]
def baseStart_1300103 : Nat := 118140960795 + 1300103 * 2 ^ 59
def prefixEnd_1300103 : Nat := 4983230072969 + 3 ^ 40 * 1300103 * 2
def baseEnd_1300103 : Nat := 667577739352432074733441

theorem tailTrace_1300103 : CollatzResearch.WordTrace tailWord_1300103 prefixEnd_1300103 667577739352432074733441 := by
  unfold tailWord_1300103
  simp only [CollatzResearch.WordTrace]
  refine ⟨47418652008956345760008963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31612434672637563840005975 47418652008956345760008963)
  ·
    refine ⟨71127978013434518640013445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47418652008956345760008963 71127978013434518640013445)
    ·
      refine ⟨13336495877518972245002521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71127978013434518640013445 13336495877518972245002521)
      ·
        refine ⟨10002371908139229183751891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13336495877518972245002521 10002371908139229183751891)
        ·
          refine ⟨15003557862208843775627837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10002371908139229183751891 15003557862208843775627837)
          ·
            refine ⟨5626334198328316415860439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15003557862208843775627837 5626334198328316415860439)
            ·
              refine ⟨8439501297492474623790659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5626334198328316415860439 8439501297492474623790659)
              ·
                refine ⟨12659251946238711935685989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8439501297492474623790659 12659251946238711935685989)
                ·
                  refine ⟨2373609739919758487941123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12659251946238711935685989 2373609739919758487941123)
                  ·
                    refine ⟨3560414609879637731911685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2373609739919758487941123 3560414609879637731911685)
                    ·
                      refine ⟨667577739352432074733441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3560414609879637731911685 667577739352432074733441)
                      ·
                        rfl

theorem cell23_1300103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_1300103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300103 prefixEnd_1300103 := by exact prefixLift 1300103
  have htrace : WordTrace (prefixWord ++ tailWord_1300103) baseStart_1300103 baseEnd_1300103 := by
    simpa [prefixWord, tailWord_1300103, baseEnd_1300103] using wordTrace_append hprefix tailTrace_1300103
  have hstable : (prefixWord ++ tailWord_1300103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300103).length < 2 ^ (prefixWord ++ tailWord_1300103).sum := by decide
  have hdescent : baseEnd_1300103 < baseStart_1300103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300104 : List Nat := [2, 1, 3, 5, 1, 1, 3, 2, 5]
def baseStart_1300104 : Nat := 118140960795 + 1300104 * 2 ^ 59
def prefixEnd_1300104 : Nat := 4983230072969 + 3 ^ 40 * 1300104 * 2
def baseEnd_1300104 : Nat := 74175361425898507868993

theorem tailTrace_1300104 : CollatzResearch.WordTrace tailWord_1300104 prefixEnd_1300104 74175361425898507868993 := by
  unfold tailWord_1300104
  simp only [CollatzResearch.WordTrace]
  refine ⟨23709344240976361465397683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31612458987968481953863577 23709344240976361465397683)
  ·
    refine ⟨35564016361464542198096525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23709344240976361465397683 35564016361464542198096525)
    ·
      refine ⟨13336506135549203324286197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35564016361464542198096525 13336506135549203324286197)
      ·
        refine ⟨1250297450207737811651831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13336506135549203324286197 1250297450207737811651831)
        ·
          refine ⟨1875446175311606717477747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1250297450207737811651831 1875446175311606717477747)
          ·
            refine ⟨2813169262967410076216621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1875446175311606717477747 2813169262967410076216621)
            ·
              refine ⟨1054938473612778778581233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2813169262967410076216621 1054938473612778778581233)
              ·
                refine ⟨791203855209584083935925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1054938473612778778581233 791203855209584083935925)
                ·
                  refine ⟨74175361425898507868993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 791203855209584083935925 74175361425898507868993)
                  ·
                    rfl

theorem cell23_1300104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 5].length) (baseStart_1300104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300104 prefixEnd_1300104 := by exact prefixLift 1300104
  have htrace : WordTrace (prefixWord ++ tailWord_1300104) baseStart_1300104 baseEnd_1300104 := by
    simpa [prefixWord, tailWord_1300104, baseEnd_1300104] using wordTrace_append hprefix tailTrace_1300104
  have hstable : (prefixWord ++ tailWord_1300104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300104).length < 2 ^ (prefixWord ++ tailWord_1300104).sum := by decide
  have hdescent : baseEnd_1300104 < baseStart_1300104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300113 : List Nat := [1, 2, 2, 1, 1, 1, 1, 7, 3, 4]
def baseStart_1300113 : Nat := 118140960795 + 1300113 * 2 ^ 59
def prefixEnd_1300113 : Nat := 4983230072969 + 3 ^ 40 * 1300113 * 2
def baseEnd_1300113 : Nat := 222527624719659011869465

theorem tailTrace_1300113 : CollatzResearch.WordTrace tailWord_1300113 prefixEnd_1300113 222527624719659011869465 := by
  unfold tailWord_1300113
  simp only [CollatzResearch.WordTrace]
  refine ⟨47419016738920117467872993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31612677825946744978581995 47419016738920117467872993)
  ·
    refine ⟨35564262554190088100904745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47419016738920117467872993 35564262554190088100904745)
    ·
      refine ⟨26673196915642566075678559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35564262554190088100904745 26673196915642566075678559)
      ·
        refine ⟨40009795373463849113517839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26673196915642566075678559 40009795373463849113517839)
        ·
          refine ⟨60014693060195773670276759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40009795373463849113517839 60014693060195773670276759)
          ·
            refine ⟨90022039590293660505415139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60014693060195773670276759 90022039590293660505415139)
            ·
              refine ⟨135033059385440490758122709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90022039590293660505415139 135033059385440490758122709)
              ·
                refine ⟨3164837329346261502143501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 135033059385440490758122709 3164837329346261502143501)
                ·
                  refine ⟨1186813998504848063303813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3164837329346261502143501 1186813998504848063303813)
                  ·
                    refine ⟨222527624719659011869465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1186813998504848063303813 222527624719659011869465)
                    ·
                      rfl

theorem cell23_1300113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 4].length) (baseStart_1300113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300113 prefixEnd_1300113 := by exact prefixLift 1300113
  have htrace : WordTrace (prefixWord ++ tailWord_1300113) baseStart_1300113 baseEnd_1300113 := by
    simpa [prefixWord, tailWord_1300113, baseEnd_1300113] using wordTrace_append hprefix tailTrace_1300113
  have hstable : (prefixWord ++ tailWord_1300113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300113).length < 2 ^ (prefixWord ++ tailWord_1300113).sum := by decide
  have hdescent : baseEnd_1300113 < baseStart_1300113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300203 : List Nat := [1, 1, 1, 1, 2, 4, 4, 2, 1, 6]
def baseStart_1300203 : Nat := 118140960795 + 1300203 * 2 ^ 59
def prefixEnd_1300203 : Nat := 4983230072969 + 3 ^ 40 * 1300203 * 2
def baseEnd_1300203 : Nat := 222543029139293894494327

theorem tailTrace_1300203 : CollatzResearch.WordTrace tailWord_1300203 prefixEnd_1300203 222543029139293894494327 := by
  unfold tailWord_1300203
  simp only [CollatzResearch.WordTrace]
  refine ⟨47422299308594062838649263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31614866205729375225766175 47422299308594062838649263)
  ·
    refine ⟨71133448962891094257973895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47422299308594062838649263 71133448962891094257973895)
    ·
      refine ⟨106700173444336641386960843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71133448962891094257973895 106700173444336641386960843)
      ·
        refine ⟨160050260166504962080441265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106700173444336641386960843 160050260166504962080441265)
        ·
          refine ⟨120037695124878721560330949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160050260166504962080441265 120037695124878721560330949)
          ·
            refine ⟨22507067835914760292562053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120037695124878721560330949 22507067835914760292562053)
            ·
              refine ⟨4220075219234017554855385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22507067835914760292562053 4220075219234017554855385)
              ·
                refine ⟨3165056414425513166141539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4220075219234017554855385 3165056414425513166141539)
                ·
                  refine ⟨4747584621638269749212309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3165056414425513166141539 4747584621638269749212309)
                  ·
                    refine ⟨222543029139293894494327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4747584621638269749212309 222543029139293894494327)
                    ·
                      rfl

theorem cell23_1300203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 6].length) (baseStart_1300203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300203 prefixEnd_1300203 := by exact prefixLift 1300203
  have htrace : WordTrace (prefixWord ++ tailWord_1300203) baseStart_1300203 baseEnd_1300203 := by
    simpa [prefixWord, tailWord_1300203, baseEnd_1300203] using wordTrace_append hprefix tailTrace_1300203
  have hstable : (prefixWord ++ tailWord_1300203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300203).length < 2 ^ (prefixWord ++ tailWord_1300203).sum := by decide
  have hdescent : baseEnd_1300203 < baseStart_1300203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300220 : List Nat := [2, 2, 2, 1, 3, 1, 3, 1, 4, 4]
def baseStart_1300220 : Nat := 118140960795 + 1300220 * 2 ^ 59
def prefixEnd_1300220 : Nat := 4983230072969 + 3 ^ 40 * 1300220 * 2
def baseEnd_1300220 : Nat := 222545938863002705656801

theorem tailTrace_1300220 : CollatzResearch.WordTrace tailWord_1300220 prefixEnd_1300220 222545938863002705656801 := by
  unfold tailWord_1300220
  simp only [CollatzResearch.WordTrace]
  refine ⟨23711459674766237371009057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31615279566354983161345409 23711459674766237371009057)
  ·
    refine ⟨17783594756074678028256793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23711459674766237371009057 17783594756074678028256793)
    ·
      refine ⟨13337696067056008521192595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17783594756074678028256793 13337696067056008521192595)
      ·
        refine ⟨20006544100584012781788893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13337696067056008521192595 20006544100584012781788893)
        ·
          refine ⟨7502454037719004793170835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20006544100584012781788893 7502454037719004793170835)
          ·
            refine ⟨11253681056578507189756253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7502454037719004793170835 11253681056578507189756253)
            ·
              refine ⟨4220130396216940196158595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11253681056578507189756253 4220130396216940196158595)
              ·
                refine ⟨6330195594325410294237893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4220130396216940196158595 6330195594325410294237893)
                ·
                  refine ⟨1186911673936014430169605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6330195594325410294237893 1186911673936014430169605)
                  ·
                    refine ⟨222545938863002705656801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1186911673936014430169605 222545938863002705656801)
                    ·
                      rfl

theorem cell23_1300220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_1300220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300220 prefixEnd_1300220 := by exact prefixLift 1300220
  have htrace : WordTrace (prefixWord ++ tailWord_1300220) baseStart_1300220 baseEnd_1300220 := by
    simpa [prefixWord, tailWord_1300220, baseEnd_1300220] using wordTrace_append hprefix tailTrace_1300220
  have hstable : (prefixWord ++ tailWord_1300220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300220).length < 2 ^ (prefixWord ++ tailWord_1300220).sum := by decide
  have hdescent : baseEnd_1300220 < baseStart_1300220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300223 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 4]
def baseStart_1300223 : Nat := 118140960795 + 1300223 * 2 ^ 59
def prefixEnd_1300223 : Nat := 4983230072969 + 3 ^ 40 * 1300223 * 2
def baseEnd_1300223 : Nat := 667639357030971605232889

theorem tailTrace_1300223 : CollatzResearch.WordTrace tailWord_1300223 prefixEnd_1300223 667639357030971605232889 := by
  unfold tailWord_1300223
  simp only [CollatzResearch.WordTrace]
  refine ⟨47423028768521606254377323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31615352512347737502918215 47423028768521606254377323)
  ·
    refine ⟨71134543152782409381565985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47423028768521606254377323 71134543152782409381565985)
    ·
      refine ⟨53350907364586807036174489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71134543152782409381565985 53350907364586807036174489)
      ·
        refine ⟨40013180523440105277130867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53350907364586807036174489 40013180523440105277130867)
        ·
          refine ⟨60019770785160157915696301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40013180523440105277130867 60019770785160157915696301)
          ·
            refine ⟨22507414044435059218386113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60019770785160157915696301 22507414044435059218386113)
            ·
              refine ⟨16880560533326294413789585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22507414044435059218386113 16880560533326294413789585)
              ·
                refine ⟨12660420399994720810342189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16880560533326294413789585 12660420399994720810342189)
                ·
                  refine ⟨4747657649998020303878321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12660420399994720810342189 4747657649998020303878321)
                  ·
                    refine ⟨3560743237498515227908741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4747657649998020303878321 3560743237498515227908741)
                    ·
                      refine ⟨667639357030971605232889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3560743237498515227908741 667639357030971605232889)
                      ·
                        rfl

theorem cell23_1300223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_1300223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300223 prefixEnd_1300223 := by exact prefixLift 1300223
  have htrace : WordTrace (prefixWord ++ tailWord_1300223) baseStart_1300223 baseEnd_1300223 := by
    simpa [prefixWord, tailWord_1300223, baseEnd_1300223] using wordTrace_append hprefix tailTrace_1300223
  have hstable : (prefixWord ++ tailWord_1300223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300223).length < 2 ^ (prefixWord ++ tailWord_1300223).sum := by decide
  have hdescent : baseEnd_1300223 < baseStart_1300223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300227 : List Nat := [1, 1, 1, 3, 2, 2, 3, 3, 3, 2, 2]
def baseStart_1300227 : Nat := 118140960795 + 1300227 * 2 ^ 59
def prefixEnd_1300227 : Nat := 4983230072969 + 3 ^ 40 * 1300227 * 2
def baseEnd_1300227 : Nat := 667641410953589589582871

theorem tailTrace_1300227 : CollatzResearch.WordTrace tailWord_1300227 prefixEnd_1300227 667641410953589589582871 := by
  unfold tailWord_1300227
  simp only [CollatzResearch.WordTrace]
  refine ⟨47423174660507114937522935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31615449773671409958348623 47423174660507114937522935)
  ·
    refine ⟨71134761990760672406284403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47423174660507114937522935 71134761990760672406284403)
    ·
      refine ⟨106702142986141008609426605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71134761990760672406284403 106702142986141008609426605)
      ·
        refine ⟨40013303619802878228534977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106702142986141008609426605 40013303619802878228534977)
        ·
          refine ⟨30009977714852158671401233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40013303619802878228534977 30009977714852158671401233)
          ·
            refine ⟨22507483286139119003550925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30009977714852158671401233 22507483286139119003550925)
            ·
              refine ⟨8440306232302169626331597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22507483286139119003550925 8440306232302169626331597)
              ·
                refine ⟨3165114837113313609874349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8440306232302169626331597 3165114837113313609874349)
                ·
                  refine ⟨1186918063917492603702881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3165114837113313609874349 1186918063917492603702881)
                  ·
                    refine ⟨890188547938119452777161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1186918063917492603702881 890188547938119452777161)
                    ·
                      refine ⟨667641410953589589582871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 890188547938119452777161 667641410953589589582871)
                      ·
                        rfl

theorem cell23_1300227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 2, 2].length) (baseStart_1300227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300227 prefixEnd_1300227 := by exact prefixLift 1300227
  have htrace : WordTrace (prefixWord ++ tailWord_1300227) baseStart_1300227 baseEnd_1300227 := by
    simpa [prefixWord, tailWord_1300227, baseEnd_1300227] using wordTrace_append hprefix tailTrace_1300227
  have hstable : (prefixWord ++ tailWord_1300227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300227).length < 2 ^ (prefixWord ++ tailWord_1300227).sum := by decide
  have hdescent : baseEnd_1300227 < baseStart_1300227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300247 : List Nat := [1, 1, 3, 4, 2, 1, 1, 4, 1, 2, 3]
def baseStart_1300247 : Nat := 118140960795 + 1300247 * 2 ^ 59
def prefixEnd_1300247 : Nat := 4983230072969 + 3 ^ 40 * 1300247 * 2
def baseEnd_1300247 : Nat := 667651680566679511332779

theorem tailTrace_1300247 : CollatzResearch.WordTrace tailWord_1300247 prefixEnd_1300247 667651680566679511332779 := by
  unfold tailWord_1300247
  simp only [CollatzResearch.WordTrace]
  refine ⟨47423904120434658353250995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31615936080289772235500663 47423904120434658353250995)
  ·
    refine ⟨71135856180651987529876493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47423904120434658353250995 71135856180651987529876493)
    ·
      refine ⟨26675946067744495323703685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71135856180651987529876493 26675946067744495323703685)
      ·
        refine ⟨5001739887702092873194441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26675946067744495323703685 5001739887702092873194441)
        ·
          refine ⟨3751304915776569654895831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5001739887702092873194441 3751304915776569654895831)
          ·
            refine ⟨5626957373664854482343747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3751304915776569654895831 5626957373664854482343747)
            ·
              refine ⟨8440436060497281723515621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5626957373664854482343747 8440436060497281723515621)
              ·
                refine ⟨1582581761343240323159179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8440436060497281723515621 1582581761343240323159179)
                ·
                  refine ⟨2373872642014860484738769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1582581761343240323159179 2373872642014860484738769)
                  ·
                    refine ⟨1780404481511145363554077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2373872642014860484738769 1780404481511145363554077)
                    ·
                      refine ⟨667651680566679511332779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1780404481511145363554077 667651680566679511332779)
                      ·
                        rfl

theorem cell23_1300247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_1300247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300247 prefixEnd_1300247 := by exact prefixLift 1300247
  have htrace : WordTrace (prefixWord ++ tailWord_1300247) baseStart_1300247 baseEnd_1300247 := by
    simpa [prefixWord, tailWord_1300247, baseEnd_1300247] using wordTrace_append hprefix tailTrace_1300247
  have hstable : (prefixWord ++ tailWord_1300247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300247).length < 2 ^ (prefixWord ++ tailWord_1300247).sum := by decide
  have hdescent : baseEnd_1300247 < baseStart_1300247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300250 : List Nat := [3, 1, 1, 3, 2, 2, 4, 7]
def baseStart_1300250 : Nat := 118140960795 + 1300250 * 2 ^ 59
def prefixEnd_1300250 : Nat := 4983230072969 + 3 ^ 40 * 1300250 * 2
def baseEnd_1300250 : Nat := 24727897074394185170195

theorem tailTrace_1300250 : CollatzResearch.WordTrace tailWord_1300250 prefixEnd_1300250 24727897074394185170195 := by
  unfold tailWord_1300250
  simp only [CollatzResearch.WordTrace]
  refine ⟨11856003384855947466402551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31616009026282526577073469 11856003384855947466402551)
  ·
    refine ⟨17784005077283921199603827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11856003384855947466402551 17784005077283921199603827)
    ·
      refine ⟨26676007615925881799405741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17784005077283921199603827 26676007615925881799405741)
      ·
        refine ⟨10003502855972205674777153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26676007615925881799405741 10003502855972205674777153)
        ·
          refine ⟨7502627141979154256082865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10003502855972205674777153 7502627141979154256082865)
          ·
            refine ⟨5626970356484365692062149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7502627141979154256082865 5626970356484365692062149)
            ·
              refine ⟨1055056941840818567261653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5626970356484365692062149 1055056941840818567261653)
              ·
                refine ⟨24727897074394185170195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1055056941840818567261653 24727897074394185170195)
                ·
                  rfl

theorem cell23_1300250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 7].length) (baseStart_1300250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300250 prefixEnd_1300250 := by exact prefixLift 1300250
  have htrace : WordTrace (prefixWord ++ tailWord_1300250) baseStart_1300250 baseEnd_1300250 := by
    simpa [prefixWord, tailWord_1300250, baseEnd_1300250] using wordTrace_append hprefix tailTrace_1300250
  have hstable : (prefixWord ++ tailWord_1300250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300250).length < 2 ^ (prefixWord ++ tailWord_1300250).sum := by decide
  have hdescent : baseEnd_1300250 < baseStart_1300250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300261 : List Nat := [1, 3, 1, 2, 3, 2, 3, 3, 1, 2, 2]
def baseStart_1300261 : Nat := 118140960795 + 1300261 * 2 ^ 59
def prefixEnd_1300261 : Nat := 4983230072969 + 3 ^ 40 * 1300261 * 2
def baseEnd_1300261 : Nat := 667658869295842456557715

theorem tailTrace_1300261 : CollatzResearch.WordTrace tailWord_1300261 prefixEnd_1300261 667658869295842456557715 := by
  unfold tailWord_1300261
  simp only [CollatzResearch.WordTrace]
  refine ⟨47424414742383938744260637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31616276494922625829507091 47424414742383938744260637)
  ·
    refine ⟨17784155528393977029097739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47424414742383938744260637 17784155528393977029097739)
    ·
      refine ⟨26676233292590965543646609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17784155528393977029097739 26676233292590965543646609)
      ·
        refine ⟨20007174969443224157734957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26676233292590965543646609 20007174969443224157734957)
        ·
          refine ⟨7502690613541209059150609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20007174969443224157734957 7502690613541209059150609)
          ·
            refine ⟨5627017960155906794362957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7502690613541209059150609 5627017960155906794362957)
            ·
              refine ⟨2110131735058465047886109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5627017960155906794362957 2110131735058465047886109)
              ·
                refine ⟨791299400646924392957291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2110131735058465047886109 791299400646924392957291)
                ·
                  refine ⟨1186949100970386589435937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 791299400646924392957291 1186949100970386589435937)
                  ·
                    refine ⟨890211825727789942076953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1186949100970386589435937 890211825727789942076953)
                    ·
                      refine ⟨667658869295842456557715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 890211825727789942076953 667658869295842456557715)
                      ·
                        rfl

theorem cell23_1300261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 1, 2, 2].length) (baseStart_1300261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300261 prefixEnd_1300261 := by exact prefixLift 1300261
  have htrace : WordTrace (prefixWord ++ tailWord_1300261) baseStart_1300261 baseEnd_1300261 := by
    simpa [prefixWord, tailWord_1300261, baseEnd_1300261] using wordTrace_append hprefix tailTrace_1300261
  have hstable : (prefixWord ++ tailWord_1300261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300261).length < 2 ^ (prefixWord ++ tailWord_1300261).sum := by decide
  have hdescent : baseEnd_1300261 < baseStart_1300261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300278 : List Nat := [5, 1, 2, 2, 1, 3, 1, 1, 3, 2, 2]
def baseStart_1300278 : Nat := 118140960795 + 1300278 * 2 ^ 59
def prefixEnd_1300278 : Nat := 4983230072969 + 3 ^ 40 * 1300278 * 2
def baseEnd_1300278 : Nat := 667667598466968890045137

theorem tailTrace_1300278 : CollatzResearch.WordTrace tailWord_1300278 prefixEnd_1300278 667667598466968890045137 := by
  unfold tailWord_1300278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2964064673957646915476843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31616689855548233765086325 2964064673957646915476843)
  ·
    refine ⟨4446097010936470373215265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2964064673957646915476843 4446097010936470373215265)
    ·
      refine ⟨3334572758202352779911449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4446097010936470373215265 3334572758202352779911449)
      ·
        refine ⟨2500929568651764584933587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3334572758202352779911449 2500929568651764584933587)
        ·
          refine ⟨3751394352977646877400381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2500929568651764584933587 3751394352977646877400381)
          ·
            refine ⟨1406772882366617579025143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3751394352977646877400381 1406772882366617579025143)
            ·
              refine ⟨2110159323549926368537715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1406772882366617579025143 2110159323549926368537715)
              ·
                refine ⟨3165238985324889552806573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2110159323549926368537715 3165238985324889552806573)
                ·
                  refine ⟨1186964619496833582302465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3165238985324889552806573 1186964619496833582302465)
                  ·
                    refine ⟨890223464622625186726849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1186964619496833582302465 890223464622625186726849)
                    ·
                      refine ⟨667667598466968890045137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 890223464622625186726849 667667598466968890045137)
                      ·
                        rfl

theorem cell23_1300278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_1300278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300278 prefixEnd_1300278 := by exact prefixLift 1300278
  have htrace : WordTrace (prefixWord ++ tailWord_1300278) baseStart_1300278 baseEnd_1300278 := by
    simpa [prefixWord, tailWord_1300278, baseEnd_1300278] using wordTrace_append hprefix tailTrace_1300278
  have hstable : (prefixWord ++ tailWord_1300278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300278).length < 2 ^ (prefixWord ++ tailWord_1300278).sum := by decide
  have hdescent : baseEnd_1300278 < baseStart_1300278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300293 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 1, 8]
def baseStart_1300293 : Nat := 118140960795 + 1300293 * 2 ^ 59
def prefixEnd_1300293 : Nat := 4983230072969 + 3 ^ 40 * 1300293 * 2
def baseEnd_1300293 : Nat := 222558433558928777119189

theorem tailTrace_1300293 : CollatzResearch.WordTrace tailWord_1300293 prefixEnd_1300293 222558433558928777119189 := by
  unfold tailWord_1300293
  simp only [CollatzResearch.WordTrace]
  refine ⟨47425581878268008209425533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31617054585512005472950355 47425581878268008209425533)
  ·
    refine ⟨17784593204350503078534575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47425581878268008209425533 17784593204350503078534575)
    ·
      refine ⟨26676889806525754617801863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17784593204350503078534575 26676889806525754617801863)
      ·
        refine ⟨40015334709788631926702795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26676889806525754617801863 40015334709788631926702795)
        ·
          refine ⟨60023002064682947890054193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40015334709788631926702795 60023002064682947890054193)
          ·
            refine ⟨45017251548512210917540645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60023002064682947890054193 45017251548512210917540645)
            ·
              refine ⟨8440734665346039547038871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45017251548512210917540645 8440734665346039547038871)
              ·
                refine ⟨12661101998019059320558307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8440734665346039547038871 12661101998019059320558307)
                ·
                  refine ⟨18991652997028588980837461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12661101998019059320558307 18991652997028588980837461)
                  ·
                    refine ⟨222558433558928777119189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18991652997028588980837461 222558433558928777119189)
                    ·
                      rfl

theorem cell23_1300293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_1300293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300293 prefixEnd_1300293 := by exact prefixLift 1300293
  have htrace : WordTrace (prefixWord ++ tailWord_1300293) baseStart_1300293 baseEnd_1300293 := by
    simpa [prefixWord, tailWord_1300293, baseEnd_1300293] using wordTrace_append hprefix tailTrace_1300293
  have hstable : (prefixWord ++ tailWord_1300293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300293).length < 2 ^ (prefixWord ++ tailWord_1300293).sum := by decide
  have hdescent : baseEnd_1300293 < baseStart_1300293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300320 : List Nat := [2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 5]
def baseStart_1300320 : Nat := 118140960795 + 1300320 * 2 ^ 59
def prefixEnd_1300320 : Nat := 4983230072969 + 3 ^ 40 * 1300320 * 2
def baseEnd_1300320 : Nat := 667689164654457725719943

theorem tailTrace_1300320 : CollatzResearch.WordTrace tailWord_1300320 prefixEnd_1300320 667689164654457725719943 := by
  unfold tailWord_1300320
  simp only [CollatzResearch.WordTrace]
  refine ⟨23713283324585095910329207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31617711099446794547105609 23713283324585095910329207)
  ·
    refine ⟨35569924986877643865493811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23713283324585095910329207 35569924986877643865493811)
    ·
      refine ⟨53354887480316465798240717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35569924986877643865493811 53354887480316465798240717)
      ·
        refine ⟨20008082805118674674340269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53354887480316465798240717 20008082805118674674340269)
        ·
          refine ⟨7503031051919503002877601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20008082805118674674340269 7503031051919503002877601)
          ·
            refine ⟨5627273288939627252158201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7503031051919503002877601 5627273288939627252158201)
            ·
              refine ⟨4220454966704720439118651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5627273288939627252158201 4220454966704720439118651)
              ·
                refine ⟨6330682450057080658677977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4220454966704720439118651 6330682450057080658677977)
                ·
                  refine ⟨4748011837542810494008483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6330682450057080658677977 4748011837542810494008483)
                  ·
                    refine ⟨7122017756314215741012725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4748011837542810494008483 7122017756314215741012725)
                    ·
                      refine ⟨667689164654457725719943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7122017756314215741012725 667689164654457725719943)
                      ·
                        rfl

theorem cell23_1300320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_1300320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300320 prefixEnd_1300320 := by exact prefixLift 1300320
  have htrace : WordTrace (prefixWord ++ tailWord_1300320) baseStart_1300320 baseEnd_1300320 := by
    simpa [prefixWord, tailWord_1300320, baseEnd_1300320] using wordTrace_append hprefix tailTrace_1300320
  have hstable : (prefixWord ++ tailWord_1300320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300320).length < 2 ^ (prefixWord ++ tailWord_1300320).sum := by decide
  have hdescent : baseEnd_1300320 < baseStart_1300320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300343 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 8]
def baseStart_1300343 : Nat := 118140960795 + 1300343 * 2 ^ 59
def prefixEnd_1300343 : Nat := 4983230072969 + 3 ^ 40 * 1300343 * 2
def baseEnd_1300343 : Nat := 667700974709511135732337

theorem tailTrace_1300343 : CollatzResearch.WordTrace tailWord_1300343 prefixEnd_1300343 667700974709511135732337 := by
  unfold tailWord_1300343
  simp only [CollatzResearch.WordTrace]
  refine ⟨47427405528086866748745683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31618270352057911165830455 47427405528086866748745683)
  ·
    refine ⟨71141108292130300123118525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47427405528086866748745683 71141108292130300123118525)
    ·
      refine ⟨26677915609548862546169447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71141108292130300123118525 26677915609548862546169447)
      ·
        refine ⟨40016873414323293819254171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26677915609548862546169447 40016873414323293819254171)
        ·
          refine ⟨60025310121484940728881257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40016873414323293819254171 60025310121484940728881257)
          ·
            refine ⟨45018982591113705546660943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60025310121484940728881257 45018982591113705546660943)
            ·
              refine ⟨67528473886670558319991415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45018982591113705546660943 67528473886670558319991415)
              ·
                refine ⟨101292710830005837479987123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67528473886670558319991415 101292710830005837479987123)
                ·
                  refine ⟨151939066245008756219980685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101292710830005837479987123 151939066245008756219980685)
                  ·
                    refine ⟨56977149841878283582492757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 151939066245008756219980685 56977149841878283582492757)
                    ·
                      refine ⟨667700974709511135732337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 56977149841878283582492757 667700974709511135732337)
                      ·
                        rfl

theorem cell23_1300343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_1300343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300343 prefixEnd_1300343 := by exact prefixLift 1300343
  have htrace : WordTrace (prefixWord ++ tailWord_1300343) baseStart_1300343 baseEnd_1300343 := by
    simpa [prefixWord, tailWord_1300343, baseEnd_1300343] using wordTrace_append hprefix tailTrace_1300343
  have hstable : (prefixWord ++ tailWord_1300343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300343).length < 2 ^ (prefixWord ++ tailWord_1300343).sum := by decide
  have hdescent : baseEnd_1300343 < baseStart_1300343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300385 : List Nat := [1, 2, 3, 4, 3, 1, 1, 2, 2, 2, 2]
def baseStart_1300385 : Nat := 118140960795 + 1300385 * 2 ^ 59
def prefixEnd_1300385 : Nat := 4983230072969 + 3 ^ 40 * 1300385 * 2
def baseEnd_1300385 : Nat := 667722540896999971407145

theorem tailTrace_1300385 : CollatzResearch.WordTrace tailWord_1300385 prefixEnd_1300385 667722540896999971407145 := by
  unfold tailWord_1300385
  simp only [CollatzResearch.WordTrace]
  refine ⟨47428937393934707921774609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31619291595956471947849739 47428937393934707921774609)
  ·
    refine ⟨35571703045451030941330957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47428937393934707921774609 35571703045451030941330957)
    ·
      refine ⟨13339388642044136602999109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35571703045451030941330957 13339388642044136602999109)
      ·
        refine ⟨2501135370383275613062333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13339388642044136602999109 2501135370383275613062333)
        ·
          refine ⟨937925763893728354898375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2501135370383275613062333 937925763893728354898375)
          ·
            refine ⟨1406888645840592532347563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 937925763893728354898375 1406888645840592532347563)
            ·
              refine ⟨2110332968760888798521345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1406888645840592532347563 2110332968760888798521345)
              ·
                refine ⟨1582749726570666598891009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2110332968760888798521345 1582749726570666598891009)
                ·
                  refine ⟨1187062294927999949168257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1582749726570666598891009 1187062294927999949168257)
                  ·
                    refine ⟨890296721195999961876193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1187062294927999949168257 890296721195999961876193)
                    ·
                      refine ⟨667722540896999971407145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 890296721195999961876193 667722540896999971407145)
                      ·
                        rfl

theorem cell23_1300385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_1300385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300385 prefixEnd_1300385 := by exact prefixLift 1300385
  have htrace : WordTrace (prefixWord ++ tailWord_1300385) baseStart_1300385 baseEnd_1300385 := by
    simpa [prefixWord, tailWord_1300385, baseEnd_1300385] using wordTrace_append hprefix tailTrace_1300385
  have hstable : (prefixWord ++ tailWord_1300385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300385).length < 2 ^ (prefixWord ++ tailWord_1300385).sum := by decide
  have hdescent : baseEnd_1300385 < baseStart_1300385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300427 : List Nat := [1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 3]
def baseStart_1300427 : Nat := 118140960795 + 1300427 * 2 ^ 59
def prefixEnd_1300427 : Nat := 4983230072969 + 3 ^ 40 * 1300427 * 2
def baseEnd_1300427 : Nat := 667744107084488807081951

theorem tailTrace_1300427 : CollatzResearch.WordTrace tailWord_1300427 prefixEnd_1300427 667744107084488807081951 := by
  unfold tailWord_1300427
  simp only [CollatzResearch.WordTrace]
  refine ⟨47430469259782549094803535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31620312839855032729869023 47430469259782549094803535)
  ·
    refine ⟨71145703889673823642205303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47430469259782549094803535 71145703889673823642205303)
    ·
      refine ⟨106718555834510735463307955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71145703889673823642205303 106718555834510735463307955)
      ·
        refine ⟨160077833751766103194961933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106718555834510735463307955 160077833751766103194961933)
        ·
          refine ⟨60029187656912288698110725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160077833751766103194961933 60029187656912288698110725)
          ·
            refine ⟨11255472685671054130895761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60029187656912288698110725 11255472685671054130895761)
            ·
              refine ⟨8441604514253290598171821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11255472685671054130895761 8441604514253290598171821)
              ·
                refine ⟨3165601692844983974314433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8441604514253290598171821 3165601692844983974314433)
                ·
                  refine ⟨2374201269633737980735825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3165601692844983974314433 2374201269633737980735825)
                  ·
                    refine ⟨1780650952225303485551869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2374201269633737980735825 1780650952225303485551869)
                    ·
                      refine ⟨667744107084488807081951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1780650952225303485551869 667744107084488807081951)
                      ·
                        rfl

theorem cell23_1300427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 3].length) (baseStart_1300427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300427 prefixEnd_1300427 := by exact prefixLift 1300427
  have htrace : WordTrace (prefixWord ++ tailWord_1300427) baseStart_1300427 baseEnd_1300427 := by
    simpa [prefixWord, tailWord_1300427, baseEnd_1300427] using wordTrace_append hprefix tailTrace_1300427
  have hstable : (prefixWord ++ tailWord_1300427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300427).length < 2 ^ (prefixWord ++ tailWord_1300427).sum := by decide
  have hdescent : baseEnd_1300427 < baseStart_1300427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300430 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 10]
def baseStart_1300430 : Nat := 118140960795 + 1300430 * 2 ^ 59
def prefixEnd_1300430 : Nat := 4983230072969 + 3 ^ 40 * 1300430 * 2
def baseEnd_1300430 : Nat := 74193960836272477260493

theorem tailTrace_1300430 : CollatzResearch.WordTrace tailWord_1300430 prefixEnd_1300430 74193960836272477260493 := by
  unfold tailWord_1300430
  simp only [CollatzResearch.WordTrace]
  refine ⟨5928822334846460075895343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31620385785847787071441829 5928822334846460075895343)
  ·
    refine ⟨8893233502269690113843015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5928822334846460075895343 8893233502269690113843015)
    ·
      refine ⟨13339850253404535170764523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8893233502269690113843015 13339850253404535170764523)
      ·
        refine ⟨20009775380106802756146785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13339850253404535170764523 20009775380106802756146785)
        ·
          refine ⟨15007331535080102067110089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20009775380106802756146785 15007331535080102067110089)
          ·
            refine ⟨11255498651310076550332567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15007331535080102067110089 11255498651310076550332567)
            ·
              refine ⟨16883247976965114825498851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11255498651310076550332567 16883247976965114825498851)
              ·
                refine ⟨25324871965447672238248277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16883247976965114825498851 25324871965447672238248277)
                ·
                  refine ⟨74193960836272477260493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 25324871965447672238248277 74193960836272477260493)
                  ·
                    rfl

theorem cell23_1300430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_1300430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300430 prefixEnd_1300430 := by exact prefixLift 1300430
  have htrace : WordTrace (prefixWord ++ tailWord_1300430) baseStart_1300430 baseEnd_1300430 := by
    simpa [prefixWord, tailWord_1300430, baseEnd_1300430] using wordTrace_append hprefix tailTrace_1300430
  have hstable : (prefixWord ++ tailWord_1300430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300430).length < 2 ^ (prefixWord ++ tailWord_1300430).sum := by decide
  have hdescent : baseEnd_1300430 < baseStart_1300430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300467 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 3, 5, 2]
def baseStart_1300467 : Nat := 118140960795 + 1300467 * 2 ^ 59
def prefixEnd_1300467 : Nat := 4983230072969 + 3 ^ 40 * 1300467 * 2
def baseEnd_1300467 : Nat := 667764646310668650581767

theorem tailTrace_1300467 : CollatzResearch.WordTrace tailWord_1300467 prefixEnd_1300467 667764646310668650581767 := by
  unfold tailWord_1300467
  simp only [CollatzResearch.WordTrace]
  refine ⟨47431928179637635926259655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31621285453091757284173103 47431928179637635926259655)
  ·
    refine ⟨71147892269456453889389483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47431928179637635926259655 71147892269456453889389483)
    ·
      refine ⟨106721838404184680834084225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71147892269456453889389483 106721838404184680834084225)
      ·
        refine ⟨80041378803138510625563169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106721838404184680834084225 80041378803138510625563169)
        ·
          refine ⟨60031034102353882969172377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80041378803138510625563169 60031034102353882969172377)
          ·
            refine ⟨45023275576765412226879283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60031034102353882969172377 45023275576765412226879283)
            ·
              refine ⟨67534913365148118340318925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45023275576765412226879283 67534913365148118340318925)
              ·
                refine ⟨25325592511930544377619597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67534913365148118340318925 25325592511930544377619597)
                ·
                  refine ⟨9497097191973954141607349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25325592511930544377619597 9497097191973954141607349)
                  ·
                    refine ⟨890352861747558200775689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9497097191973954141607349 890352861747558200775689)
                    ·
                      refine ⟨667764646310668650581767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 890352861747558200775689 667764646310668650581767)
                      ·
                        rfl

theorem cell23_1300467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 5, 2].length) (baseStart_1300467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300467 prefixEnd_1300467 := by exact prefixLift 1300467
  have htrace : WordTrace (prefixWord ++ tailWord_1300467) baseStart_1300467 baseEnd_1300467 := by
    simpa [prefixWord, tailWord_1300467, baseEnd_1300467] using wordTrace_append hprefix tailTrace_1300467
  have hstable : (prefixWord ++ tailWord_1300467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300467).length < 2 ^ (prefixWord ++ tailWord_1300467).sum := by decide
  have hdescent : baseEnd_1300467 < baseStart_1300467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300491 : List Nat := [1, 1, 1, 1, 6, 1, 2, 5, 1, 1, 3]
def baseStart_1300491 : Nat := 118140960795 + 1300491 * 2 ^ 59
def prefixEnd_1300491 : Nat := 4983230072969 + 3 ^ 40 * 1300491 * 2
def baseEnd_1300491 : Nat := 667776969846376556681657

theorem tailTrace_1300491 : CollatzResearch.WordTrace tailWord_1300491 prefixEnd_1300491 667776969846376556681657 := by
  unfold tailWord_1300491
  simp only [CollatzResearch.WordTrace]
  refine ⟨47432803531550688025133327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31621869021033792016755551 47432803531550688025133327)
  ·
    refine ⟨71149205297326032037699991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47432803531550688025133327 71149205297326032037699991)
    ·
      refine ⟨106723807945989048056549987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71149205297326032037699991 106723807945989048056549987)
      ·
        refine ⟨160085711918983572084824981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106723807945989048056549987 160085711918983572084824981)
        ·
          refine ⟨7504017746202354941476171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 160085711918983572084824981 7504017746202354941476171)
          ·
            refine ⟨11256026619303532412214257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7504017746202354941476171 11256026619303532412214257)
            ·
              refine ⟨8442019964477649309160693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11256026619303532412214257 8442019964477649309160693)
              ·
                refine ⟨791439371669779622733815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8442019964477649309160693 791439371669779622733815)
                ·
                  refine ⟨1187159057504669434100723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 791439371669779622733815 1187159057504669434100723)
                  ·
                    refine ⟨1780738586257004151151085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1187159057504669434100723 1780738586257004151151085)
                    ·
                      refine ⟨667776969846376556681657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1780738586257004151151085 667776969846376556681657)
                      ·
                        rfl

theorem cell23_1300491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 1, 1, 3].length) (baseStart_1300491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300491 prefixEnd_1300491 := by exact prefixLift 1300491
  have htrace : WordTrace (prefixWord ++ tailWord_1300491) baseStart_1300491 baseEnd_1300491 := by
    simpa [prefixWord, tailWord_1300491, baseEnd_1300491] using wordTrace_append hprefix tailTrace_1300491
  have hstable : (prefixWord ++ tailWord_1300491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300491).length < 2 ^ (prefixWord ++ tailWord_1300491).sum := by decide
  have hdescent : baseEnd_1300491 < baseStart_1300491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300508 : List Nat := [2, 2, 3, 1, 3, 2, 1, 4, 1, 1, 3]
def baseStart_1300508 : Nat := 118140960795 + 1300508 * 2 ^ 59
def prefixEnd_1300508 : Nat := 4983230072969 + 3 ^ 40 * 1300508 * 2
def baseEnd_1300508 : Nat := 667785699017502990169079

theorem tailTrace_1300508 : CollatzResearch.WordTrace tailWord_1300508 prefixEnd_1300508 667785699017502990169079 := by
  unfold tailWord_1300508
  simp only [CollatzResearch.WordTrace]
  refine ⟨23716711786244549964251089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31622282381659399952334785 23716711786244549964251089)
  ·
    refine ⟨17787533839683412473188317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23716711786244549964251089 17787533839683412473188317)
    ·
      refine ⟨6670325189881279677445619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17787533839683412473188317 6670325189881279677445619)
      ·
        refine ⟨10005487784821919516168429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6670325189881279677445619 10005487784821919516168429)
        ·
          refine ⟨3752057919308219818563161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10005487784821919516168429 3752057919308219818563161)
          ·
            refine ⟨2814043439481164863922371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3752057919308219818563161 2814043439481164863922371)
            ·
              refine ⟨4221065159221747295883557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2814043439481164863922371 4221065159221747295883557)
              ·
                refine ⟨791449717354077617978167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4221065159221747295883557 791449717354077617978167)
                ·
                  refine ⟨1187174576031116426967251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 791449717354077617978167 1187174576031116426967251)
                  ·
                    refine ⟨1780761864046674640450877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1187174576031116426967251 1780761864046674640450877)
                    ·
                      refine ⟨667785699017502990169079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1780761864046674640450877 667785699017502990169079)
                      ·
                        rfl

theorem cell23_1300508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_1300508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300508 prefixEnd_1300508 := by exact prefixLift 1300508
  have htrace : WordTrace (prefixWord ++ tailWord_1300508) baseStart_1300508 baseEnd_1300508 := by
    simpa [prefixWord, tailWord_1300508, baseEnd_1300508] using wordTrace_append hprefix tailTrace_1300508
  have hstable : (prefixWord ++ tailWord_1300508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300508).length < 2 ^ (prefixWord ++ tailWord_1300508).sum := by decide
  have hdescent : baseEnd_1300508 < baseStart_1300508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300547 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 3]
def baseStart_1300547 : Nat := 118140960795 + 1300547 * 2 ^ 59
def prefixEnd_1300547 : Nat := 4983230072969 + 3 ^ 40 * 1300547 * 2
def baseEnd_1300547 : Nat := 667805724763028337581399

theorem tailTrace_1300547 : CollatzResearch.WordTrace tailWord_1300547 prefixEnd_1300547 667805724763028337581399 := by
  unfold tailWord_1300547
  simp only [CollatzResearch.WordTrace]
  refine ⟨47434846019347809589171895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31623230679565206392781263 47434846019347809589171895)
  ·
    refine ⟨71152269029021714383757843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47434846019347809589171895 71152269029021714383757843)
    ·
      refine ⟨106728403543532571575636765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71152269029021714383757843 106728403543532571575636765)
      ·
        refine ⟨40023151328824714340863787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106728403543532571575636765 40023151328824714340863787)
        ·
          refine ⟨60034726993237071511295681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40023151328824714340863787 60034726993237071511295681)
          ·
            refine ⟨45026045244927803633471761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60034726993237071511295681 45026045244927803633471761)
            ·
              refine ⟨33769533933695852725103821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45026045244927803633471761 33769533933695852725103821)
              ·
                refine ⟨12663575225135944771913933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33769533933695852725103821 12663575225135944771913933)
                ·
                  refine ⟨4748840709425979289467725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12663575225135944771913933 4748840709425979289467725)
                  ·
                    refine ⟨1780815266034742233550397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4748840709425979289467725 1780815266034742233550397)
                    ·
                      refine ⟨667805724763028337581399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1780815266034742233550397 667805724763028337581399)
                      ·
                        rfl

theorem cell23_1300547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 3].length) (baseStart_1300547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300547 prefixEnd_1300547 := by exact prefixLift 1300547
  have htrace : WordTrace (prefixWord ++ tailWord_1300547) baseStart_1300547 baseEnd_1300547 := by
    simpa [prefixWord, tailWord_1300547, baseEnd_1300547] using wordTrace_append hprefix tailTrace_1300547
  have hstable : (prefixWord ++ tailWord_1300547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300547).length < 2 ^ (prefixWord ++ tailWord_1300547).sum := by decide
  have hdescent : baseEnd_1300547 < baseStart_1300547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300578 : List Nat := [3, 3, 2, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_1300578 : Nat := 118140960795 + 1300578 * 2 ^ 59
def prefixEnd_1300578 : Nat := 4983230072969 + 3 ^ 40 * 1300578 * 2
def baseEnd_1300578 : Nat := 667821642663317716293757

theorem tailTrace_1300578 : CollatzResearch.WordTrace tailWord_1300578 prefixEnd_1300578 667821642663317716293757 := by
  unfold tailWord_1300578
  simp only [CollatzResearch.WordTrace]
  refine ⟨11858994170558875470887597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31623984454823667922366925 11858994170558875470887597)
  ·
    refine ⟨4447122813959578301582849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11858994170558875470887597 4447122813959578301582849)
    ·
      refine ⟨3335342110469683726187137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4447122813959578301582849 3335342110469683726187137)
      ·
        refine ⟨2501506582852262794640353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3335342110469683726187137 2501506582852262794640353)
        ·
          refine ⟨1876129937139197095980265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2501506582852262794640353 1876129937139197095980265)
          ·
            refine ⟨1407097452854397821985199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1876129937139197095980265 1407097452854397821985199)
            ·
              refine ⟨2110646179281596732977799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1407097452854397821985199 2110646179281596732977799)
              ·
                refine ⟨3165969268922395099466699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2110646179281596732977799 3165969268922395099466699)
                ·
                  refine ⟨4748953903383592649200049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3165969268922395099466699 4748953903383592649200049)
                  ·
                    refine ⟨3561715427537694486900037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4748953903383592649200049 3561715427537694486900037)
                    ·
                      refine ⟨667821642663317716293757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3561715427537694486900037 667821642663317716293757)
                      ·
                        rfl

theorem cell23_1300578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_1300578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300578 prefixEnd_1300578 := by exact prefixLift 1300578
  have htrace : WordTrace (prefixWord ++ tailWord_1300578) baseStart_1300578 baseEnd_1300578 := by
    simpa [prefixWord, tailWord_1300578, baseEnd_1300578] using wordTrace_append hprefix tailTrace_1300578
  have hstable : (prefixWord ++ tailWord_1300578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300578).length < 2 ^ (prefixWord ++ tailWord_1300578).sum := by decide
  have hdescent : baseEnd_1300578 < baseStart_1300578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300581 : List Nat := [1, 3, 1, 3, 2, 4, 1, 1, 1, 3, 3]
def baseStart_1300581 : Nat := 118140960795 + 1300581 * 2 ^ 59
def prefixEnd_1300581 : Nat := 4983230072969 + 3 ^ 40 * 1300581 * 2
def baseEnd_1300581 : Nat := 667823183105281204556243

theorem tailTrace_1300581 : CollatzResearch.WordTrace tailWord_1300581 prefixEnd_1300581 667823183105281204556243 := by
  unfold tailWord_1300581
  simp only [CollatzResearch.WordTrace]
  refine ⟨47436086101224633395909597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31624057400816422263939731 47436086101224633395909597)
  ·
    refine ⟨17788532287959237523466099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47436086101224633395909597 17788532287959237523466099)
    ·
      refine ⟨26682798431938856285199149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17788532287959237523466099 26682798431938856285199149)
      ·
        refine ⟨10006049411977071106949681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26682798431938856285199149 10006049411977071106949681)
        ·
          refine ⟨7504537058982803330212261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10006049411977071106949681 7504537058982803330212261)
          ·
            refine ⟨1407100698559275624414799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7504537058982803330212261 1407100698559275624414799)
            ·
              refine ⟨2110651047838913436622199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1407100698559275624414799 2110651047838913436622199)
              ·
                refine ⟨3165976571758370154933299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2110651047838913436622199 3165976571758370154933299)
                ·
                  refine ⟨4748964857637555232399949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3165976571758370154933299 4748964857637555232399949)
                  ·
                    refine ⟨1780861821614083212149981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4748964857637555232399949 1780861821614083212149981)
                    ·
                      refine ⟨667823183105281204556243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1780861821614083212149981 667823183105281204556243)
                      ·
                        rfl

theorem cell23_1300581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_1300581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300581 prefixEnd_1300581 := by exact prefixLift 1300581
  have htrace : WordTrace (prefixWord ++ tailWord_1300581) baseStart_1300581 baseEnd_1300581 := by
    simpa [prefixWord, tailWord_1300581, baseEnd_1300581] using wordTrace_append hprefix tailTrace_1300581
  have hstable : (prefixWord ++ tailWord_1300581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300581).length < 2 ^ (prefixWord ++ tailWord_1300581).sum := by decide
  have hdescent : baseEnd_1300581 < baseStart_1300581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300591 : List Nat := [1, 1, 2, 1, 3, 4, 1, 4, 1, 3, 2]
def baseStart_1300591 : Nat := 118140960795 + 1300591 * 2 ^ 59
def prefixEnd_1300591 : Nat := 4983230072969 + 3 ^ 40 * 1300591 * 2
def baseEnd_1300591 : Nat := 667828317911826165431197

theorem tailTrace_1300591 : CollatzResearch.WordTrace tailWord_1300591 prefixEnd_1300591 667828317911826165431197 := by
  unfold tailWord_1300591
  simp only [CollatzResearch.WordTrace]
  refine ⟨47436450831188405103773627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31624300554125603402515751 47436450831188405103773627)
  ·
    refine ⟨71154676246782607655660441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47436450831188405103773627 71154676246782607655660441)
    ·
      refine ⟨53366007185086955741745331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71154676246782607655660441 53366007185086955741745331)
      ·
        refine ⟨80049010777630433612617997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53366007185086955741745331 80049010777630433612617997)
        ·
          refine ⟨30018379041611412604731749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80049010777630433612617997 30018379041611412604731749)
          ·
            refine ⟨5628446070302139863387203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30018379041611412604731749 5628446070302139863387203)
            ·
              refine ⟨8442669105453209795080805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5628446070302139863387203 8442669105453209795080805)
              ·
                refine ⟨1583000457272476836577651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8442669105453209795080805 1583000457272476836577651)
                ·
                  refine ⟨2374500685908715254866477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1583000457272476836577651 2374500685908715254866477)
                  ·
                    refine ⟨890437757215768220574929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2374500685908715254866477 890437757215768220574929)
                    ·
                      refine ⟨667828317911826165431197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 890437757215768220574929 667828317911826165431197)
                      ·
                        rfl

theorem cell23_1300591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 3, 2].length) (baseStart_1300591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300591 prefixEnd_1300591 := by exact prefixLift 1300591
  have htrace : WordTrace (prefixWord ++ tailWord_1300591) baseStart_1300591 baseEnd_1300591 := by
    simpa [prefixWord, tailWord_1300591, baseEnd_1300591] using wordTrace_append hprefix tailTrace_1300591
  have hstable : (prefixWord ++ tailWord_1300591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300591).length < 2 ^ (prefixWord ++ tailWord_1300591).sum := by decide
  have hdescent : baseEnd_1300591 < baseStart_1300591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300632 : List Nat := [2, 1, 2, 4, 4, 1, 2, 1, 2, 1, 3]
def baseStart_1300632 : Nat := 118140960795 + 1300632 * 2 ^ 59
def prefixEnd_1300632 : Nat := 4983230072969 + 3 ^ 40 * 1300632 * 2
def baseEnd_1300632 : Nat := 667849370618660505018509

theorem tailTrace_1300632 : CollatzResearch.WordTrace tailWord_1300632 prefixEnd_1300632 667849370618660505018509 := by
  unfold tailWord_1300632
  simp only [CollatzResearch.WordTrace]
  refine ⟨23718973112019934553008075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31625297482693246070677433 23718973112019934553008075)
  ·
    refine ⟨35578459668029901829512113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23718973112019934553008075 35578459668029901829512113)
    ·
      refine ⟨26683844751022426372134085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35578459668029901829512113 26683844751022426372134085)
      ·
        refine ⟨5003220890816704944775141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26683844751022426372134085 5003220890816704944775141)
        ·
          refine ⟨938103917028132177145339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5003220890816704944775141 938103917028132177145339)
          ·
            refine ⟨1407155875542198265718009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938103917028132177145339 1407155875542198265718009)
            ·
              refine ⟨1055366906656648699288507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1407155875542198265718009 1055366906656648699288507)
              ·
                refine ⟨1583050359984973048932761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1055366906656648699288507 1583050359984973048932761)
                ·
                  refine ⟨1187287769988729786699571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1583050359984973048932761 1187287769988729786699571)
                  ·
                    refine ⟨1780931654983094680049357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1187287769988729786699571 1780931654983094680049357)
                    ·
                      refine ⟨667849370618660505018509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1780931654983094680049357 667849370618660505018509)
                      ·
                        rfl

theorem cell23_1300632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_1300632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300632 prefixEnd_1300632 := by exact prefixLift 1300632
  have htrace : WordTrace (prefixWord ++ tailWord_1300632) baseStart_1300632 baseEnd_1300632 := by
    simpa [prefixWord, tailWord_1300632, baseEnd_1300632] using wordTrace_append hprefix tailTrace_1300632
  have hstable : (prefixWord ++ tailWord_1300632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300632).length < 2 ^ (prefixWord ++ tailWord_1300632).sum := by decide
  have hdescent : baseEnd_1300632 < baseStart_1300632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300667 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 5]
def baseStart_1300667 : Nat := 118140960795 + 1300667 * 2 ^ 59
def prefixEnd_1300667 : Nat := 4983230072969 + 3 ^ 40 * 1300667 * 2
def baseEnd_1300667 : Nat := 667867342441567868080847

theorem tailTrace_1300667 : CollatzResearch.WordTrace tailWord_1300667 prefixEnd_1300667 667867342441567868080847 := by
  unfold tailWord_1300667
  simp only [CollatzResearch.WordTrace]
  refine ⟨47439222778913070083540255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31626148519275380055693503 47439222778913070083540255)
  ·
    refine ⟨71158834168369605125310383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47439222778913070083540255 71158834168369605125310383)
    ·
      refine ⟨106738251252554407687965575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71158834168369605125310383 106738251252554407687965575)
      ·
        refine ⟨160107376878831611531948363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106738251252554407687965575 160107376878831611531948363)
        ·
          refine ⟨240161065318247417297922545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160107376878831611531948363 240161065318247417297922545)
          ·
            refine ⟨180120798988685562973441909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240161065318247417297922545 180120798988685562973441909)
            ·
              refine ⟨16886324905189271528760179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 180120798988685562973441909 16886324905189271528760179)
              ·
                refine ⟨25329487357783907293140269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16886324905189271528760179 25329487357783907293140269)
                ·
                  refine ⟨9498557759168965234927601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25329487357783907293140269 9498557759168965234927601)
                  ·
                    refine ⟨7123918319376723926195701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9498557759168965234927601 7123918319376723926195701)
                    ·
                      refine ⟨667867342441567868080847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7123918319376723926195701 667867342441567868080847)
                      ·
                        rfl

theorem cell23_1300667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 5].length) (baseStart_1300667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300667 prefixEnd_1300667 := by exact prefixLift 1300667
  have htrace : WordTrace (prefixWord ++ tailWord_1300667) baseStart_1300667 baseEnd_1300667 := by
    simpa [prefixWord, tailWord_1300667, baseEnd_1300667] using wordTrace_append hprefix tailTrace_1300667
  have hstable : (prefixWord ++ tailWord_1300667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300667).length < 2 ^ (prefixWord ++ tailWord_1300667).sum := by decide
  have hdescent : baseEnd_1300667 < baseStart_1300667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300711 : List Nat := [1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_1300711 : Nat := 118140960795 + 1300711 * 2 ^ 59
def prefixEnd_1300711 : Nat := 4983230072969 + 3 ^ 40 * 1300711 * 2
def baseEnd_1300711 : Nat := 667889935590365695930645

theorem tailTrace_1300711 : CollatzResearch.WordTrace tailWord_1300711 prefixEnd_1300711 667889935590365695930645 := by
  unfold tailWord_1300711
  simp only [CollatzResearch.WordTrace]
  refine ⟨47440827590753665598141987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31627218393835777065427991 47440827590753665598141987)
  ·
    refine ⟨71161241386130498397212981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47440827590753665598141987 71161241386130498397212981)
    ·
      refine ⟨6671366379949734224738717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71161241386130498397212981 6671366379949734224738717)
      ·
        refine ⟨2501762392481150334277019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6671366379949734224738717 2501762392481150334277019)
        ·
          refine ⟨3752643588721725501415529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2501762392481150334277019 3752643588721725501415529)
          ·
            refine ⟨2814482691541294126061647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3752643588721725501415529 2814482691541294126061647)
            ·
              refine ⟨4221724037311941189092471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2814482691541294126061647 4221724037311941189092471)
              ·
                refine ⟨6332586055967911783638707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4221724037311941189092471 6332586055967911783638707)
                ·
                  refine ⟨9498879083951867675458061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6332586055967911783638707 9498879083951867675458061)
                  ·
                    refine ⟨3562079656481950378296773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9498879083951867675458061 3562079656481950378296773)
                    ·
                      refine ⟨667889935590365695930645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3562079656481950378296773 667889935590365695930645)
                      ·
                        rfl

theorem cell23_1300711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_1300711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300711 prefixEnd_1300711 := by exact prefixLift 1300711
  have htrace : WordTrace (prefixWord ++ tailWord_1300711) baseStart_1300711 baseEnd_1300711 := by
    simpa [prefixWord, tailWord_1300711, baseEnd_1300711] using wordTrace_append hprefix tailTrace_1300711
  have hstable : (prefixWord ++ tailWord_1300711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300711).length < 2 ^ (prefixWord ++ tailWord_1300711).sum := by decide
  have hdescent : baseEnd_1300711 < baseStart_1300711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300738 : List Nat := [3, 4, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_1300738 : Nat := 118140960795 + 1300738 * 2 ^ 59
def prefixEnd_1300738 : Nat := 4983230072969 + 3 ^ 40 * 1300738 * 2
def baseEnd_1300738 : Nat := 222634599856012363431007

theorem tailTrace_1300738 : CollatzResearch.WordTrace tailWord_1300738 prefixEnd_1300738 222634599856012363431007 := by
  unfold tailWord_1300738
  simp only [CollatzResearch.WordTrace]
  refine ⟨11860453090413962302343717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31627874907770566139583245 11860453090413962302343717)
  ·
    refine ⟨2223834954452617931689447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11860453090413962302343717 2223834954452617931689447)
    ·
      refine ⟨3335752431678926897534171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2223834954452617931689447 3335752431678926897534171)
      ·
        refine ⟨5003628647518390346301257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3335752431678926897534171 5003628647518390346301257)
        ·
          refine ⟨3752721485638792759725943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5003628647518390346301257 3752721485638792759725943)
          ·
            refine ⟨5629082228458189139588915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3752721485638792759725943 5629082228458189139588915)
            ·
              refine ⟨8443623342687283709383373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5629082228458189139588915 8443623342687283709383373)
              ·
                refine ⟨3166358753507731391018765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8443623342687283709383373 3166358753507731391018765)
                ·
                  refine ⟨1187384532565399271632037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3166358753507731391018765 1187384532565399271632037)
                  ·
                    refine ⟨222634599856012363431007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1187384532565399271632037 222634599856012363431007)
                    ·
                      rfl

theorem cell23_1300738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_1300738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300738 prefixEnd_1300738 := by exact prefixLift 1300738
  have htrace : WordTrace (prefixWord ++ tailWord_1300738) baseStart_1300738 baseEnd_1300738 := by
    simpa [prefixWord, tailWord_1300738, baseEnd_1300738] using wordTrace_append hprefix tailTrace_1300738
  have hstable : (prefixWord ++ tailWord_1300738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300738).length < 2 ^ (prefixWord ++ tailWord_1300738).sum := by decide
  have hdescent : baseEnd_1300738 < baseStart_1300738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300771 : List Nat := [1, 1, 1, 4, 2, 2, 1, 3, 1, 5, 2]
def baseStart_1300771 : Nat := 118140960795 + 1300771 * 2 ^ 59
def prefixEnd_1300771 : Nat := 4983230072969 + 3 ^ 40 * 1300771 * 2
def baseEnd_1300771 : Nat := 667920744429635461180369

theorem tailTrace_1300771 : CollatzResearch.WordTrace tailWord_1300771 prefixEnd_1300771 667920744429635461180369 := by
  unfold tailWord_1300771
  simp only [CollatzResearch.WordTrace]
  refine ⟨47443015970536295845326167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31628677313690863896884111 47443015970536295845326167)
  ·
    refine ⟨71164523955804443767989251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47443015970536295845326167 71164523955804443767989251)
    ·
      refine ⟨106746785933706665651983877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71164523955804443767989251 106746785933706665651983877)
      ·
        refine ⟨20015022362569999809746977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106746785933706665651983877 20015022362569999809746977)
        ·
          refine ⟨15011266771927499857310233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20015022362569999809746977 15011266771927499857310233)
          ·
            refine ⟨11258450078945624892982675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15011266771927499857310233 11258450078945624892982675)
            ·
              refine ⟨16887675118418437339474013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11258450078945624892982675 16887675118418437339474013)
              ·
                refine ⟨6332878169406914002302755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16887675118418437339474013 6332878169406914002302755)
                ·
                  refine ⟨9499317254110371003454133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6332878169406914002302755 9499317254110371003454133)
                  ·
                    refine ⟨890560992572847281573825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9499317254110371003454133 890560992572847281573825)
                    ·
                      refine ⟨667920744429635461180369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 890560992572847281573825 667920744429635461180369)
                      ·
                        rfl

theorem cell23_1300771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 5, 2].length) (baseStart_1300771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300771 prefixEnd_1300771 := by exact prefixLift 1300771
  have htrace : WordTrace (prefixWord ++ tailWord_1300771) baseStart_1300771 baseEnd_1300771 := by
    simpa [prefixWord, tailWord_1300771, baseEnd_1300771] using wordTrace_append hprefix tailTrace_1300771
  have hstable : (prefixWord ++ tailWord_1300771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300771).length < 2 ^ (prefixWord ++ tailWord_1300771).sum := by decide
  have hdescent : baseEnd_1300771 < baseStart_1300771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300818 : List Nat := [3, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4]
def baseStart_1300818 : Nat := 118140960795 + 1300818 * 2 ^ 59
def prefixEnd_1300818 : Nat := 4983230072969 + 3 ^ 40 * 1300818 * 2
def baseEnd_1300818 : Nat := 667944878020396777292653

theorem tailTrace_1300818 : CollatzResearch.WordTrace tailWord_1300818 prefixEnd_1300818 667944878020396777292653 := by
  unfold tailWord_1300818
  simp only [CollatzResearch.WordTrace]
  refine ⟨11861182550341505718071777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31629820134244015248191405 11861182550341505718071777)
  ·
    refine ⟨8895886912756129288553833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11861182550341505718071777 8895886912756129288553833)
    ·
      refine ⟨6671915184567096966415375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8895886912756129288553833 6671915184567096966415375)
      ·
        refine ⟨10007872776850645449623063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6671915184567096966415375 10007872776850645449623063)
        ·
          refine ⟨15011809165275968174434595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10007872776850645449623063 15011809165275968174434595)
          ·
            refine ⟨22517713747913952261651893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15011809165275968174434595 22517713747913952261651893)
            ·
              refine ⟨2111035663866933024529865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22517713747913952261651893 2111035663866933024529865)
              ·
                refine ⟨1583276747900199768397399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2111035663866933024529865 1583276747900199768397399)
                ·
                  refine ⟨2374915121850299652596099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1583276747900199768397399 2374915121850299652596099)
                  ·
                    refine ⟨3562372682775449478894149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2374915121850299652596099 3562372682775449478894149)
                    ·
                      refine ⟨667944878020396777292653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3562372682775449478894149 667944878020396777292653)
                      ·
                        rfl

theorem cell23_1300818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_1300818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300818 prefixEnd_1300818 := by exact prefixLift 1300818
  have htrace : WordTrace (prefixWord ++ tailWord_1300818) baseStart_1300818 baseEnd_1300818 := by
    simpa [prefixWord, tailWord_1300818, baseEnd_1300818] using wordTrace_append hprefix tailTrace_1300818
  have hstable : (prefixWord ++ tailWord_1300818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300818).length < 2 ^ (prefixWord ++ tailWord_1300818).sum := by decide
  have hdescent : baseEnd_1300818 < baseStart_1300818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300864 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 5]
def baseStart_1300864 : Nat := 118140960795 + 1300864 * 2 ^ 59
def prefixEnd_1300864 : Nat := 4983230072969 + 3 ^ 40 * 1300864 * 2
def baseEnd_1300864 : Nat := 667968498130503597317441

theorem tailTrace_1300864 : CollatzResearch.WordTrace tailWord_1300864 prefixEnd_1300864 667968498130503597317441 := by
  unfold tailWord_1300864
  simp only [CollatzResearch.WordTrace]
  refine ⟨23723203979599686364230823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31630938639466248485641097 23723203979599686364230823)
  ·
    refine ⟨35584805969399529546346235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23723203979599686364230823 35584805969399529546346235)
    ·
      refine ⟨53377208954099294319519353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35584805969399529546346235 53377208954099294319519353)
      ·
        refine ⟨40032906715574470739639515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53377208954099294319519353 40032906715574470739639515)
        ·
          refine ⟨60049360073361706109459273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40032906715574470739639515 60049360073361706109459273)
          ·
            refine ⟨45037020055021279582094455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60049360073361706109459273 45037020055021279582094455)
            ·
              refine ⟨67555530082531919373141683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45037020055021279582094455 67555530082531919373141683)
              ·
                refine ⟨101333295123797879059712525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67555530082531919373141683 101333295123797879059712525)
                ·
                  refine ⟨37999985671424204647392197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101333295123797879059712525 37999985671424204647392197)
                  ·
                    refine ⟨7124997313392038371386037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37999985671424204647392197 7124997313392038371386037)
                    ·
                      refine ⟨667968498130503597317441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7124997313392038371386037 667968498130503597317441)
                      ·
                        rfl

theorem cell23_1300864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_1300864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300864 prefixEnd_1300864 := by exact prefixLift 1300864
  have htrace : WordTrace (prefixWord ++ tailWord_1300864) baseStart_1300864 baseEnd_1300864 := by
    simpa [prefixWord, tailWord_1300864, baseEnd_1300864] using wordTrace_append hprefix tailTrace_1300864
  have hstable : (prefixWord ++ tailWord_1300864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300864).length < 2 ^ (prefixWord ++ tailWord_1300864).sum := by decide
  have hdescent : baseEnd_1300864 < baseStart_1300864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300868 : List Nat := [2, 3, 2, 1, 1, 2, 4, 1, 1, 3, 3]
def baseStart_1300868 : Nat := 118140960795 + 1300868 * 2 ^ 59
def prefixEnd_1300868 : Nat := 4983230072969 + 3 ^ 40 * 1300868 * 2
def baseEnd_1300868 : Nat := 667970552053121581667423

theorem tailTrace_1300868 : CollatzResearch.WordTrace tailWord_1300868 prefixEnd_1300868 667970552053121581667423 := by
  unfold tailWord_1300868
  simp only [CollatzResearch.WordTrace]
  refine ⟨23723276925592440705803629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31631035900789920941071505 23723276925592440705803629)
  ·
    refine ⟨8896228847097165264676361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23723276925592440705803629 8896228847097165264676361)
    ·
      refine ⟨6672171635322873948507271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8896228847097165264676361 6672171635322873948507271)
      ·
        refine ⟨10008257452984310922760907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6672171635322873948507271 10008257452984310922760907)
        ·
          refine ⟨15012386179476466384141361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10008257452984310922760907 15012386179476466384141361)
          ·
            refine ⟨11259289634607349788106021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15012386179476466384141361 11259289634607349788106021)
            ·
              refine ⟨2111116806488878085269879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11259289634607349788106021 2111116806488878085269879)
              ·
                refine ⟨3166675209733317127904819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2111116806488878085269879 3166675209733317127904819)
                ·
                  refine ⟨4750012814599975691857229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3166675209733317127904819 4750012814599975691857229)
                  ·
                    refine ⟨1781254805474990884446461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4750012814599975691857229 1781254805474990884446461)
                    ·
                      refine ⟨667970552053121581667423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1781254805474990884446461 667970552053121581667423)
                      ·
                        rfl

theorem cell23_1300868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_1300868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300868 prefixEnd_1300868 := by exact prefixLift 1300868
  have htrace : WordTrace (prefixWord ++ tailWord_1300868) baseStart_1300868 baseEnd_1300868 := by
    simpa [prefixWord, tailWord_1300868, baseEnd_1300868] using wordTrace_append hprefix tailTrace_1300868
  have hstable : (prefixWord ++ tailWord_1300868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300868).length < 2 ^ (prefixWord ++ tailWord_1300868).sum := by decide
  have hdescent : baseEnd_1300868 < baseStart_1300868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300895 : List Nat := [1, 1, 2, 5, 1, 1, 3, 3, 1, 3, 2]
def baseStart_1300895 : Nat := 118140960795 + 1300895 * 2 ^ 59
def prefixEnd_1300895 : Nat := 4983230072969 + 3 ^ 40 * 1300895 * 2
def baseEnd_1300895 : Nat := 667984416030792976029799

theorem tailTrace_1300895 : CollatzResearch.WordTrace tailWord_1300895 prefixEnd_1300895 667984416030792976029799 := by
  unfold tailWord_1300895
  simp only [CollatzResearch.WordTrace]
  refine ⟨47447538622087065022840139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31631692414724710015226759 47447538622087065022840139)
  ·
    refine ⟨71171307933130597534260209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47447538622087065022840139 71171307933130597534260209)
    ·
      refine ⟨53378480949847948150695157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71171307933130597534260209 53378480949847948150695157)
      ·
        refine ⟨5004232589048245139127671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53378480949847948150695157 5004232589048245139127671)
        ·
          refine ⟨7506348883572367708691507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5004232589048245139127671 7506348883572367708691507)
          ·
            refine ⟨11259523325358551563037261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7506348883572367708691507 11259523325358551563037261)
            ·
              refine ⟨4222321247009456836138973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11259523325358551563037261 4222321247009456836138973)
              ·
                refine ⟨1583370467628546313552115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4222321247009456836138973 1583370467628546313552115)
                ·
                  refine ⟨2375055701442819470328173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1583370467628546313552115 2375055701442819470328173)
                  ·
                    refine ⟨890645888041057301373065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2375055701442819470328173 890645888041057301373065)
                    ·
                      refine ⟨667984416030792976029799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 890645888041057301373065 667984416030792976029799)
                      ·
                        rfl

theorem cell23_1300895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_1300895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300895 prefixEnd_1300895 := by exact prefixLift 1300895
  have htrace : WordTrace (prefixWord ++ tailWord_1300895) baseStart_1300895 baseEnd_1300895 := by
    simpa [prefixWord, tailWord_1300895, baseEnd_1300895] using wordTrace_append hprefix tailTrace_1300895
  have hstable : (prefixWord ++ tailWord_1300895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300895).length < 2 ^ (prefixWord ++ tailWord_1300895).sum := by decide
  have hdescent : baseEnd_1300895 < baseStart_1300895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300925 : List Nat := [1, 4, 1, 2, 2, 2, 3, 1, 1, 4, 2]
def baseStart_1300925 : Nat := 118140960795 + 1300925 * 2 ^ 59
def prefixEnd_1300925 : Nat := 4983230072969 + 3 ^ 40 * 1300925 * 2
def baseEnd_1300925 : Nat := 667999820450427858654661

theorem tailTrace_1300925 : CollatzResearch.WordTrace tailWord_1300925 prefixEnd_1300925 667999820450427858654661 := by
  unfold tailWord_1300925
  simp only [CollatzResearch.WordTrace]
  refine ⟨47448632811978380146432229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31632421874652253430954819 47448632811978380146432229)
  ·
    refine ⟨8896618652245946277456043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47448632811978380146432229 8896618652245946277456043)
    ·
      refine ⟨13344927978368919416184065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8896618652245946277456043 13344927978368919416184065)
      ·
        refine ⟨10008695983776689562138049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13344927978368919416184065 10008695983776689562138049)
        ·
          refine ⟨7506521987832517171603537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10008695983776689562138049 7506521987832517171603537)
          ·
            refine ⟨5629891490874387878702653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7506521987832517171603537 5629891490874387878702653)
            ·
              refine ⟨2111209309077895454513495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5629891490874387878702653 2111209309077895454513495)
              ·
                refine ⟨3166813963616843181770243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2111209309077895454513495 3166813963616843181770243)
                ·
                  refine ⟨4750220945425264772655365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3166813963616843181770243 4750220945425264772655365)
                  ·
                    refine ⟨890666427267237144872881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4750220945425264772655365 890666427267237144872881)
                    ·
                      refine ⟨667999820450427858654661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 890666427267237144872881 667999820450427858654661)
                      ·
                        rfl

theorem cell23_1300925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_1300925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300925 prefixEnd_1300925 := by exact prefixLift 1300925
  have htrace : WordTrace (prefixWord ++ tailWord_1300925) baseStart_1300925 baseEnd_1300925 := by
    simpa [prefixWord, tailWord_1300925, baseEnd_1300925] using wordTrace_append hprefix tailTrace_1300925
  have hstable : (prefixWord ++ tailWord_1300925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300925).length < 2 ^ (prefixWord ++ tailWord_1300925).sum := by decide
  have hdescent : baseEnd_1300925 < baseStart_1300925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300965 : List Nat := [1, 3, 1, 5, 2, 2, 1, 1, 7]
def baseStart_1300965 : Nat := 118140960795 + 1300965 * 2 ^ 59
def prefixEnd_1300965 : Nat := 4983230072969 + 3 ^ 40 * 1300965 * 2
def baseEnd_1300965 : Nat := 74224484408511966906053

theorem tailTrace_1300965 : CollatzResearch.WordTrace tailWord_1300965 prefixEnd_1300965 74224484408511966906053 := by
  unfold tailWord_1300965
  simp only [CollatzResearch.WordTrace]
  refine ⟨47450091731833466977888349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31633394487888977985258899 47450091731833466977888349)
  ·
    refine ⟨17793784399437550116708131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47450091731833466977888349 17793784399437550116708131)
    ·
      refine ⟨26690676599156325175062197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17793784399437550116708131 26690676599156325175062197)
      ·
        refine ⟨2502250931170905485162081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26690676599156325175062197 2502250931170905485162081)
        ·
          refine ⟨1876688198378179113871561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2502250931170905485162081 1876688198378179113871561)
          ·
            refine ⟨1407516148783634335403671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1876688198378179113871561 1407516148783634335403671)
            ·
              refine ⟨2111274223175451503105507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1407516148783634335403671 2111274223175451503105507)
              ·
                refine ⟨3166911334763177254658261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2111274223175451503105507 3166911334763177254658261)
                ·
                  refine ⟨74224484408511966906053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3166911334763177254658261 74224484408511966906053)
                  ·
                    rfl

theorem cell23_1300965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 7].length) (baseStart_1300965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300965 prefixEnd_1300965 := by exact prefixLift 1300965
  have htrace : WordTrace (prefixWord ++ tailWord_1300965) baseStart_1300965 baseEnd_1300965 := by
    simpa [prefixWord, tailWord_1300965, baseEnd_1300965] using wordTrace_append hprefix tailTrace_1300965
  have hstable : (prefixWord ++ tailWord_1300965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300965).length < 2 ^ (prefixWord ++ tailWord_1300965).sum := by decide
  have hdescent : baseEnd_1300965 < baseStart_1300965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300971 : List Nat := [1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 5]
def baseStart_1300971 : Nat := 118140960795 + 1300971 * 2 ^ 59
def prefixEnd_1300971 : Nat := 4983230072969 + 3 ^ 40 * 1300971 * 2
def baseEnd_1300971 : Nat := 668023440560534678679449

theorem tailTrace_1300971 : CollatzResearch.WordTrace tailWord_1300971 prefixEnd_1300971 668023440560534678679449 := by
  unfold tailWord_1300971
  simp only [CollatzResearch.WordTrace]
  refine ⟨47450310569811730002606767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31633540379874486668404511 47450310569811730002606767)
  ·
    refine ⟨71175465854717595003910151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47450310569811730002606767 71175465854717595003910151)
    ·
      refine ⟨106763198782076392505865227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71175465854717595003910151 106763198782076392505865227)
      ·
        refine ⟨160144798173114588758797841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106763198782076392505865227 160144798173114588758797841)
        ·
          refine ⟨120108598629835941569098381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160144798173114588758797841 120108598629835941569098381)
          ·
            refine ⟨45040724486188478088411893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120108598629835941569098381 45040724486188478088411893)
            ·
              refine ⟨4222567920580169820788615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45040724486188478088411893 4222567920580169820788615)
              ·
                refine ⟨6333851880870254731182923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4222567920580169820788615 6333851880870254731182923)
                ·
                  refine ⟨9500777821305382096774385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6333851880870254731182923 9500777821305382096774385)
                  ·
                    refine ⟨7125583365979036572580789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9500777821305382096774385 7125583365979036572580789)
                    ·
                      refine ⟨668023440560534678679449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7125583365979036572580789 668023440560534678679449)
                      ·
                        rfl

theorem cell23_1300971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 5].length) (baseStart_1300971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1300971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1300971 prefixEnd_1300971 := by exact prefixLift 1300971
  have htrace : WordTrace (prefixWord ++ tailWord_1300971) baseStart_1300971 baseEnd_1300971 := by
    simpa [prefixWord, tailWord_1300971, baseEnd_1300971] using wordTrace_append hprefix tailTrace_1300971
  have hstable : (prefixWord ++ tailWord_1300971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300971).length < 2 ^ (prefixWord ++ tailWord_1300971).sum := by decide
  have hdescent : baseEnd_1300971 < baseStart_1300971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301011 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 6]
def baseStart_1301011 : Nat := 118140960795 + 1301011 * 2 ^ 59
def prefixEnd_1301011 : Nat := 4983230072969 + 3 ^ 40 * 1301011 * 2
def baseEnd_1301011 : Nat := 668043979786714522179265

theorem tailTrace_1301011 : CollatzResearch.WordTrace tailWord_1301011 prefixEnd_1301011 668043979786714522179265 := by
  unfold tailWord_1301011
  simp only [CollatzResearch.WordTrace]
  refine ⟨47451769489666816834062887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31634512993111211222708591 47451769489666816834062887)
  ·
    refine ⟨71177654234500225251094331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47451769489666816834062887 71177654234500225251094331)
    ·
      refine ⟨106766481351750337876641497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71177654234500225251094331 106766481351750337876641497)
      ·
        refine ⟨80074861013812753407481123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106766481351750337876641497 80074861013812753407481123)
        ·
          refine ⟨120112291520719130111221685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80074861013812753407481123 120112291520719130111221685)
          ·
            refine ⟨11260527330067418447927033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120112291520719130111221685 11260527330067418447927033)
            ·
              refine ⟨8445395497550563835945275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11260527330067418447927033 8445395497550563835945275)
              ·
                refine ⟨12668093246325845753917913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8445395497550563835945275 12668093246325845753917913)
                ·
                  refine ⟨9501069934744384315438435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12668093246325845753917913 9501069934744384315438435)
                  ·
                    refine ⟨14251604902116576473157653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9501069934744384315438435 14251604902116576473157653)
                    ·
                      refine ⟨668043979786714522179265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14251604902116576473157653 668043979786714522179265)
                      ·
                        rfl

theorem cell23_1301011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 6].length) (baseStart_1301011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301011 prefixEnd_1301011 := by exact prefixLift 1301011
  have htrace : WordTrace (prefixWord ++ tailWord_1301011) baseStart_1301011 baseEnd_1301011 := by
    simpa [prefixWord, tailWord_1301011, baseEnd_1301011] using wordTrace_append hprefix tailTrace_1301011
  have hstable : (prefixWord ++ tailWord_1301011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301011).length < 2 ^ (prefixWord ++ tailWord_1301011).sum := by decide
  have hdescent : baseEnd_1301011 < baseStart_1301011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301032 : List Nat := [2, 1, 5, 2, 1, 2, 1, 1, 2, 4, 2]
def baseStart_1301032 : Nat := 118140960795 + 1301032 * 2 ^ 59
def prefixEnd_1301032 : Nat := 4983230072969 + 3 ^ 40 * 1301032 * 2
def baseEnd_1301032 : Nat := 668054762880458940016669

theorem tailTrace_1301032 : CollatzResearch.WordTrace tailWord_1301032 prefixEnd_1301032 668054762880458940016669 := by
  unfold tailWord_1301032
  simp only [CollatzResearch.WordTrace]
  refine ⟨23726267711295368710288675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31635023615060491613718233 23726267711295368710288675)
  ·
    refine ⟨35589401566943053065433013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23726267711295368710288675 35589401566943053065433013)
    ·
      refine ⟨3336506396900911224884345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35589401566943053065433013 3336506396900911224884345)
      ·
        refine ⟨2502379797675683418663259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3336506396900911224884345 2502379797675683418663259)
        ·
          refine ⟨3753569696513525127994889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2502379797675683418663259 3753569696513525127994889)
          ·
            refine ⟨2815177272385143845996167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3753569696513525127994889 2815177272385143845996167)
            ·
              refine ⟨4222765908577715768994251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2815177272385143845996167 4222765908577715768994251)
              ·
                refine ⟨6334148862866573653491377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4222765908577715768994251 6334148862866573653491377)
                ·
                  refine ⟨4750611647149930240118533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6334148862866573653491377 4750611647149930240118533)
                  ·
                    refine ⟨890739683840611920022225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4750611647149930240118533 890739683840611920022225)
                    ·
                      refine ⟨668054762880458940016669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 890739683840611920022225 668054762880458940016669)
                      ·
                        rfl

theorem cell23_1301032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_1301032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301032 prefixEnd_1301032 := by exact prefixLift 1301032
  have htrace : WordTrace (prefixWord ++ tailWord_1301032) baseStart_1301032 baseEnd_1301032 := by
    simpa [prefixWord, tailWord_1301032, baseEnd_1301032] using wordTrace_append hprefix tailTrace_1301032
  have hstable : (prefixWord ++ tailWord_1301032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301032).length < 2 ^ (prefixWord ++ tailWord_1301032).sum := by decide
  have hdescent : baseEnd_1301032 < baseStart_1301032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301052 : List Nat := [2, 2, 2, 2, 3, 3, 1, 1, 2, 2, 3]
def baseStart_1301052 : Nat := 118140960795 + 1301052 * 2 ^ 59
def prefixEnd_1301052 : Nat := 4983230072969 + 3 ^ 40 * 1301052 * 2
def baseEnd_1301052 : Nat := 668065032493548861766577

theorem tailTrace_1301052 : CollatzResearch.WordTrace tailWord_1301052 prefixEnd_1301052 668065032493548861766577 := by
  unfold tailWord_1301052
  simp only [CollatzResearch.WordTrace]
  refine ⟨23726632441259140418152705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31635509921678853890870273 23726632441259140418152705)
  ·
    refine ⟨17794974330944355313614529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23726632441259140418152705 17794974330944355313614529)
    ·
      refine ⟨13346230748208266485210897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17794974330944355313614529 13346230748208266485210897)
      ·
        refine ⟨10009673061156199863908173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13346230748208266485210897 10009673061156199863908173)
        ·
          refine ⟨3753627397933574948965565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10009673061156199863908173 3753627397933574948965565)
          ·
            refine ⟨1407610274225090605862087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3753627397933574948965565 1407610274225090605862087)
            ·
              refine ⟨2111415411337635908793131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1407610274225090605862087 2111415411337635908793131)
              ·
                refine ⟨3167123117006453863189697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2111415411337635908793131 3167123117006453863189697)
                ·
                  refine ⟨2375342337754840397392273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3167123117006453863189697 2375342337754840397392273)
                  ·
                    refine ⟨1781506753316130298044205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2375342337754840397392273 1781506753316130298044205)
                    ·
                      refine ⟨668065032493548861766577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1781506753316130298044205 668065032493548861766577)
                      ·
                        rfl

theorem cell23_1301052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_1301052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301052 prefixEnd_1301052 := by exact prefixLift 1301052
  have htrace : WordTrace (prefixWord ++ tailWord_1301052) baseStart_1301052 baseEnd_1301052 := by
    simpa [prefixWord, tailWord_1301052, baseEnd_1301052] using wordTrace_append hprefix tailTrace_1301052
  have hstable : (prefixWord ++ tailWord_1301052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301052).length < 2 ^ (prefixWord ++ tailWord_1301052).sum := by decide
  have hdescent : baseEnd_1301052 < baseStart_1301052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301081 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 2, 10]
def baseStart_1301081 : Nat := 118140960795 + 1301081 * 2 ^ 59
def prefixEnd_1301081 : Nat := 4983230072969 + 3 ^ 40 * 1301081 * 2
def baseEnd_1301081 : Nat := 222693307810843082767981

theorem tailTrace_1301081 : CollatzResearch.WordTrace tailWord_1301081 prefixEnd_1301081 222693307810843082767981 := by
  unfold tailWord_1301081
  simp only [CollatzResearch.WordTrace]
  refine ⟨47454322599413218789111097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31636215066275479192740731 47454322599413218789111097)
  ·
    refine ⟨35590741949559914091833323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47454322599413218789111097 35590741949559914091833323)
    ·
      refine ⟨53386112924339871137749985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35590741949559914091833323 53386112924339871137749985)
      ·
        refine ⟨40039584693254903353312489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53386112924339871137749985 40039584693254903353312489)
        ·
          refine ⟨30029688519941177514984367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40039584693254903353312489 30029688519941177514984367)
          ·
            refine ⟨45044532779911766272476551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30029688519941177514984367 45044532779911766272476551)
            ·
              refine ⟨67566799169867649408714827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45044532779911766272476551 67566799169867649408714827)
              ·
                refine ⟨101350198754801474113072241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67566799169867649408714827 101350198754801474113072241)
                ·
                  refine ⟨76012649066101105584804181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101350198754801474113072241 76012649066101105584804181)
                  ·
                    refine ⟨222693307810843082767981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 76012649066101105584804181 222693307810843082767981)
                    ·
                      rfl

theorem cell23_1301081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 10].length) (baseStart_1301081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301081 prefixEnd_1301081 := by exact prefixLift 1301081
  have htrace : WordTrace (prefixWord ++ tailWord_1301081) baseStart_1301081 baseEnd_1301081 := by
    simpa [prefixWord, tailWord_1301081, baseEnd_1301081] using wordTrace_append hprefix tailTrace_1301081
  have hstable : (prefixWord ++ tailWord_1301081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301081).length < 2 ^ (prefixWord ++ tailWord_1301081).sum := by decide
  have hdescent : baseEnd_1301081 < baseStart_1301081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301088 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 4]
def baseStart_1301088 : Nat := 118140960795 + 1301088 * 2 ^ 59
def prefixEnd_1301088 : Nat := 4983230072969 + 3 ^ 40 * 1301088 * 2
def baseEnd_1301088 : Nat := 668083517797110720916411

theorem tailTrace_1301088 : CollatzResearch.WordTrace tailWord_1301088 prefixEnd_1301088 668083517797110720916411 := by
  unfold tailWord_1301088
  simp only [CollatzResearch.WordTrace]
  refine ⟨23727288955193929492307959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31636385273591905989743945 23727288955193929492307959)
  ·
    refine ⟨35590933432790894238461939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23727288955193929492307959 35590933432790894238461939)
    ·
      refine ⟨53386400149186341357692909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35590933432790894238461939 53386400149186341357692909)
      ·
        refine ⟨20019900055944878009134841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53386400149186341357692909 20019900055944878009134841)
        ·
          refine ⟨15014925041958658506851131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20019900055944878009134841 15014925041958658506851131)
          ·
            refine ⟨22522387562937987760276697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15014925041958658506851131 22522387562937987760276697)
            ·
              refine ⟨16891790672203490820207523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22522387562937987760276697 16891790672203490820207523)
              ·
                refine ⟨25337686008305236230311285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16891790672203490820207523 25337686008305236230311285)
                ·
                  refine ⟨2375408063278615896591683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25337686008305236230311285 2375408063278615896591683)
                  ·
                    refine ⟨3563112094917923844887525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2375408063278615896591683 3563112094917923844887525)
                    ·
                      refine ⟨668083517797110720916411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3563112094917923844887525 668083517797110720916411)
                      ·
                        rfl

theorem cell23_1301088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_1301088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301088 prefixEnd_1301088 := by exact prefixLift 1301088
  have htrace : WordTrace (prefixWord ++ tailWord_1301088) baseStart_1301088 baseEnd_1301088 := by
    simpa [prefixWord, tailWord_1301088, baseEnd_1301088] using wordTrace_append hprefix tailTrace_1301088
  have hstable : (prefixWord ++ tailWord_1301088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301088).length < 2 ^ (prefixWord ++ tailWord_1301088).sum := by decide
  have hdescent : baseEnd_1301088 < baseStart_1301088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301102 : List Nat := [4, 1, 2, 2, 2, 2, 2, 2, 1, 5]
def baseStart_1301102 : Nat := 118140960795 + 1301102 * 2 ^ 59
def prefixEnd_1301102 : Nat := 4983230072969 + 3 ^ 40 * 1301102 * 2
def baseEnd_1301102 : Nat := 222696902175424555380449

theorem tailTrace_1301102 : CollatzResearch.WordTrace tailWord_1301102 prefixEnd_1301102 222696902175424555380449 := by
  unfold tailWord_1301102
  simp only [CollatzResearch.WordTrace]
  refine ⟨5931886066542142421953195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31636725688224759583750373 5931886066542142421953195)
  ·
    refine ⟨8897829099813213632929793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5931886066542142421953195 8897829099813213632929793)
    ·
      refine ⟨6673371824859910224697345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8897829099813213632929793 6673371824859910224697345)
      ·
        refine ⟨5005028868644932668523009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6673371824859910224697345 5005028868644932668523009)
        ·
          refine ⟨3753771651483699501392257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5005028868644932668523009 3753771651483699501392257)
          ·
            refine ⟨2815328738612774626044193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3753771651483699501392257 2815328738612774626044193)
            ·
              refine ⟨2111496553959580969533145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2815328738612774626044193 2111496553959580969533145)
              ·
                refine ⟨1583622415469685727149859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2111496553959580969533145 1583622415469685727149859)
                ·
                  refine ⟨2375433623204528590724789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1583622415469685727149859 2375433623204528590724789)
                  ·
                    refine ⟨222696902175424555380449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2375433623204528590724789 222696902175424555380449)
                    ·
                      rfl

theorem cell23_1301102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_1301102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301102 prefixEnd_1301102 := by exact prefixLift 1301102
  have htrace : WordTrace (prefixWord ++ tailWord_1301102) baseStart_1301102 baseEnd_1301102 := by
    simpa [prefixWord, tailWord_1301102, baseEnd_1301102] using wordTrace_append hprefix tailTrace_1301102
  have hstable : (prefixWord ++ tailWord_1301102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301102).length < 2 ^ (prefixWord ++ tailWord_1301102).sum := by decide
  have hdescent : baseEnd_1301102 < baseStart_1301102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301125 : List Nat := [1, 3, 1, 1, 4, 3, 2, 1, 1, 1, 5]
def baseStart_1301125 : Nat := 118140960795 + 1301125 * 2 ^ 59
def prefixEnd_1301125 : Nat := 4983230072969 + 3 ^ 40 * 1301125 * 2
def baseEnd_1301125 : Nat := 668102516581327076153741

theorem tailTrace_1301125 : CollatzResearch.WordTrace tailWord_1301125 prefixEnd_1301125 668102516581327076153741 := by
  unfold tailWord_1301125
  simp only [CollatzResearch.WordTrace]
  refine ⟨47455927411253814303712829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31637284940835876202475219 47455927411253814303712829)
  ·
    refine ⟨17795972779220180363892311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47455927411253814303712829 17795972779220180363892311)
    ·
      refine ⟨26693959168830270545838467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17795972779220180363892311 26693959168830270545838467)
      ·
        refine ⟨40040938753245405818757701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26693959168830270545838467 40040938753245405818757701)
        ·
          refine ⟨7507676016233513591017069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40040938753245405818757701 7507676016233513591017069)
          ·
            refine ⟨2815378506087567596631401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7507676016233513591017069 2815378506087567596631401)
            ·
              refine ⟨2111533879565675697473551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2815378506087567596631401 2111533879565675697473551)
              ·
                refine ⟨3167300819348513546210327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2111533879565675697473551 3167300819348513546210327)
                ·
                  refine ⟨4750951229022770319315491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3167300819348513546210327 4750951229022770319315491)
                  ·
                    refine ⟨7126426843534155478973237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4750951229022770319315491 7126426843534155478973237)
                    ·
                      refine ⟨668102516581327076153741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7126426843534155478973237 668102516581327076153741)
                      ·
                        rfl

theorem cell23_1301125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 1, 5].length) (baseStart_1301125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301125 prefixEnd_1301125 := by exact prefixLift 1301125
  have htrace : WordTrace (prefixWord ++ tailWord_1301125) baseStart_1301125 baseEnd_1301125 := by
    simpa [prefixWord, tailWord_1301125, baseEnd_1301125] using wordTrace_append hprefix tailTrace_1301125
  have hstable : (prefixWord ++ tailWord_1301125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301125).length < 2 ^ (prefixWord ++ tailWord_1301125).sum := by decide
  have hdescent : baseEnd_1301125 < baseStart_1301125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301155 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 6, 1, 3]
def baseStart_1301155 : Nat := 118140960795 + 1301155 * 2 ^ 59
def prefixEnd_1301155 : Nat := 4983230072969 + 3 ^ 40 * 1301155 * 2
def baseEnd_1301155 : Nat := 668117921000961958778603

theorem tailTrace_1301155 : CollatzResearch.WordTrace tailWord_1301155 prefixEnd_1301155 668117921000961958778603 := by
  unfold tailWord_1301155
  simp only [CollatzResearch.WordTrace]
  refine ⟨47457021601145129427304919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31638014400763419618203279 47457021601145129427304919)
  ·
    refine ⟨71185532401717694140957379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47457021601145129427304919 71185532401717694140957379)
    ·
      refine ⟨106778298602576541211436069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71185532401717694140957379 106778298602576541211436069)
      ·
        refine ⟨20020930987983101477144263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106778298602576541211436069 20020930987983101477144263)
        ·
          refine ⟨30031396481974652215716395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20020930987983101477144263 30031396481974652215716395)
          ·
            refine ⟨45047094722961978323574593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30031396481974652215716395 45047094722961978323574593)
            ·
              refine ⟨33785321042221483742680945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45047094722961978323574593 33785321042221483742680945)
              ·
                refine ⟨25338990781666112807010709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33785321042221483742680945 25338990781666112807010709)
                ·
                  refine ⟨1187765192890599037828627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25338990781666112807010709 1187765192890599037828627)
                  ·
                    refine ⟨1781647789335898556742941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1187765192890599037828627 1781647789335898556742941)
                    ·
                      refine ⟨668117921000961958778603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1781647789335898556742941 668117921000961958778603)
                      ·
                        rfl

theorem cell23_1301155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_1301155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301155 prefixEnd_1301155 := by exact prefixLift 1301155
  have htrace : WordTrace (prefixWord ++ tailWord_1301155) baseStart_1301155 baseEnd_1301155 := by
    simpa [prefixWord, tailWord_1301155, baseEnd_1301155] using wordTrace_append hprefix tailTrace_1301155
  have hstable : (prefixWord ++ tailWord_1301155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301155).length < 2 ^ (prefixWord ++ tailWord_1301155).sum := by decide
  have hdescent : baseEnd_1301155 < baseStart_1301155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301159 : List Nat := [1, 1, 6, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_1301159 : Nat := 118140960795 + 1301159 * 2 ^ 59
def prefixEnd_1301159 : Nat := 4983230072969 + 3 ^ 40 * 1301159 * 2
def baseEnd_1301159 : Nat := 668119974923579943128585

theorem tailTrace_1301159 : CollatzResearch.WordTrace tailWord_1301159 prefixEnd_1301159 668119974923579943128585 := by
  unfold tailWord_1301159
  simp only [CollatzResearch.WordTrace]
  refine ⟨47457167493130638110450531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31638111662087092073633687 47457167493130638110450531)
  ·
    refine ⟨71185751239695957165675797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47457167493130638110450531 71185751239695957165675797)
    ·
      refine ⟨3336832089360747992141053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 71185751239695957165675797 3336832089360747992141053)
      ·
        refine ⟨1251312033510280497052895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3336832089360747992141053 1251312033510280497052895)
        ·
          refine ⟨1876968050265420745579343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1251312033510280497052895 1876968050265420745579343)
          ·
            refine ⟨2815452075398131118369015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1876968050265420745579343 2815452075398131118369015)
            ·
              refine ⟨4223178113097196677553523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2815452075398131118369015 4223178113097196677553523)
              ·
                refine ⟨6334767169645795016330285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4223178113097196677553523 6334767169645795016330285)
                ·
                  refine ⟨2375537688617173131123857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6334767169645795016330285 2375537688617173131123857)
                  ·
                    refine ⟨1781653266462879848342893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2375537688617173131123857 1781653266462879848342893)
                    ·
                      refine ⟨668119974923579943128585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1781653266462879848342893 668119974923579943128585)
                      ·
                        rfl

theorem cell23_1301159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_1301159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301159 prefixEnd_1301159 := by exact prefixLift 1301159
  have htrace : WordTrace (prefixWord ++ tailWord_1301159) baseStart_1301159 baseEnd_1301159 := by
    simpa [prefixWord, tailWord_1301159, baseEnd_1301159] using wordTrace_append hprefix tailTrace_1301159
  have hstable : (prefixWord ++ tailWord_1301159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301159).length < 2 ^ (prefixWord ++ tailWord_1301159).sum := by decide
  have hdescent : baseEnd_1301159 < baseStart_1301159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301228 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 7]
def baseStart_1301228 : Nat := 118140960795 + 1301228 * 2 ^ 59
def prefixEnd_1301228 : Nat := 4983230072969 + 3 ^ 40 * 1301228 * 2
def baseEnd_1301228 : Nat := 668155405088740173165767

theorem tailTrace_1301228 : CollatzResearch.WordTrace tailWord_1301228 prefixEnd_1301228 668155405088740173165767 := by
  unfold tailWord_1301228
  simp only [CollatzResearch.WordTrace]
  refine ⟨23729842064940331447356169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31639789419920441929808225 23729842064940331447356169)
  ·
    refine ⟨17797381548705248585517127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23729842064940331447356169 17797381548705248585517127)
    ·
      refine ⟨26696072323057872878275691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17797381548705248585517127 26696072323057872878275691)
      ·
        refine ⟨40044108484586809317413537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26696072323057872878275691 40044108484586809317413537)
        ·
          refine ⟨30033081363440106988060153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40044108484586809317413537 30033081363440106988060153)
          ·
            refine ⟨22524811022580080241045115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30033081363440106988060153 22524811022580080241045115)
            ·
              refine ⟨33787216533870120361567673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22524811022580080241045115 33787216533870120361567673)
              ·
                refine ⟨25340412400402590271175755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33787216533870120361567673 25340412400402590271175755)
                ·
                  refine ⟨38010618600603885406763633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25340412400402590271175755 38010618600603885406763633)
                  ·
                    refine ⟨28507963950452914055072725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38010618600603885406763633 28507963950452914055072725)
                    ·
                      refine ⟨668155405088740173165767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28507963950452914055072725 668155405088740173165767)
                      ·
                        rfl

theorem cell23_1301228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_1301228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301228 prefixEnd_1301228 := by exact prefixLift 1301228
  have htrace : WordTrace (prefixWord ++ tailWord_1301228) baseStart_1301228 baseEnd_1301228 := by
    simpa [prefixWord, tailWord_1301228, baseEnd_1301228] using wordTrace_append hprefix tailTrace_1301228
  have hstable : (prefixWord ++ tailWord_1301228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301228).length < 2 ^ (prefixWord ++ tailWord_1301228).sum := by decide
  have hdescent : baseEnd_1301228 < baseStart_1301228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301229 : List Nat := [1, 5, 1, 2, 1, 1, 2, 2, 4, 2, 2]
def baseStart_1301229 : Nat := 118140960795 + 1301229 * 2 ^ 59
def prefixEnd_1301229 : Nat := 4983230072969 + 3 ^ 40 * 1301229 * 2
def baseEnd_1301229 : Nat := 668155918569394669253263

theorem tailTrace_1301229 : CollatzResearch.WordTrace tailWord_1301229 prefixEnd_1301229 668155918569394669253263 := by
  unfold tailWord_1301229
  simp only [CollatzResearch.WordTrace]
  refine ⟨47459720602877040065498741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31639813735251360043665827 47459720602877040065498741)
  ·
    refine ⟨4449348806519722506140507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47459720602877040065498741 4449348806519722506140507)
    ·
      refine ⟨6674023209779583759210761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4449348806519722506140507 6674023209779583759210761)
      ·
        refine ⟨5005517407334687819408071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6674023209779583759210761 5005517407334687819408071)
        ·
          refine ⟨7508276111002031729112107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5005517407334687819408071 7508276111002031729112107)
          ·
            refine ⟨11262414166503047593668161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7508276111002031729112107 11262414166503047593668161)
            ·
              refine ⟨8446810624877285695251121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11262414166503047593668161 8446810624877285695251121)
              ·
                refine ⟨6335107968657964271438341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8446810624877285695251121 6335107968657964271438341)
                ·
                  refine ⟨1187832744123368300894689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6335107968657964271438341 1187832744123368300894689)
                  ·
                    refine ⟨890874558092526225671017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1187832744123368300894689 890874558092526225671017)
                    ·
                      refine ⟨668155918569394669253263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 890874558092526225671017 668155918569394669253263)
                      ·
                        rfl

theorem cell23_1301229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_1301229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301229 prefixEnd_1301229 := by exact prefixLift 1301229
  have htrace : WordTrace (prefixWord ++ tailWord_1301229) baseStart_1301229 baseEnd_1301229 := by
    simpa [prefixWord, tailWord_1301229, baseEnd_1301229] using wordTrace_append hprefix tailTrace_1301229
  have hstable : (prefixWord ++ tailWord_1301229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301229).length < 2 ^ (prefixWord ++ tailWord_1301229).sum := by decide
  have hdescent : baseEnd_1301229 < baseStart_1301229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301245 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 4, 3, 3]
def baseStart_1301245 : Nat := 118140960795 + 1301245 * 2 ^ 59
def prefixEnd_1301245 : Nat := 4983230072969 + 3 ^ 40 * 1301245 * 2
def baseEnd_1301245 : Nat := 668164134259866606653189

theorem tailTrace_1301245 : CollatzResearch.WordTrace tailWord_1301245 prefixEnd_1301245 668164134259866606653189 := by
  unfold tailWord_1301245
  simp only [CollatzResearch.WordTrace]
  refine ⟨47460304170819074798081189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31640202780546049865387459 47460304170819074798081189)
  ·
    refine ⟨8898807032028576524640223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47460304170819074798081189 8898807032028576524640223)
    ·
      refine ⟨13348210548042864786960335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8898807032028576524640223 13348210548042864786960335)
      ·
        refine ⟨20022315822064297180440503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13348210548042864786960335 20022315822064297180440503)
        ·
          refine ⟨30033473733096445770660755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20022315822064297180440503 30033473733096445770660755)
          ·
            refine ⟨45050210599644668655991133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30033473733096445770660755 45050210599644668655991133)
            ·
              refine ⟨16893828974866750745996675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45050210599644668655991133 16893828974866750745996675)
              ·
                refine ⟨25340743462300126118995013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16893828974866750745996675 25340743462300126118995013)
                ·
                  refine ⟨4751389399181273647311565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25340743462300126118995013 4751389399181273647311565)
                  ·
                    refine ⟨1781771024692977617741837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4751389399181273647311565 1781771024692977617741837)
                    ·
                      refine ⟨668164134259866606653189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1781771024692977617741837 668164134259866606653189)
                      ·
                        rfl

theorem cell23_1301245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_1301245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301245 prefixEnd_1301245 := by exact prefixLift 1301245
  have htrace : WordTrace (prefixWord ++ tailWord_1301245) baseStart_1301245 baseEnd_1301245 := by
    simpa [prefixWord, tailWord_1301245, baseEnd_1301245] using wordTrace_append hprefix tailTrace_1301245
  have hstable : (prefixWord ++ tailWord_1301245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301245).length < 2 ^ (prefixWord ++ tailWord_1301245).sum := by decide
  have hdescent : baseEnd_1301245 < baseStart_1301245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301246 : List Nat := [4, 2, 2, 1, 2, 2, 1, 1, 4, 2, 2]
def baseStart_1301246 : Nat := 118140960795 + 1301246 * 2 ^ 59
def prefixEnd_1301246 : Nat := 4983230072969 + 3 ^ 40 * 1301246 * 2
def baseEnd_1301246 : Nat := 668164647740521102740685

theorem tailTrace_1301246 : CollatzResearch.WordTrace tailWord_1301246 prefixEnd_1301246 668164647740521102740685 := by
  unfold tailWord_1301246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5932542580476931496108449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31640227095876967979245061 5932542580476931496108449)
  ·
    refine ⟨4449406935357698622081337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5932542580476931496108449 4449406935357698622081337)
    ·
      refine ⟨3337055201518273966561003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4449406935357698622081337 3337055201518273966561003)
      ·
        refine ⟨5005582802277410949841505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3337055201518273966561003 5005582802277410949841505)
        ·
          refine ⟨3754187101708058212381129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5005582802277410949841505 3754187101708058212381129)
          ·
            refine ⟨2815640326281043659285847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3754187101708058212381129 2815640326281043659285847)
            ·
              refine ⟨4223460489421565488928771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2815640326281043659285847 4223460489421565488928771)
              ·
                refine ⟨6335190734132348233393157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4223460489421565488928771 6335190734132348233393157)
                ·
                  refine ⟨1187848262649815293761217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6335190734132348233393157 1187848262649815293761217)
                  ·
                    refine ⟨890886196987361470320913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1187848262649815293761217 890886196987361470320913)
                    ·
                      refine ⟨668164647740521102740685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 890886196987361470320913 668164647740521102740685)
                      ·
                        rfl

theorem cell23_1301246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_1301246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301246 prefixEnd_1301246 := by exact prefixLift 1301246
  have htrace : WordTrace (prefixWord ++ tailWord_1301246) baseStart_1301246 baseEnd_1301246 := by
    simpa [prefixWord, tailWord_1301246, baseEnd_1301246] using wordTrace_append hprefix tailTrace_1301246
  have hstable : (prefixWord ++ tailWord_1301246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301246).length < 2 ^ (prefixWord ++ tailWord_1301246).sum := by decide
  have hdescent : baseEnd_1301246 < baseStart_1301246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301248 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 5, 7]
def baseStart_1301248 : Nat := 118140960795 + 1301248 * 2 ^ 59
def prefixEnd_1301248 : Nat := 4983230072969 + 3 ^ 40 * 1301248 * 2
def baseEnd_1301248 : Nat := 222721891567276698305225

theorem tailTrace_1301248 : CollatzResearch.WordTrace tailWord_1301248 prefixEnd_1301248 222721891567276698305225 := by
  unfold tailWord_1301248
  simp only [CollatzResearch.WordTrace]
  refine ⟨23730206794904103155220199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31640275726538804206960265 23730206794904103155220199)
  ·
    refine ⟨35595310192356154732830299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23730206794904103155220199 35595310192356154732830299)
    ·
      refine ⟨53392965288534232099245449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35595310192356154732830299 53392965288534232099245449)
      ·
        refine ⟨40044723966400674074434087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53392965288534232099245449 40044723966400674074434087)
        ·
          refine ⟨60067085949601011111651131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40044723966400674074434087 60067085949601011111651131)
          ·
            refine ⟨90100628924401516667476697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60067085949601011111651131 90100628924401516667476697)
            ·
              refine ⟨67575471693301137500607523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90100628924401516667476697 67575471693301137500607523)
              ·
                refine ⟨101363207539951706250911285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67575471693301137500607523 101363207539951706250911285)
                ·
                  refine ⟨9502800706870472461022933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 101363207539951706250911285 9502800706870472461022933)
                  ·
                    refine ⟨222721891567276698305225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9502800706870472461022933 222721891567276698305225)
                    ·
                      rfl

theorem cell23_1301248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 5, 7].length) (baseStart_1301248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301248 prefixEnd_1301248 := by exact prefixLift 1301248
  have htrace : WordTrace (prefixWord ++ tailWord_1301248) baseStart_1301248 baseEnd_1301248 := by
    simpa [prefixWord, tailWord_1301248, baseEnd_1301248] using wordTrace_append hprefix tailTrace_1301248
  have hstable : (prefixWord ++ tailWord_1301248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301248).length < 2 ^ (prefixWord ++ tailWord_1301248).sum := by decide
  have hdescent : baseEnd_1301248 < baseStart_1301248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301252 : List Nat := [2, 3, 2, 2, 1, 1, 1, 6, 5]
def baseStart_1301252 : Nat := 118140960795 + 1301252 * 2 ^ 59
def prefixEnd_1301252 : Nat := 4983230072969 + 3 ^ 40 * 1301252 * 2
def baseEnd_1301252 : Nat := 74240858736049786585073

theorem tailTrace_1301252 : CollatzResearch.WordTrace tailWord_1301252 prefixEnd_1301252 74240858736049786585073 := by
  unfold tailWord_1301252
  simp only [CollatzResearch.WordTrace]
  refine ⟨23730279740896857496793005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31640372987862476662390673 23730279740896857496793005)
  ·
    refine ⟨8898854902836321561297377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23730279740896857496793005 8898854902836321561297377)
    ·
      refine ⟨6674141177127241170973033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8898854902836321561297377 6674141177127241170973033)
      ·
        refine ⟨5005605882845430878229775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6674141177127241170973033 5005605882845430878229775)
        ·
          refine ⟨7508408824268146317344663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5005605882845430878229775 7508408824268146317344663)
          ·
            refine ⟨11262613236402219476016995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7508408824268146317344663 11262613236402219476016995)
            ·
              refine ⟨16893919854603329214025493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11262613236402219476016995 16893919854603329214025493)
              ·
                refine ⟨791902493184531056907445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16893919854603329214025493 791902493184531056907445)
                ·
                  refine ⟨74240858736049786585073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 791902493184531056907445 74240858736049786585073)
                  ·
                    rfl

theorem cell23_1301252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_1301252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301252 prefixEnd_1301252 := by exact prefixLift 1301252
  have htrace : WordTrace (prefixWord ++ tailWord_1301252) baseStart_1301252 baseEnd_1301252 := by
    simpa [prefixWord, tailWord_1301252, baseEnd_1301252] using wordTrace_append hprefix tailTrace_1301252
  have hstable : (prefixWord ++ tailWord_1301252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301252).length < 2 ^ (prefixWord ++ tailWord_1301252).sum := by decide
  have hdescent : baseEnd_1301252 < baseStart_1301252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
